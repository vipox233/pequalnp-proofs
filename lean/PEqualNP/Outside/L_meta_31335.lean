import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31335
-- Seven-input certificate adapted from upstream L-meta-10720.
-- Free-inversion restriction lemmas adapted from upstream L-meta-30042.
-- Both sources are distributed under the project Apache-2.0 license.
namespace Seven

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
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
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
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
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
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
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
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
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
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))

abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

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
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
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

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
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
    simpa [needed,yes] using no
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

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)

def rowsMask (i : ℕ) : ℕ :=
  let block := (#[0x1ff01ff000000000000000000000000000000000000000000000175000000000000000000000000000000000000000000000000000001d300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cf0000000000000000000000000000000000000000000000000045000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x7ff07ff07ff07ff07ff00000000000000000000000000000000077507750000077500000000000000000000000000000000000007d3000007d3000007d3000000000000000000000000000000000751000000000000000000000000000000000000000000000000000006cf06cf06cf00000000000000000000000000000000000000000645000006450000000000000000000000000000000000000000000006c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000023f023f023f0000023f000000000000000000000000000000000235023500000000000000000000000000000000000000000000021300000213000002130000000000000000000000000000000002110000000000000000000000000000000000000000000000000000020f020f00000000000000000000000000000000000000000000020500000000000000000000000000000000000000000000000000000203000000000000000000000000000000000000000000000000000000000000,0x19ff19ff19ff00000000000019ff19ff00000000000000000000197519750000000000000000197500000000000000000000000019d3000019d3000000000000000019d300000000000000000000195100000000000000000000000000000000000000000000000008cf08cf08cf00000000000008cf000000000000000000000000084508450000000000000000084500000000000000000000000008c3000008c3000000000000000000000000000000000000000008410000000000000000000000000000000000000000000000000000183f183f0000000000000000183f000000000000000000000000183500000000000000000000000000000000000000000000000000001813000000000000000018130000000000000000000000000000000000000000000000000000000000000000000000000000080f080f00000000000000000000000000000000000000000000080500000000000000000000000000000000000000000000000000000803000000000000000000000000000000000000000000000000000000000000000000000000,0x3fff3fff3fff3fff3fff3fff3fff3fff000000000000000000003f753f7500003f753f7500003f750000000000000000000000003fd300003fd33fd300003fd300003fd3000000000000000000003f51000000003f510000000000000000000000000000000000002ecf2ecf2ecf00002ecf2ecf2ecf0000000000000000000000002e452e45000000002e4500002e450000000000000000000000002ec300002ec3000000002ec300000000000000000000000000002e4100000000000000000000000000000000000000000000000000003a3f3a3f3a3f3a3f3a3f00003a3f0000000000000000000000003a3500003a353a3500000000000000000000000000000000000000003a133a1300003a1300003a13000000000000000000000000000000003a1100000000000000000000000000000000000000002a0f2a0f00002a0f2a0f000000000000000000000000000000002a05000000002a0500000000000000000000000000000000000000002a03000000002a03000000000000000000000000000000000000000000000000000000000000,0xc1ffc1ffc1ff000000000000000000000000c1ffc1ff00000000c175c1750000000000000000000000000000c175000000000000c1d30000c1d30000000000000000000000000000c1d300000000c1510000000000000000000000000000000000000000000000000000c0cfc0cf000000000000000000000000c0cf0000000000000000c0450000000000000000000000000000c04500000000000000000000c0c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000403f403f403f0000000000000000000000000000403f000000004035403500000000000000000000000000000000000000000000401300004013000000000000000000000000000040130000000040110000000000000000000000000000000000000000000000000000400f400f00000000000000000000000000000000000000000000400500000000000000000000000000000000000000000000000000004003000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xc7ffc7ffc7ffc7ff000000000000c7ffc7ffc7ffc7ffc7ff0000c775c775c7750000000000000000c775c7750000c77500000000c7d3c7d30000c7d3000000000000c7d30000c7d30000c7d30000c751c75100000000000000000000c75100000000000000000000c6cf0000c6cfc6cf0000000000000000c6cfc6cfc6cf00000000c6450000c64500000000000000000000c6450000c64500000000c6c300000000c6c300000000000000000000c6c3000000000000c641000000000000000000000000000000000000000000000000423f423f423f423f000000000000423f423f423f0000423f0000423542354235000000000000000042354235000000000000000042134213000042130000000000004213000042130000421300004211421100000000000000000000421100000000000000000000420f0000420f420f0000000000000000420f420f00000000000042050000420500000000000000000000420500000000000000004203000000004203000000000000000000004203000000000000420100000000000000000000000000000000000000000000,0xd9ff0000d9ffd9ffd9ffd9ffd9ffd9ff000000000000d9ffd9ffd9750000d975d9750000d975d9750000000000000000d9750000d9d30000d9d30000d9d3d9d30000d9d30000000000000000d9d3d9510000d95100000000d9510000000000000000000000000000c8cf00000000c8cfc8cfc8cfc8cfc8cf000000000000c8cf0000c84500000000c8450000c845c8450000000000000000c8450000c8c3000000000000c8c3c8c30000c8c300000000000000000000c8410000000000000000c8410000000000000000000000000000583f0000583f583f583f0000583f583f0000000000000000583f583500005835583500000000583500000000000000000000000058130000581300005813000000005813000000000000000058135811000058110000000000000000000000000000000000000000480f00000000480f480f0000480f480f00000000000000000000480500000000480500000000480500000000000000000000000048030000000000004803000000004803000000000000000000004801000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffff75ff75ff75ff750000ff75ff750000ff75ff750000ff750000ffd3ffd3ffd30000ffd3ffd30000ffd3ffd30000ffd30000ffd3ff51ff51ff5100000000ff5100000000ff510000000000000000eecfeecf0000eecfeecfeecfeecfeecf0000eecfeecfeecf0000ee45ee450000ee450000ee45ee4500000000ee450000ee450000eec3eec300000000eec3eec30000eec300000000eec300000000ee41ee41000000000000ee4100000000000000000000000000007a3f7a3f7a3f7a3f7a3f00007a3f7a3f7a3f7a3f7a3f00007a3f7a357a357a357a35000000007a3500007a357a350000000000007a137a137a1300007a13000000007a137a1300007a1300007a137a117a117a11000000000000000000007a1100000000000000006a0f6a0f00006a0f6a0f00006a0f6a0f00006a0f6a0f000000006a056a0500006a05000000006a05000000006a050000000000006a036a03000000006a03000000006a03000000006a03000000006a016a0100000000000000000000000000000000000000000000] : Array ℕ)[i/16]?.getD 0
  (block >>> ((i%16)*208)) &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffff
def firstRow (i : ℕ) : ℕ :=
  let block := (#[0x100000101000000000000000000000,0x100040101020000030004020302000,0x100070101050700060000050605000,0x100040101020700030004020302000,0x1000a010108000009000a080908000,0x100040101020b000300040203020b0,0x10007010105070006000a0506050c0,0x1000401010207000300040203020b0] : Array ℕ)[i/16]?.getD 0
  (block >>> ((i%16)*8)) &&& 0xff
def lb (i : ℕ) : ℕ :=
  let block := (#[0x3110110010100000,0x7441421052412110,0x7441542141202110,0x9773654164513220,0x7441421052412110,0xa774754185745441,0xa774755275525441,0xaa79774a7856552] : Array ℕ)[i/16]?.getD 0
  (block >>> ((i%16)*4)) &&& 0xf
def rawBit (i : ℕ) : ℕ :=
  let block := (#[0xc000c000c000c000c000c000c000c000c000c000c000c000c000ffffffffffffffffffff000000000000000000000000000000003800380038003800380038003800380038003800380038003800ffff0000000000000000ffffffffffff0000000000000000000026002600260026002600260026002600260026002600260026000000ffff000000000000000000000000ffffffffffff0000000085c085c085c085c085c085c085c085c085c085c085c085c085c000000000000000000000ffff00000000000000000000ffff0000113011301130113011301130113011301130113011301130113000000000ffff00000000000000000000ffff000000000000ffff002c002c002c002c002c002c002c002c002c002c002c002c002c000000000000ffff00000000ffff00000000ffff0000ffff0000008a008a008a008a008a008a008a008a008a008a008a008a008a0000000000000000ffff00000000ffff00000000ffff0000ffff] : Array ℕ)[i/16]?.getD 0
  (block >>> ((i%16)*416)) &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def normaliser (s w : ℕ) : ℕ :=
  let mask := rowsMask s
  let k := firstRow s
  let absent := (2^208-1) ^^^ mask
  (w &&& (mask ||| (mask <<< 208))) ||| (if w.testBit k then absent else 0) |||
    (if w.testBit (208+k) then absent <<< 208 else 0)

def sigPool (i : ℕ) : ℕ :=
  let block := (#[0x400000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000002c002c0000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000000240000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000c0000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000040000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000082ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000030ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000002c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000affffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000002ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xc000c00000000000000000000000000000000000000000000020f000000000000000000000000000000000000000000000000000a000a00000000fffffffffffffffffffffffffffffffffffffdf0ffffffffffff0000000000000000000000000000000000000004000000040000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000004000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000060000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000004c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000008200000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000200000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000001c001c00000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000001400000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000001300130fffffffffffffffffffffffffffffffffffffffffffffe00ffff000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000008a008afffffffffffffffffffffffffffffffffffffffffffffe00ffff00000000000000000000000000000000000000000000008a00000000000000000000000000000000000000000000000000000000,0x2c002c002c002c002c00000000000000000000000000000000000007ff000007ff000000000000000000000000000000000000002c002c002c0000002c000000000000000000000000000000000000023f0000000000000000000000000000000000000000000000240024000000240000fffffffffffffffffffffffffffffffff88affffffffffffffff0000000000000000000000000000000000240024000000000000fffffffffffffffffffffffffffffffffdcaffffffffffffffff0000000000000000000000000000000000100000001000000010fffffffffffffffffffffffffffffffffffffffffdecffffffff0000000000000000000000000000000000100000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000a000a000a0000000afffffffffffffffffffffffffffffffffdc0fdc0ffffffffffff0000000000000000000000000000000000020000000200000002fffffffffffffffffffffffffffffffffdecffffffffffffffff000000000000000000000000000000000000060006000600000000000000000000000000000000000000000006cf06cf000000000000000000000000000000000000000000000600000006000000000000000000000000000000000000000000064500000000000000000000000000000000000000000000000004c004c004c00000fffffffffffffffffffffffffffffffffffff930f930ffffffff0000000000000000000000000000000000000440000004400000fffffffffffffffffffffffffffffffffffff9baffffffffffff0000000000000000000000000000000000000200020000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000200000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000008a008a008a0000000000000000000000000000000000000000000006cf00000000000000000000000000000000000000000000000c000c000c0000fffffffffffffffffffffffffffffffffffffffff930ffffffff,0x5c005c005c005c005c00000000000000000000000000000000000000000000007ff00000000000000000000000000000000000005c0000005c0000005c000000000000000000000000000000000000000000000000000000000000000000000000000000000000005400540000005400000fffffffffffffffffffffffffffffffff88af88affffffffffff00000000000000000000000000000000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200020002000000020000000000000000000000000000000000023f023f023f000000000000000000000000000000000000000002000200000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000200000002000000020000000000000000000000000000000000021300000213000000000000000000000000000000000000000002000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000001300130013001300130fffffffffffffffffffffffffffffffffffff800f800f800ffff000000000000000000000000000000000130013000000130000000000000000000000000000000000000077500000000000000000000000000000000000000000000000001100000011000000110fffffffffffffffffffffffffffffffffffffffff82cffffffff0000000000000000000000000000000001100000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000008a008a008a008a008afffffffffffffffffffffffffffffffff800f800fffff800ffff0000000000000000000000000000000000820000008200000082fffffffffffffffffffffffffffffffff82cffffffffffffffff0000000000000000000000000000000000300030003000000030fffffffffffffffffffffffffffffffffffffdc0fdc0ffffffff00000000000000000000000000000000003000300000000000000000000000000000000000000000000002350000000000000000,0x220000000000220000000000ffffffffffffffffffffffffffffd5fcffffffffffffffffffff000000000000000000000000000018000000000000000000180000000000000000000000000000001813000000000000000000000000000000000000000000000000101010100000101000001010ffffffffffffffffffffffffffffc5ecffffffffc5ecffffffff0000000000000000000000000000101000000000000000001010ffffffffffffffffffffffffffffe7ecffffffffffffffffffff0000000000000000000000000000080000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000200020000000200000002ffffffffffffffffffffffffffffffffc5ecffffffffffffffff0000000000000000000000000000000200000000000200000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000200000000000000000002ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000200000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000010100000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000060006000600060006000000000000000000000000000000000007ff07ff07ff000000000000000000000000000000000000000006000600000006000000000000000000000000000000000000000775077500000000000000000000000000000000000000000000060000000600000006000000000000000000000000000000000007d3000007d3000000000000000000000000000000000000000006000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x800000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000002c002c002c002c002c0000002c0000000000000000000000003a3f000000003a3f000000000000000000000000000000000000002c002c0000000000000000002c000000000000000000000000183f0000000000000000000000000000000000000000000000000024000000240024000000000000ffffffffffffffffffffffffffffffffc5caffffffffffffffff0000000000000000000000000024000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000c000c0000000c000c000000000000000000000000000000002a0f000000002a0f000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000080f000000000000000000000000000000000000000000000000000a000a000a000a000a0000000affffffffffffffffffffffffc5c0ffffc5c0c5c0ffffffffffff000000000000000000000000000a000a0000000a000a00000000ffffffffffffffffffffffffd5f0ffffffffd5f0ffffffffffff000000000000000000000000000a000a0000000000000000000affffffffffffffffffffffffe7c0ffffffffffffffffffffffff000000000000000000000000000a000a00000000000000000000fffffffffffffffffffffffff7f0ffffffffffffffffffffffff0000000000000000000000000004000000000004000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000004000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000038003800000038000000380000000000000000000000000000003a1300000000000000000000000000000000000000000000000028000000000028000000000000000000000000000000000000002a03000000000000000000000000000000000000000000000000220022000000220000002200000000000000000000000000000000003a1300003a1300000000,0x40004000000000000000000040000fffffffffffffffffffff7baffffffffffffffffffffffffffff00000000000000000000000038003800380038003800000038000000000000000000000000003a3f3a3f0000000000000000000000000000000000000000000038000000380038000000000000000000000000000000000000003a3500000000000000000000000000000000000000000000000028002800000028002800000000000000000000000000000000002a0f2a0f0000000000000000000000000000000000000000000028000000000028000000000000000000000000000000000000002a050000000000000000000000000000000000000000000000002200220022002200220000002200000000000000000000000000000000003a3f3a3f3a3f000000000000000000000000000000002200220000002200220000000000ffffffffffffffffffffffffd5f0d5f0ffffffffffffffffffff0000000000000000000000002200000022002200000000000000ffffffffffffffffffffffffc5caffffffffffffffffffffffff0000000000000000000000002200000000002200000000000000ffffffffffffffffffffffffd5faffffffffffffffffffffffff0000000000000000000000001800180000000000000000001800000000000000000000000000183f183f000000000000000000000000000000000000000000001800000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000001030103010301030103000001030ffffffffffffffffffffffffc5c0c5c0ffffc5c0c5c0ffffffff0000000000000000000000001030103000000000000000001030ffffffffffffffffffffffffe7c0e7c0ffffffffffffffffffff0000000000000000000000001030000010301030000000000000000000000000000000000000000000003a350000000000000000000000000000000000000000103000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800080000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x8a008a008a0000008a008a008a000000000000000000000000000000002ecf000000002ecf0000000000000000000000000000008a008a008a000000000000008a008affffffffffffffffffffe600e600ffffffffffffffffe600ffff00000000000000000000008a008a008a000000000000008a0000000000000000000000000000000008cf000000000000000000000000000000000000000000820000008200820000008200000082ffffffffffffffffffffc02cffffffffc02cffffffffffffffff0000000000000000000000820000008200000000008200000000ffffffffffffffffffffd13cffffffffffffffffffffffffffff0000000000000000000000820000008200000000000000000082ffffffffffffffffffffe62cffffffffffffffffffffffffffff0000000000000000000000820000008200000000000000000000fffffffffffffffffffff73cffffffffffffffffffffffffffff0000000000000000000000400040000000000000000000400000fffffffffffffffffffffffff7baffffffffffffffffffffffff0000000000000000000000400000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000002c002c002c002c002c002c002c002c0000000000000000000000003fff000000003fff00003fff000000000000000000000000002c002c002c000000000000002c002c00000000000000000000000019ff000000000000000019ff00000000000000000000000000240024000000240024000000240000ffffffffffffffffffffc08affffffffc08affffffffffffffff0000000000000000000000240024000000000000000000240000ffffffffffffffffffffe68affffffffffffffffffffffffffff00000000000000000000000c000c000c0000000c000c000c0000ffffffffffffffffffffd130ffffd130ffffffffd130ffffffff00000000000000000000000c000c000c000000000000000c0000fffffffffffffffffffff730fffff730ffffffffffffffffffff0000000000000000000000040004000000000004000000040000ffffffffffffffffffffd1baffffffffffffffffffffffffffff,0x8000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000005c005c005c005c005c005c005c005c0000000000000000000003fff000000000000000000003fff00000000000000000000000005c0000005c005c0000005c0000005c0000000000000000000003fd300000000000000000000000000000000000000000000000005400540000005400540000005400000ffffffffffffffffffffffffc08affffc08ac08affffffffffff0000000000000000000005400000000005400000000000000000000000000000000000003f5100000000000000000000000000000000000000000000000004c004c004c0000004c004c004c00000ffffffffffffffffffffffffd130d130ffffd130d130ffffffff0000000000000000000004c0000004c00000000004c000000000000000000000000000002ec300000000000000000000000000000000000000000000000004400440000000000440000004400000ffffffffffffffffffffffffd1baffffffffd1baffffffffffff0000000000000000000004400000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000001c001c001c000000000000001c001c00000000000000000000019ff0000000000000000000019ff00000000000000000000000001c0000001c0000000000000000001c00000000000000000000019d300000000000000000000000000000000000000000000000001400140000000000000000001400000ffffffffffffffffffffffffe68affffffffffffffffffffffff0000000000000000000001400000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000c000c000c000000000000000c00000fffffffffffffffffffffffff730f730ffffffffffffffffffff0000000000000000000000c0000000c0000000000000000000000000000000000000000008c3000000000000000000000000000000000000000000000000008a008a008a008a008a008a008a008affffffffffffffffffffc000c000ffffc000c000ffffc000ffff,0x26000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180018001800000000000000180018000000000000000000000019ff19ff19ff000000000000000000000000000000000000000018001800000000000000000018000000000000000000000000001975197500000000000000000000000000000000000000000000180000001800000000000000000018000000000000000000000019d3000019d3000000000000000000000000000000000000000018000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000011301130113011301130113011301130ffffffffffffffffffffc000c000c000ffffc000c000c000ffff0000000000000000000011301130113000000000000011301130ffffffffffffffffffffe600e600e600ffffffffffffe600ffff0000000000000000000011301130000011301130000011300000000000000000000000000000000000003f750000000000000000000000000000000000001130113000000000000000001130000000000000000000000000000000000000000000000000000000000000000000000000000011100000111011100000111000001110ffffffffffffffffffffc02cffffc02cffffffffc02cffffffff0000000000000000000011100000111000000000000000001110ffffffffffffffffffffe62cffffe62cffffffffffffffffffff0000000000000000000011100000000011100000000000000000ffffffffffffffffffffc0aeffffffffffffffffffffffffffff0000000000000000000011100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080008000800000000000000080000000000000000000000000008cf08cf08cf00000000000000000000000000000000000000000800080000000000000000000800000000000000000000000000084508450000000000000000000000000000000000000000000008000000080000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x200000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000038003800380038003800380038003800000000000000000000003fff3fff3fff000000000000000000000000000000000000000038003800000038003800000038000000000000000000000000003f753f750000000000000000000000000000000000000000000038000000380038000000380000003800000000000000000000003fd300003fd3000000000000000000000000000000000000000038000000000038000000000000000000000000000000000000003f5100000000000000000000000000000000000000000000000028002800280000002800280028000000000000000000000000002ecf2ecf2ecf000000000000000000000000000000000000000028002800000000002800000028000000000000000000000000002e452e450000000000000000000000000000000000000000000028000000280000000000280000000000000000000000000000002ec300002ec3000000000000000000000000000000000000000028000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000026002600260026002600260026002600000000000000000000000000000000003fff3fff3fff0000000000000000000000000000260026002600000026002600260000000000000000000000000000000000000000002ecf2ecf000000000000000000000000000026002600000026002600000026000000000000000000000000000000000000003f753f7500000000000000000000000000000000260026000000000026000000260000000000000000000000000000000000000000002e450000000000000000000000000000000026000000260026000000260000002600000000000000000000000000000000003fd300003fd3000000000000000000000000000026000000260000000000260000000000ffffffffffffffffffffd13cffffd13cffffffffffffffffffff0000000000000000000026000000000026000000000000000000ffffffffffffffffffffc0aeffffffffffffffffffffffffffff,0xc000c000000000000000000000000000c0000000000000000000c0cfc0cf00000000000000000000000000000000000000000000c0000000000000000000000000000000c0000000000000000000c04500000000000000000000000000000000000000000000000080c080c000000000000000000000000080c00000ffffffffffff3f303f30ffffffffffffffffffffffffffffffff0000000000008040000000000000000000000000000080400000ffffffffffff3fbaffffffffffffffffffffffffffffffffffff0000000000004000400000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000004000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000008a008a000000000000000000000000008a00000000000000000000c0cf00000000000000000000000000000000000000000000000c000c000000000000000000000000000c0000ffffffffffffffff3f30ffffffffffffffffffffffffffffffff000000000000000c000c00000000000000000000000000000000000000000000400f000000000000000000000000000000000000000000000000000a000a00000000000000000000000000000000ffffffffffffbff0ffffffffffffffffffffffffffffffffffff0000000000000004000000000000000000000000000000040000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000004000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000c00000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000080c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000008200000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1300130013000000000000000000000000001300130ffffffffffff3e003e00ffffffffffffffffffffffff3e00ffff000000000130013000000000000000000000000000000130000000000000c17500000000000000000000000000000000000000000000000001100000011000000000000000000000000000000110ffffffffffffffff3e2cffffffffffffffffffffffffffffffff0000000001100000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000008a008a008a000000000000000000000000008a008affffffff3e003e00ffffffffffffffffffffffffffff3e00ffff0000000000820000008200000000000000000000000000000082ffffffff3e2cffffffffffffffffffffffffffffffffffffffff0000000000300030003000000000000000000000000000000030ffffffffffffbfc0bfc0ffffffffffffffffffffffffffffffff0000000000300030000000000000000000000000000000000000000000004035000000000000000000000000000000000000000000000000002c002c002c000000000000000000000000002c002c000000000000c1ff0000000000000000000000000000c1ff000000000000002c002c002c0000000000000000000000000000002c000000000000403f0000000000000000000000000000000000000000000000240024000000000000000000000000000000240000ffffffff3e8affffffffffffffffffffffffffffffffffffffff0000000000240024000000000000000000000000000000000000ffffffffbfcaffffffffffffffffffffffffffffffffffffffff0000000000100000001000000000000000000000000000000010ffffffffffffffffbfecffffffffffffffffffffffffffffffff0000000000100000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000a000a000a0000000000000000000000000000000affffffffbfc0bfc0ffffffffffffffffffffffffffffffffffff0000000000020000000200000000000000000000000000000002ffffffffbfecffffffffffffffffffffffffffffffffffffffff,0x400000004000000000000000000000004000000040000ffff39baffffffffffffffffffffffffffffffffffffffffffff0000000400000004000000000000000000000004000000000000ffffbdfaffffffffffffffffffffffffffffffffffffffffffff0000000200020000000200000000000000020000000200000002ffffbdecbdecffffffffffffffffffffbdecffffffffffffffff0000000200000000000200000000000000000000000200000000ffffbdfcffffffffffffffffffffffffffffffffffffffffffff00000000c000c000c000000000000000000000000000c000c00000000000c1ffc1ffc1ff0000000000000000000000000000000000000000c000c0000000000000000000000000000000c000000000000000c175c17500000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000c00000000000c1d30000c1d30000000000000000000000000000000000000000c0000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000000081c081c081c000000000000000000000000081c081c000000000000000000000000000000000000000000000c1ff00000000000081c0000081c0000000000000000000000000000081c000000000000000000000000000000000000000000000000000000000000081408140000000000000000000000000000081400000ffffffff3e8a3e8affffffffffffffffffffffffffffffffffff00000000814000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000400040000000000000000000000000000000400000000000403f403f403f000000000000000000000000000000000000000040004000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000000004000000040000000000000000000000000000000400000000000401300004013000000000000000000000000000000000000000040000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x8a008a008a008a000000000000008a008a008a008a008affff380038003800ffffffffffffffff38003800ffff3800ffff0000008a0000008a008a0000000000000000008a008a008a00000000000000000000c6cf00000000000000000000c6cf000000000000008200820000008200000000000000820000008200000082ffff382c382cffffffffffffffffffff382cffffffffffffffff0000008200000000008200000000000000000000008200000000ffff393cffffffffffffffffffffffffffffffffffffffffffff0000003000300030003000000000000000300030003000000030ffffbdc0ffffbdc0bdc0ffffffffffffffffbdc0bdc0ffffffff000000300030003000000000000000000030003000000000000000000000423500000000000000000000423500000000000000000000002c002c002c002c000000000000002c002c002c002c002c000000000000c7ff00000000000000000000c7ff0000c7ff00000000002c002c002c002c000000000000002c002c002c0000002c000000000000423f00000000000000000000423f0000000000000000002400240024000000000000000000240024000000240000ffff388a388affffffffffffffffffff388affffffffffffffff0000002400240024000000000000000000240024000000000000ffffbdcabdcaffffffffffffffffffffbdcaffffffffffffffff0000001000100000001000000000000000100000001000000010ffffbdecffffffffbdecffffffffffffffffffffbdecffffffff0000001000100000000000000000000000100000000000000000ffffbdeeffffffffffffffffffffffffffffffffffffffffffff0000000c0000000c000c0000000000000000000c000c000c0000ffff3930ffffffff3930ffffffffffffffffffff3930ffffffff0000000c0000000c000c0000000000000000000c000c00000000000000000000420f00000000000000000000420f0000000000000000000a000a000a000a000000000000000a000a000a0000000affffbdc0bdc0bdc0ffffffffffffffffbdc0bdc0ffffffffffff0000000a0000000a000a0000000000000000000a000a00000000ffffbdf0ffffbdf0ffffffffffffffffffffbdf0ffffffffffff,0x600000006000600000000000000000006000600060000000000c6cf0000000000000000000000000000c6cfc6cf0000000000000600000006000000000000000000000006000000060000000000c6450000000000000000000000000000c6450000000000000000060000000000060000000000000000000000060000000000ffffffffffffffff393cffffffffffffffffffffffffffffffff0000060000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000200020002000200000000000000020002000200000002000000423f000000000000000000000000423f423f423f000000000000020002000200000000000000000002000200000000000000ffffffffbdcabdcaffffffffffffffffffffffffffffffffffff000002000200000002000000000000000200000002000000020000004213000000000000000000000000421300004213000000000000020002000000000000000000000002000000000000000000ffffffffbdeeffffffffffffffffffffffffffffffffffffffff0000020000000200020000000000000000000200020000000000ffffffffffffbdf0bdf0ffffffffffffffffffffffffffffffff0000020000000200000000000000000000000200000000000000ffffffffffffbdfaffffffffffffffffffffffffffffffffffff0000020000000000020000000000000000000000020000000000ffffffffffffffffbdfcffffffffffffffffffffffffffffffff0000020000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000013001300130013000000000000001300130013001300130ffff3800ffff38003800ffffffffffffffff380038003800ffff000001300130013000000000000000000130013000000130000000000000c77500000000000000000000c77500000000000000000000011001100000011000000000000001100000011000000110ffff382cffffffff382cffffffffffffffffffff382cffffffff0000011001100000000000000000000001100000000000000000ffff38aeffffffffffffffffffffffffffffffffffffffffffff,0x84c0000084c084c0000000000000000084c084c084c00000ffff3930ffff39303930ffffffffffffffff39303930ffffffff000084c00000000084c00000000000000000000084c00000000000000000000000000000000000000000000000000000000000000000844000008440000000000000000000008440000084400000ffff39baffff39baffffffffffffffffffff39baffffffffffff0000844000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000400040004000000000000000400040004000000040000000423f423f423f423f0000000000000000000000000000000000004000400040000000000000000000400040000000000000000000423542354235000000000000000000000000000000000000000040004000000040000000000000004000000040000000400000004213421300004213000000000000000000000000000000000000400040000000000000000000000040000000000000000000000042114211000000000000000000000000000000000000000000004000000040004000000000000000000040004000000000000000420f0000420f420f0000000000000000000000000000000000004000000040000000000000000000000040000000000000000000420500004205000000000000000000000000000000000000000040000000000040000000000000000000000040000000000000004203000000004203000000000000000000000000000000000000400000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff00000600060006000600000000000000060006000600060006000000c7ff000000000000000000000000c7ffc7ffc7ff0000000000000600060006000000000000000000060006000000060000000000c775000000000000000000000000c775c77500000000000000000600060000000600000000000000060000000600000006000000c7d3000000000000000000000000c7d30000c7d3000000000000060006000000000000000000000006000000000000000000ffffffff38aeffffffffffffffffffffffffffffffffffffffff,0x200020002000000020000000000020002000000020000000285ec85ec85ecffffffffffffffffffff85ecffffffffffffffff000200020000000000020000000000020000000000020000000095fc95fcffffffffffffffffffffffffffffffffffffffffffff0002000000020000000200000000000200000000000000000002a7ecffffa7ecffffffffffffffffffffffffffffffffffffffff0002000000000000000200000000000200000000000000000000b7fcffffffffffffffffffffffffffffffffffffffffffffffff0000c000c000c000c000000000000000c000c000c000c000c0000000c7ffc7ffc7ffc7ff000000000000000000000000000000000000c000c000c0000000000000000000c000c0000000c00000000000c775c775c7750000000000000000000000000000000000000000c000c0000000c000000000000000c0000000c0000000c0000000c7d3c7d30000c7d3000000000000000000000000000000000000c000c00000000000000000000000c00000000000000000000000c751c75100000000000000000000000000000000000000000000c0000000c000c0000000000000000000c000c000c00000000000c6cf0000c6cfc6cf000000000000000000000000000000000000c0000000c00000000000000000000000c0000000c00000000000c6450000c6450000000000000000000000000000000000000000c00000000000c00000000000000000000000c000000000000000c6c300000000c6c3000000000000000000000000000000000000c00000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff000085c085c085c085c000000000000085c085c085c085c085c000000000000000000000000000000000000000000000c7ff0000000085c085c0000085c000000000000085c0000085c0000085c000000000000000000000000000000000000000000000000000000000854085408540000000000000000085408540000085400000ffff388a388a388affffffffffffffff388a388affffffffffff00008540854000000000000000000000854000000000000000000000000000000000000000000000000000000000000000000000,0x24002400240024000000240024000000240024000000240000008a008a008affffffff008affffffff008affffffffffffffff002400240024002400000000002400000024002400000000000085ca85ca85caffffffffffffffffffff85caffffffffffffffff0024000000240024000000240024000000000000000000240000268affff268affffffff268affffffffffffffffffffffffffff0024000000240024000000000024000000000000000000000000a7caffffa7caffffffffffffffffffffffffffffffffffffffff000c000c0000000c000c000c000c000c0000000c000c000c000011301130ffffffff11301130ffff1130ffffffff1130ffffffff000c000c0000000c000c0000000c000c0000000c000c000000000000000000006a0f000000006a0f000000006a0f000000000000000c00000000000c000c000c000c000c000000000000000c00003730ffffffffffff37303730ffff3730ffffffffffffffffffff000c00000000000c000c0000000c000c00000000000000000000000000000000480f00000000480f000000000000000000000000000a000a000a000a000a0000000a000a000a000a000a0000000a85c085c085c085c0ffffffff85c0ffff85c085c0ffffffffffff000a000a0000000a000a0000000a000a0000000a000a0000000095f095f0ffff95f0ffffffff95f0ffffffff95f0ffffffffffff000a0000000a000a000a0000000a000a0000000000000000000aa7c0ffffa7c0a7c0ffffffffa7c0ffffffffffffffffffffffff000a00000000000a000a0000000a000a00000000000000000000b7f0ffffffffb7f0ffffffffb7f0ffffffffffffffffffffffff000400040000000400000004000400000000000400000004000011ba11baffffffffffff11baffffffffffffffffffffffffffff000400040000000400000000000400000000000400000000000095fa95faffffffffffffffffffffffffffffffffffffffffffff000400000000000400000004000400000000000000000004000037baffffffffffffffff37baffffffffffffffffffffffffffff0004000000000004000000000004000000000000000000000000b7faffffffffffffffffffffffffffffffffffffffffffffffff,0x800000000000000080008000000080000000000000000000000ffffffffffffffff373cffffffffffffffffffffffffffffffff0800000000000000080000000000080000000000000000000000ffffffffffffffffb7fcffffffffffffffffffffffffffffffff0800000000000000000008000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0800000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff008a008a008a008a008a008a008a008a008a008a008a008a008a0000000000000000ffff00000000ffff00000000ffff0000ffff008a008a0000008a008a008a008a008a0000008a008a008a00000000000000000000eecf00000000eecf00000000eecf00000000008a0000008a008a008a008a008a008a000000000000008a008a2600ffff26002600ffff26002600ffffffffffffffff2600ffff008a00000000008a008a008a008a008a000000000000008a00000000000000000000c8cf00000000c8cf000000000000000000000082008200820000008200820000008200820000008200000082002c002c002cffffffff002cffffffff002cffffffffffffffff0082008200000000008200820000008200000000008200000000113c113cffffffffffff113cffffffffffffffffffffffffffff0082000000820000008200820000008200000000000000000082262cffff262cffffffff262cffffffffffffffffffffffffffff0082000000000000008200820000008200000000000000000000373cffffffffffffffff373cffffffffffffffffffffffffffff002c002c002c002c002c002c002c002c002c002c002c002c002c000000000000ffff00000000ffff00000000ffff0000ffff0000002c002c002c002c002c0000002c002c002c002c002c0000002c0000000000007a3f000000007a3f000000007a3f000000000000002c0000002c002c002c002c002c002c000000000000002c002c000000000000d9ff00000000d9ff0000000000000000d9ff0000002c0000002c002c002c0000002c002c0000000000000000002c000000000000583f00000000583f000000000000000000000000,0x1110111011100000111011100000111011100000111000001110002c002cffffffff002c002cffff002cffffffff002cffffffff111011101110000000001110000000001110000000000000000000ae00aeffffffffffff00aeffffffffffffffffffffffffffff1110000011100000111011100000111000000000000000001110262cffffffffffff262c262cffff262cffffffffffffffffffff111000001110000000001110000000000000000000000000000000000000d9510000000000000000000000000000000000000000103010301030103010300000103010301030103010300000103085c085c0ffff85c085c0ffff85c085c0ffff85c085c0ffffffff1030103010301030000000001030000010301030000000000000000000007a35000000000000000000007a3500000000000000001030000010301030103000001030103000000000000000001030a7c0ffffffffa7c0a7c0ffffa7c0a7c0ffffffffffffffffffff10300000103010300000000010300000000000000000000000000000000058350000000000000000000000000000000000000000101010101010000010100000000010101010000010100000101085ec85ecffffffff85ecffffffff85ecffffffff85ecffffffff101010101010000000000000000000001010000000000000000085ee85eeffffffffffffffffffffffffffffffffffffffffffff1010000010100000101000000000101000000000000000001010a7ecffffffffffffa7ecffffffffa7ecffffffffffffffffffff1010000010100000000000000000000000000000000000000000a7eeffffffffffffffffffffffffffffffffffffffffffffffff0800000000000800080008000800080000000000000008000000c8cf0000000000000000c8cfc8cfc8cf000000000000000000000800000000000800080000000800080000000000000000000000ffffffffffffb7f0b7f0ffffffffffffffffffffffffffffffff0800000000000800000008000800000000000000000008000000c8450000000000000000c845c8450000000000000000000000000800000000000800000000000800000000000000000000000000ffffffffffffb7faffffffffffffffffffffffffffffffffffff,0x220022000000220022000000220022000000220022000000000095f0ffffffff95f095f0ffff95f095f0ffffffffffffffffffff220022000000220000000000220000000000220000000000000095faffffffff95faffffffff95faffffffffffffffffffffffff220022000000000022000000000022000000000022000000000095fcffffffffffff95fcffffffff95fcffffffffffffffffffff220022000000000000000000000000000000000000000000000095feffffffffffffffffffffffffffffffffffffffffffffffff1800000018001800180018001800180000000000000018001800d9ff0000000000000000d9ffd9ffd9ff000000000000000000001800000018001800180000001800180000000000000000001800583f00000000000000000000583f583f000000000000000000001800000018001800000018001800000000000000000018000000d9750000000000000000d975d9750000000000000000000000001800000018001800000000001800000000000000000000000000ffffffffa7caa7caffffffffffffffffffffffffffffffffffff1800000018000000180018000000180000000000000000001800d9d30000000000000000d9d30000d9d300000000000000000000180000001800000018000000000018000000000000000000180058130000000000000000000000005813000000000000000000001800000018000000000018000000000000000000000000000000ffffffff26aeffffffffffffffffffffffffffffffffffffffff18000000180000000000000000000000000000000000000000005811000000000000000000000000000000000000000000000000113011301130113011301130113011301130113011301130113000000000ffff00000000000000000000ffff000000000000ffff113011301130113000001130113000001130113000001130000000000000ff7500000000000000000000ff75000000000000000011300000113011301130113011301130000000000000113011302600ffffffff26002600260026002600ffffffffffff2600ffff113000001130113000001130113000000000000000001130000000000000d9750000000000000000000000000000000000000000,0x2800280000000000280028000000280000000000280000000000eec30000000000000000eec30000eec30000000000000000000028002800000000002800000000002800000000002800000000006a030000000000000000000000006a03000000000000000000002800280000000000000028000000000000000000000000000000ffff11beffffffffffffffffffffffffffffffffffffffffffff28002800000000000000000000000000000000000000000000006a0100000000000000000000000000000000000000000000000026002600260026002600260026002600260026002600260026000000ffff000000000000000000000000ffffffffffff0000000026002600260026000000260026000000260026000000260000000000ff75000000000000000000000000ff75ff7500000000000026002600260000002600260000002600260000002600000026000000ffd3000000000000000000000000ffd30000ffd300000000260026002600000000002600000000002600000000000000000000aeffff00aeffffffff00aeffffffffffffffffffffffffffff26002600000026002600260026002600000026002600260000000000eecf0000000000000000000000000000eecfeecf0000000026002600000026000000260026000000000026000000260000000000ee450000000000000000000000000000ee450000000000002600260000000000260026000000260000000000260000000000113cffffffffffff113c113cffff113cffffffffffffffffffff26002600000000000000260000000000000000000000000000000000ee4100000000000000000000000000000000000000000000220022002200220022000000220022002200220022000000220000007a3f0000000000000000000000007a3f7a3f7a3f00000000220022002200220000000000220000002200220000000000000085caffff85ca85caffffffff85caffffffffffffffffffffffff220022002200000022000000000022002200000022000000220000007a130000000000000000000000007a1300007a1300000000220022002200000000000000000000002200000000000000000085eeffff85eeffffffffffffffffffffffffffffffffffffffff,0x4000000000004000400000004000400000000000000000000000480f00000000480f480f0000000000000000000000000000000040000000000040000000000040000000000000000000000000004805000000004805000000000000000000000000000000000000400000000000000040000000000040000000000000000000000048030000000000004803000000000000000000000000000000004000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff3800380038003800380038003800380038003800380038003800ffff0000000000000000ffffffffffff0000000000000000000038003800380038003800000038003800380038003800000038007a3f000000000000000000007a3f7a3f000000000000000000003800380038003800000038003800000038003800000038000000ff750000000000000000ff75ff7500000000000000000000000038003800380038000000000038000000380038000000000000007a35000000000000000000007a350000000000000000000000003800380038000000380038000000380038000000380000003800ffd30000000000000000ffd30000ffd30000000000000000000038003800380000003800000000003800380000003800000038007a130000000000000000000000007a13000000000000000000003800380038000000000038000000000038000000000000000000ff510000000000000000ff51000000000000000000000000000038003800380000000000000000000000380000000000000000007a110000000000000000000000000000000000000000000000002800280000002800280028002800280000002800280028000000eecf0000000000000000eecfeecfeecf0000000000000000000028002800000028002800000028002800000028002800000000006a0f000000000000000000006a0f6a0f000000000000000000002800280000002800000028002800000000002800000028000000ee450000000000000000ee45ee4500000000000000000000000028002800000028000000000028000000000028000000000000006a05000000000000000000006a05000000000000000000000000,0x80c00000000080c080c080c080c080c000000000000080c000003730ffffffff37303730ffff37303730ffffffffffffffffffff80c000000000000080c080c0000080c00000000000000000000000000000000000000000c8c30000000000000000000000000000804000000000804000008040804000000000000000008040000037baffffffff37baffffffff37baffffffffffffffffffffffff804000000000000000008040000000000000000000000000000037beffffffffffffffffffffffffffffffffffffffffffffffff40004000400040004000000040004000400040004000000040007a3f7a3f7a3f7a3f7a3f0000000000000000000000000000000040004000400040000000000040000000400040000000000000007a357a357a357a3500000000000000000000000000000000000040004000400000004000000000004000400000004000000040007a137a137a1300007a130000000000000000000000000000000040004000400000000000000000000000400000000000000000007a117a117a11000000000000000000000000000000000000000040004000000040004000000040004000000040004000000000006a0f6a0f00006a0f6a0f0000000000000000000000000000000040004000000040000000000040000000000040000000000000006a056a0500006a0500000000000000000000000000000000000040004000000000004000000000004000000000004000000000006a036a03000000006a03000000000000000000000000000000004000400000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff4000000040004000400000004000400000000000000000004000583f0000583f583f583f0000000000000000000000000000000040000000400040000000000040000000000000000000000000005835000058355835000000000000000000000000000000000000400000004000000040000000000040000000000000000000400058130000581300005813000000000000000000000000000000004000000040000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff,0xc00000000000c000c000c000c000c000000000000000c0000000c8cf00000000c8cfc8cf00000000000000000000000000000000c00000000000c0000000c000c0000000000000000000c0000000c84500000000c845000000000000000000000000000000000000c000000000000000c000c0000000c00000000000000000000000c8c3000000000000c8c300000000000000000000000000000000c0000000000000000000c0000000000000000000000000000000c84100000000000000000000000000000000000000000000000085c085c085c085c085c085c085c085c085c085c085c085c085c000000000000000000000ffff00000000000000000000ffff000085c085c085c0000085c085c0000085c085c0000085c0000085c000000000000000000000ffd300000000000000000000000000008540854085408540000085408540000085408540000085400000008a008a008a008affffffff008affff008a008affffffffffff854085408540000000008540000000008540000000000000000000000000000000000000ff51000000000000000000000000000084c084c0000084c084c084c084c084c0000084c084c084c0000011301130ffff11301130ffff11301130ffff11301130ffffffff84c084c00000000084c084c0000084c00000000084c00000000000000000000000000000eec30000000000000000000000000000844084400000844000008440844000000000844000008440000011ba11baffff11baffffffff11baffffffff11baffffffffffff844084400000000000008440000000000000000000000000000011be11beffffffffffffffffffffffffffffffffffffffffffff81c0000081c081c081c081c081c081c000000000000081c081c000000000000000000000d9ff00000000000000000000d9ff000081c0000081c0000081c081c0000081c0000000000000000081c000000000000000000000d9d300000000000000000000000000008140000081408140000081408140000000000000000081400000268affff268a268affffffff268affffffffffffffffffffffff814000008140000000008140000000000000000000000000000026aeffff26aeffffffffffffffffffffffffffffffffffffffff,0xc000c000c000c000c000c000c000c000c000c000c000c000c000ffffffffffffffffffff00000000000000000000000000000000c000c000c000c0000000c000c0000000c000c0000000c0000000ff75ff75ff75ff75000000000000000000000000000000000000c000c000c0000000c000c0000000c000c0000000c0000000c000ffd3ffd3ffd30000ffd300000000000000000000000000000000c000c000c00000000000c00000000000c0000000000000000000ff51ff51ff510000000000000000000000000000000000000000c000c0000000c000c000c000c000c0000000c000c000c0000000eecfeecf0000eecfeecf00000000000000000000000000000000c000c0000000c0000000c000c00000000000c0000000c0000000ee45ee450000ee45000000000000000000000000000000000000c000c00000000000c000c0000000c00000000000c00000000000eec3eec300000000eec300000000000000000000000000000000c000c000000000000000c0000000000000000000000000000000ee41ee4100000000000000000000000000000000000000000000c0000000c000c000c000c000c000c000000000000000c000c000d9ff0000d9ffd9ffd9ff00000000000000000000000000000000c0000000c000c0000000c000c0000000000000000000c0000000d9750000d975d975000000000000000000000000000000000000c0000000c0000000c000c0000000c0000000000000000000c000d9d30000d9d30000d9d300000000000000000000000000000000c0000000c00000000000c0000000000000000000000000000000d9510000d9510000000000000000000000000000000000000000] : Array ℕ)[i/16]?.getD 0
  (block >>> ((i%16)*416)) &&& 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def sigCodes (i : ℕ) : ℕ :=
  let block := (#[0x160a03822000000000150983400000000014090400000000000002020000000000903020000000000000782c0000000000001010000000000000001000000000038180800000000000010040000000000005018000000000000002000000000000040400000000000000040000000000000010000000000000000,0x863f1b8bc660000000843d1b0b40000001047c3519000000000100783400000002712880420000000002612074000000000361a0c000000000000020100000003b188b8520000000003a180b0000000000722b14000000000000702a0000000001187c3c000000000001107000000000000190b8000000000000001,0x13c864c9d4fc00000013a844b9cc0000002710a953d00000000026d0693000000092411c4fa000000000913c1bc00000000120813c8000000000011e7700000006631974ac000000000653096c0000000009c4c24000000000000020200000000030164aa000000000002f94c000000000004b238000000000000001,0x2b94c8e4d1d90000002b5488c4c1d00000562891a963e000000055a8116940000154a5451c8fe000000152a3441c00000002a142893d80000000029d3e8700000dc6a32178b00000000da6831170000000148a04d250000000001188a4400000006c34968ae0000000006b33950000000000a24f248000000000000201,0x1b6d767b1d960000001b4d567314000000365accd65000000000361a8cc0000000bf5eae172000000000be5e2d400000000166b25800000000000002010000000d364b1982000000000d264310000000001a2c360000000000001a0c20000000005dadd6c000000000005d2d000000000000b1578000000000000001,0x46e071379ba5de000046a05117939c00008cc0624f17680000008c40220f0000022eff87b8ddc00000022cfe86b7c000000455fb0e76000000000451f90c0000216fb75ba1c2000000214fa75398000000425f2e56e800000000421f0e40000001077bb89c0000000001067b3780000000020af56e00000000000208f4,0x68eb793a8cc672000068ab391a84b40000d0d5f254d9a8000000d0557214c000033f43c7ca67000000033d41c6c840000006767f8e9a0000000006727b8c00003075aa4cc24a00000030558a44b0000000606ad458e800000000602a94400000017fa14a2480000000017ea0480000000002fb3e8e000000000002f93c,0xd5deed79ba9cce7600d55e6d599a94bc01a9bbda7354f9b80001a8bada3314e0069ee767cbcae74000069ae366cac8c0000d2dbecb969b0000000d25b6c9940062ef563a5cca4e000062af162a54b80000c4ddac3478f8000000c45d2c146000030f72afcaa4c00000030d70af488000000616dd5d8f000000000612d95c] : Array ℕ)[i/16]?.getD 0
  (block >>> ((i%16)*63)) &&& 0x7fffffffffffffff
def sigRead : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n+1, c => if c=0 then [] else sigPool (c &&& 511) :: sigRead n (c >>> 9)
def basis (s : ℕ) : List ℕ := sigRead 7 (sigCodes s)

def pinch (m mask i w : ℕ) : ℕ :=
  let absent := (2^m-1) ^^^ mask
  (w &&& (mask ||| (mask <<< m))) |||
    (if w.testBit i then absent else 0) |||
    (if w.testBit (m+i) then absent <<< m else 0)

private theorem pinchBits (m mask i w j : ℕ) (hm : mask < 2^m) :
    (pinch m mask i w).testBit j =
      if j < m then w.testBit (if mask.testBit j then j else i)
      else if j < m+m then w.testBit (if mask.testBit (j-m) then j else m+i)
      else false := by
  have off (k : ℕ) (hk : m ≤ k) : mask.testBit k = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hk))
  by_cases lo : j < m
  · have n := Nat.not_le_of_lt lo
    cases h₁ : w.testBit i <;> cases h₂ : w.testBit (m+i) <;> cases h₃ : mask.testBit j <;>
      simp [pinch, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
        Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft, lo, n, h₁, h₂, h₃]
  have mj : m ≤ j := by omega
  by_cases mid : j < m+m
  · have sub : j-m < m := by omega
    cases h₁ : w.testBit i <;> cases h₂ : w.testBit (m+i) <;> cases h₃ : mask.testBit (j-m) <;>
      simp [pinch, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
        Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft, lo, mj, off _ mj, mid, sub, h₁, h₂, h₃]
  · have sub : m ≤ j-m := by omega
    cases h₁ : w.testBit i <;> cases h₂ : w.testBit (m+i) <;>
      simp [pinch, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
        Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft, lo, mj, off _ mj, mid,
        Nat.not_lt_of_ge sub, off _ sub, h₁, h₂]

def pinchProj (m mask i : ℕ) (hm : mask < 2^m) (hi : i < m) : Projection m m := by
  refine ⟨pinch m mask i, by simp [pinch], ?_, ?_, by omega⟩
  · intro d a b hd
    apply Nat.eq_of_testBit_eq
    intro j
    interval_cases d <;>
      simp only [combine, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, pinchBits _ _ _ _ _ hm] <;>
      split <;> split <;> simp [*]
  · intro a ha j hj
    have big : ¬ m+j < m := by omega
    have small : m+j < m+m := by omega
    cases h : mask.testBit j <;>
      simp [pinchBits _ _ _ _ _ hm, hj, big, small, h, ha i hi, ha j hj]

def extraTest (av : List ℕ) : List ℕ → Bool
  | [] => true
  | z::zs =>
    (av.any (fun a => av.any (fun b => (List.range 4).any (fun d => combine d a b == z)))) &&
      extraTest (av++[z]) zs

def cutTest (f t : ℕ) (p : ℕ → ℕ) (av v extra : List ℕ) : Bool :=
  let w := v.map p
  decide (f+extra.length ≤ t+w.count 0) &&
    w.all (fun x => x == 0 || (av++extra).contains x) && extraTest av extra

private theorem extraTest_pull {m k : ℕ} (av extra : List ℕ) (ok : extraTest av extra = true)
    (run : Possible m k (av++extra)) : Possible m (k+extra.length) av := by
  induction extra generalizing av with
  | nil => simpa using run
  | cons z zs ih =>
    simp only [extraTest, Bool.and_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at ok
    obtain ⟨⟨a, ha, b, hb, d, hd, rfl⟩, tail⟩ := ok
    have prev := ih (av++[combine d a b]) tail (by simpa using run)
    obtain ⟨l, S, lim, live, sub⟩ := pullPaid hd ha hb prev
    refine ⟨l, S, ?_, live, sub⟩
    have one : (charge av (combine d a b)).toNat ≤ 1 := by cases charge av (combine d a b) <;> decide
    simp only [List.length_cons]; omega

theorem cutTest_ok {m h f t : ℕ} (p : Projection m h) {av v extra : List ℕ}
    (hw : Wide h t av) (nd : v.Nodup) (hc : cutTest f t p.toFun av v extra = true) : Ban m f v := by
  simp only [cutTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hc
  obtain ⟨⟨cost, mem⟩, cert⟩ := hc
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x; simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map]
    rw [List.countP_eq_length_filter]; congr 2
  rw [fixed] at c
  have bound : Possible h j (av++extra) := by
    refine ⟨j,T,le_rfl,ok,?_⟩
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
    have found := mem _ (List.mem_map.mpr ⟨y,List.mem_toFinset.mp hy,rfl⟩)
    exact found.resolve_left (liveNonzero ok _ hx)
  obtain ⟨l,S,le,live,sub⟩ := extraTest_pull av extra cert bound
  exact hw ⟨l,S,by omega,live,sub⟩

open PEqualNP.CircuitLowerBounds
def bouts : List ℕ := [0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6]
def graph (x : Fin 7 → Bool) := decide (∃ i < bouts.length / 2,
  (List.ofFn x).getD (bouts.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (bouts.getD (2*i+1) 0) false = true)
def temoin : List Gate := [⟨.or,[0,1]⟩,⟨.or,[7,2]⟩,⟨.or,[4,6]⟩,⟨.or,[4,5]⟩,⟨.or,[7,6]⟩,⟨.or,[1,5]⟩,⟨.and,[0,2]⟩,⟨.and,[8,9]⟩,⟨.and,[10,11]⟩,⟨.and,[3,12]⟩,⟨.or,[13,14]⟩,⟨.or,[15,16]⟩,⟨.or,[17,18]⟩]
theorem legalite : ∀ g ∈ temoin, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [temoin]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨temoin,19⟩ (List.ofFn x) = graph x := by decide +kernel
theorem remplacement (k : ℕ) (h : 13 ≤ k) : ∃ (gs : List Gate) (o : ℕ),
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length ≤ k ∧
    ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graph x :=
  ⟨temoin, 19, legalite, h, correct⟩

def repsIso : List ℕ := [5,15,19,21,23,27,31,51,55,63,83,85,87,91,95,103,111,115,119,123]
def refIso (s : ℕ) : ℕ := (#[0x0,0x0,0x0,0x0,0x0,0x5,0x0,0x5,0x0,0x0,0x5,0x5,0x0,0x5,0x5,0xf,0x0,0x5,0x5,0x13,0x5,0x15,0x13,0x17,0x0,0x5,0x13,0x1b,0x5,0x15,0x1b,0x1f,0x0,0x5,0x5,0x13,0x0,0x13,0x5,0x1b,0x5,0x13,0x15,0x17,0x5,0x1b,0x15,0x1f,0x0,0x13,0x13,0x33,0x5,0x17,0x1b,0x37,0x5,0x1b,0x17,0x37,0xf,0x1f,0x1f,0x3f,0x0,0x5,0x5,0x13,0x5,0x15,0x13,0x17,0x0,0x5,0x13,0x1b,0x5,0x15,0x1b,0x1f,0x5,0x15,0x15,0x53,0x15,0x55,0x53,0x57,0x5,0x15,0x17,0x5b,0x15,0x55,0x5b,0x5f,0x5,0x15,0x15,0x53,0x13,0x53,0x17,0x67,0x13,0x17,0x53,0x67,0x1b,0x5b,0x5b,0x6f,0x13,0x53,0x53,0x73,0x17,0x57,0x67,0x77,0x1b,0x5b,0x67,0x7b,0x1f,0x5f,0x6f] : Array ℕ)[s]?.getD 0
def posIso (s : ℕ) : ℕ := (#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x0,0x0,0x1,0x10,0x0,0x2,0x3,0x3200,0x4,0x40200,0x4300,0x43200,0x0,0x2,0x3100,0x3210,0x4,0x40200,0x3410,0x43210,0x0,0x5,0x6,0x6500,0x0,0x5000,0x6,0x5600,0x7,0x7500,0x70601,0x75601,0x7,0x5700,0x70601,0x75601,0x0,0x5200,0x6300,0x6503200,0x4,0x25004,0x3460,0x6543200,0x7,0x5720,0x63107,0x2375601,0x74,0x25074,0x63147,0x76543210,0x0,0x8,0x9,0x9800,0xa,0xa0800,0xa900,0xa9800,0x0,0x8,0x9100,0x9810,0xa,0xa0800,0x9a10,0xa9810,0xb,0xb0802,0xb0903,0xb09800003200,0xb0a04,0xba0800040200,0xb0a900004300,0xba9800043200,0xb,0xb0802,0x9130b,0xb09800003210,0xb0a04,0xba0800040200,0xb09a00003410,0xba9800043210,0xc,0xc0805,0xc0906,0xc09800006500,0xca00,0x80ca00005000,0xca906,0xc0a9806500000,0xc700,0xc7508,0x60c700009100,0xc075608900001,0xca70,0x80ca00005070,0x60c7000091a0,0xc0a9876500010,0xcb00,0x80cb00005200,0x90cb00006300,0xcb09806503200,0xbca04,0x8bca00025004,0xb0ca904300006,0xcba9806543200,0xcb70,0x80cb00005270,0x901360bc00007,0xcb09876503210,0xbca74,0x8bca00025074,0x90acb16300074] : Array ℕ)[s]?.getD 0
def negIso (s : ℕ) : ℕ := (#[0x0,0x0,0x0,0x0,0x0,0x40010,0x0,0x40010,0x0,0x0,0x60020,0x60020,0x0,0x40010,0x60020,0x876543210,0x0,0x90010,0x90020,0x9000003210,0x90040,0x9000040010,0x9000005420,0x9000543210,0x0,0x90010,0x200000a960,0xa9076003210,0x90040,0x9000040010,0xa9086005240,0xa9876543210,0x0,0xb0010,0xb0020,0xb000003210,0x0,0x100000cb40,0xb0020,0xcb054003120,0xb0060,0xb000007610,0xb000060020,0xb000763120,0xb0060,0xcb084007160,0xb000060020,0xcb854763120,0x0,0x100000db90,0x200000db90,0xd0b09000003210,0x90040,0x1000d9cb40,0xd90cb005240,0xdcb09000543210,0xb0060,0xdb0a9007160,0x2000dba960,0xda90b000763120,0xdcba98640,0x71a86d9cb40,0x52c84dba960,0xdcba9876543210,0x0,0xe0010,0xe0020,0xe000003210,0xe0040,0xe000040010,0xe000005420,0xe000543210,0x0,0xe0010,0x200000fe60,0xfe076003210,0xe0040,0xe000040010,0xfe086005240,0xfe876543210,0xe0090,0xe000090010,0xe000090020,0xe00009000003210,0xe000090040,0xe00009000040010,0xe00009000005420,0xe00009000543210,0xe0090,0xe000090010,0x2000fea690,0xfe000a9076003210,0xe000090040,0xe00009000040010,0xfe000a9086005240,0xfe000a9876543210,0xe00b0,0xe0000b0010,0xe0000b0020,0xe0000b000003210,0xe00000cb40,0xe0000100000cb40,0xe000cb5420,0xe0cb00000543210,0xb00000fe60,0xb000fe7610,0xb0000200000fe60,0xb0fe00000763120,0xfe08600cb40,0xfe0007108600cb40,0xcb0005208400fe60,0xfe0cb00876543210,0xe00000db90,0xe0000100000db90,0xe0000200000db90,0xed0b09000003210,0xe000d9cb40,0xe00001000d9cb40,0xe0d900000cb5420,0xedcb09000543210,0xfe0a600db90,0xfe000710a600db90,0x20fe00000a6d9b0,0xfed0ba9076003210,0xfea86d9cb40,0xfe00071a86d9cb40,0xfe052008a6c4db90] : Array ℕ)[s]?.getD 0
def indiceIso (s i : ℕ) : ℕ :=
  let t := refIso s
  let j := if (rowsMask t).testBit i then i else firstRow t
  16 * ((((posIso s) >>> (4*(j/16))) % 16) % 13) + (((negIso s) >>> (4*(j%16))) % 16)
def lignesIso (s : ℕ) : List ℕ := (List.range 208).map (indiceIso s)
def projIso (s : ℕ) : Projection 208 208 := pick (lignesIso s) (by simp [lignesIso]) (by
  intro i hi
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  unfold indiceIso
  dsimp only
  omega) (by decide)

theorem largeIso {m h k : ℕ} {av bv : List ℕ} (p : Projection m h)
    (mène : ∀ x∈av, p.toFun x = 0 ∨ p.toFun x ∈ bv) (but : Wide h k bv) : Wide m k av := by
  rintro ⟨n,S,lim,live,sub⟩
  obtain ⟨j,T,t,ok,incl⟩ := projectLive p live
  refine but ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mène a (sub a ha)).resolve_left (liveNonzero ok _ hx)

def testIso (s : ℕ) : Bool :=
  let t := refIso s
  lb s == 0 || (repsIso.contains t && lb t == lb s &&
    (t == s || (decide (t<s) && (basis s).all (fun a => let z := coord 208 (lignesIso s) a;
      z == 0 || (basis t).contains z))))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc0 : ∀ j : Fin 8, testIso (0+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc1 : ∀ j : Fin 8, testIso (8+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc2 : ∀ j : Fin 8, testIso (16+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc3 : ∀ j : Fin 8, testIso (24+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc4 : ∀ j : Fin 8, testIso (32+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc5 : ∀ j : Fin 8, testIso (40+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc6 : ∀ j : Fin 8, testIso (48+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc7 : ∀ j : Fin 8, testIso (56+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc8 : ∀ j : Fin 8, testIso (64+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc9 : ∀ j : Fin 8, testIso (72+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc10 : ∀ j : Fin 8, testIso (80+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc11 : ∀ j : Fin 8, testIso (88+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc12 : ∀ j : Fin 8, testIso (96+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc13 : ∀ j : Fin 8, testIso (104+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc14 : ∀ j : Fin 8, testIso (112+j.val) = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem isoBloc15 : ∀ j : Fin 8, testIso (120+j.val) = true := by decide +kernel

private theorem isoTous (s : Fin 127) : testIso s.val = true := by
  let j : Fin 8 := ⟨s.val % 8,by omega⟩
  have n : s.val/8 < 16 := by omega
  interval_cases e : s.val/8
  · have p := isoBloc0 j; rwa [show 0+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc1 j; rwa [show 8+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc2 j; rwa [show 16+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc3 j; rwa [show 24+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc4 j; rwa [show 32+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc5 j; rwa [show 40+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc6 j; rwa [show 48+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc7 j; rwa [show 56+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc8 j; rwa [show 64+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc9 j; rwa [show 72+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc10 j; rwa [show 80+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc11 j; rwa [show 88+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc12 j; rwa [show 96+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc13 j; rwa [show 104+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc14 j; rwa [show 112+j.val=s.val by dsimp [j]; omega] at p
  · have p := isoBloc15 j; rwa [show 120+j.val=s.val by dsimp [j]; omega] at p

set_option maxRecDepth 8192 in
theorem petitsParIso (H : ∀ s : Fin 127, s.val ∈ repsIso →
    (∀ t : Fin 127, t.val < s.val → 0 < lb t.val → Wide 208 (lb t.val-1) (basis t.val)) →
    Wide 208 (lb s.val-1) (basis s.val))
    (s : Fin 127) (hs : 0 < lb s.val) : Wide 208 (lb s.val-1) (basis s.val) := by
  induction s using WellFoundedLT.induction with
  | ind s ih =>
   have test := isoTous s
   simp only [testIso, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq] at test
   rcases test with zero|⟨⟨mem,cost⟩,eq|⟨lt,iter⟩⟩
   · omega
   · exact H s (eq ▸ mem) (fun t ht hp => ih t ht hp)
   · apply largeIso (projIso s.val) (bv := basis (refIso s.val))
     · intro a ha
       exact iter a ha
     · let t : Fin 127 := ⟨refIso s.val,lt_trans lt s.isLt⟩
       have hp : 0 < lb (refIso s.val) := Eq.mpr (congrArg (fun q : ℕ => 0 < q) cost) hs
       have h := ih t (show t.val<s.val from lt) hp
       change Wide 208 (lb (refIso s.val)-1) (basis (refIso s.val)) at h
       exact Eq.mp (congrArg (fun q : ℕ => Wide 208 (q-1) (basis (refIso s.val))) cost) h

def vzSecond (k : ℕ → List ℕ → ℕ → Bool) (p : List ℕ) (c : ℕ) : List ℕ → Bool
  | [] => false
  | b :: t => k b (p ++ t) (c ||| cover 208 t) ||
      vzSecond k (b :: p) (separation 208 b ||| c) t

def vzPremier (k : ℕ → ℕ → List ℕ → ℕ → Bool) (p : List ℕ) (c : ℕ) : List ℕ → Bool
  | [] => false
  | a :: t => vzSecond (k a) p c t ||
      vzPremier k (a :: p) (separation 208 a ||| c) t

def vzRecherche : ℕ → List ℕ → Bool
  | 0, v => terminal 208 v
  | f+1, v =>
    vzPremier (fun a b r c =>
      let test := fun z => enough 208 (separation 208 z ||| c) &&
        (f == 0 || (z != 0 && !(v.contains z) && vzRecherche f (z :: r)))
      let ab := a &&& b
      test ab || test (a ||| b) || test (a ^^^ ab) || test (b ^^^ ab)) [] 0 v

theorem vzCouverture (p t : List ℕ) :
    cover 208 (p ++ t) = cover 208 p ||| cover 208 t := by
  induction p with
  | nil => simp [cover]
  | cons x p ih => simp [cover, ih, Nat.or_assoc]

theorem vzSecond_ok (k) {b : ℕ} (p t : List ℕ) (h : b ∈ t)
    (ok : ∀ r, (b :: r).Perm (p ++ t) → k b r (cover 208 r) = true) :
    vzSecond k p (cover 208 p) t = true := by
  induction t generalizing p with
  | nil => simp at h
  | cons x t ih =>
    rw [vzSecond, Bool.or_eq_true]
    rcases List.mem_cons.mp h with eq | ht
    · subst x
      exact Or.inl (vzCouverture p t ▸ ok _ List.perm_middle.symm)
    · right
      apply ih _ ht
      intro r hr
      exact ok _ (hr.trans List.perm_middle.symm)

theorem vzPremier_ok (k) {a b : ℕ} (p t : List ℕ) (ha : a ∈ t) (hb : b ∈ t) (ab : a ≠ b)
    (ok : ∀ x y r, ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) →
      (x :: y :: r).Perm (p ++ t) → k x y r (cover 208 r) = true) :
    vzPremier k p (cover 208 p) t = true := by
  induction t generalizing p with
  | nil => simp at ha
  | cons x t ih =>
    rw [vzPremier, Bool.or_eq_true]
    by_cases xa : x = a
    · subst x
      left
      apply vzSecond_ok _ (b := b) _ _ (List.mem_cons.mp hb |>.resolve_left (Ne.symm ab))
      intro r hr
      exact ok _ _ _ (Or.inl ⟨rfl,rfl⟩) ((hr.cons a).trans List.perm_middle.symm)
    by_cases xb : x = b
    · subst x
      left
      apply vzSecond_ok _ (b := a) _ _ (List.mem_cons.mp ha |>.resolve_left ab)
      intro r hr
      exact ok _ _ _ (Or.inr ⟨rfl,rfl⟩) ((hr.cons b).trans List.perm_middle.symm)
    · right
      apply ih _ ((List.mem_cons.mp ha).resolve_left (Ne.symm xa))
        ((List.mem_cons.mp hb).resolve_left (Ne.symm xb))
      intro i j r h hr
      exact ok _ _ _ h (hr.trans List.perm_middle.symm)

theorem vzRecherche_ok {f n v} (h : Live 208 n (List.toFinset v)) (lim : n ≤ f)
    (nd : List.Nodup v) (len : v.length = f+1) : vzRecherche f v = true := by
  have exactN := liveSize h
  rw [List.toFinset_card_of_nodup nd] at exactN
  have eq : n = f := by omega
  subst n
  clear exactN lim
  induction f generalizing v with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rep, good, _⟩ := h
    exact ends good v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
  | succ f ih =>
    rw [Live] at h
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fresh,tail⟩ := h
    have ma : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
    have mb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    unfold vzRecherche
    apply vzPremier_ok _ [] v ma mb ab
    intro x y r side perm
    change (x :: y :: r).Perm v at perm
    have ndxy := perm.nodup_iff.mpr nd
    simp only [List.nodup_cons, List.mem_cons, not_or] at ndxy
    have lr := perm.length_eq
    simp only [List.length_cons] at lr
    have lr' : r.length = f := by omega
    let z := combine d a b
    have fr : z ∉ U := fun hz => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    have sm := liveSize tail
    rw [Finset.card_insert_of_notMem fr] at sm
    have sub : r.toFinset ⊆ U := by
      intro i hi
      have mr := List.mem_toFinset.mp hi
      have mv : i ∈ v := perm.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mr))
      have ms := rep ▸ List.mem_toFinset.mpr mv
      simp only [Finset.mem_insert] at ms
      rcases side with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> aesop
    have er : r.toFinset = U := Finset.eq_of_subset_of_card_le sub (by
      rw [List.toFinset_card_of_nodup ndxy.2.2, lr']; omega)
    have child : Live 208 f (z :: r).toFinset := by simpa [er,z] using tail
    have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
    have nv : z ∉ v := fun hz => fresh (rep ▸ List.mem_toFinset.mpr hz)
    have nr : z ∉ r := fun hz => fr (er ▸ List.mem_toFinset.mpr hz)
    have cov := enoughLive child _ rfl
    have suite := ih (List.nodup_cons.mpr ⟨nr,ndxy.2.2⟩) (by simp [lr']) child
    have nz' : z ≠ 0 := nz
    have ok : (enough 208 (separation 208 z ||| cover 208 r) &&
        (f == 0 || (z != 0 && !(v.contains z) && vzRecherche f (z :: r)))) = true := by
      change (enough 208 (cover 208 (z :: r)) && _) = true
      simp [cov, nz', nv, suite]
    obtain ⟨e,he,ze⟩ : ∃ e<4, z = combine e x y := by
      rcases side with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨d,hd,rfl⟩
      · exact swapOp d _ _ hd
    rw [ze] at ok
    interval_cases e <;> simp only [combine] at ok <;> simp only [Bool.or_eq_true]
    · exact Or.inl (Or.inl (Or.inl ok))
    · exact Or.inl (Or.inl (Or.inr ok))
    · exact Or.inl (Or.inr ok)
    · exact Or.inr ok

def vitesseZero (f : ℕ) (v : List ℕ) : Bool :=
  if v.length = f+1 then !(vzRecherche f v) else !(search 208 f v)

theorem vitesseZero_ok {f v} (h : vitesseZero f v = true) (nd : List.Nodup v) :
    PEqualNP.Outside.L_meta_31335.Seven.Ban 208 f v := by
  unfold vitesseZero at h
  split at h
  · rename_i len
    intro n lim live
    simp [vzRecherche_ok live lim nd len] at h
  · exact viaSmall (by simpa using h) nd

def l2Children (m f : ℕ) (v : List ℕ) : List (List ℕ) :=
  v.flatMap fun a => v.flatMap fun b =>
    if a < b then
    let rest := without v a b
    let n := rest.length
    let cv := cover m rest
    let both := a &&& b
    [both,a ||| b,a ^^^ both,b ^^^ both].flatMap fun z =>
      if z == 0 || v.contains z then [] else
      let base := separation m z ||| cv
      let xa := separation m a
      let xb := separation m b
      let k := fun (ka kb : Bool) =>
        if 1+n+ka.toNat+kb.toNat ≤ f+1 && enough m ((base ||| (if ka then xa else 0)) ||| (if kb then xb else 0)) then
          [z::save ka a (save kb b rest)] else []
      k false false ++ k true false ++ k false true ++ k true true
    else []

theorem l2Any (m f : ℕ) (v : List ℕ) (go : List ℕ → Bool) :
    anyGate m f go v = (l2Children m f v).any go := by
  simp only [anyGate,l2Children,List.any_flatMap]
  apply congrArg (List.any v); funext a
  apply congrArg (List.any v); funext b
  by_cases ab : a<b
  · simp only [pairStep,ab,ite_true,List.any_flatMap,
      List.any_cons,List.any_nil,Bool.or_false]
    have gate (z : ℕ) : gateStep m f go v (without v a b) (without v a b).length (cover m (without v a b)) a b z =
        ((if z == 0 || v.contains z then [] else
          let k := fun (ka kb : Bool) => if 1+(without v a b).length+ka.toNat+kb.toNat ≤ f+1 &&
              enough m (((separation m z ||| cover m (without v a b)) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0)) then
              [z::save ka a (save kb b (without v a b))] else []
          k false false ++ k true false ++ k false true ++ k true true) : List (List ℕ)).any go := by
      have sel (c : Prop) [Decidable c] (w : List ℕ) : (if c then [w] else []).any go = (decide c && go w) := by by_cases h : c <;> simp [h]
      by_cases h : z=0 <;> by_cases j : z∈v <;> simp [gateStep,h,j,optionStep,sel,bne_iff_ne,Bool.or_assoc,Bool.and_assoc]
    simp only [gate,Bool.or_assoc,ite_true]
  · simp [pairStep,ab]

theorem l2Branch {m f : ℕ} {v : List ℕ} (nd : v.Nodup) (no : terminal m v = false)
    (closed : ∀ u∈l2Children m f v, u.Nodup → Ban m f u) : Ban m (f+1) v := by
  intro n hn live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)); simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !(l2Children m f v).contains u) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      simp
      intro h
      exact closed u h nu n (by omega) (hu.symm ▸ tail))
    rw [l2Any,List.any_eq_true] at yes
    obtain ⟨x,hx,bad⟩ := yes
    simp [hx] at bad

def l2Subs (f : ℕ) (v : List ℕ) := v.sublists.filter (fun u => u.length≤f+1 && enough 208 (cover 208 u))

theorem l2Wide {f : ℕ} {v : List ℕ} (nd : v.Nodup)
    (closed : ∀ u∈l2Subs f v, u.Nodup → Ban 208 f u) : Wide 208 f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have cap : u.length ≤ f+1 := by omega
  have cov := enoughLive live u eq
  have ms : u∈v.sublists := List.mem_sublists.mpr List.filter_sublist
  exact closed u (by simp [l2Subs,ms,cap,cov]) nd' n lim (eq.symm ▸ live)

def l2IH (s : ℕ) := ∀ t : Fin 127, t.val<s → 0<lb t.val → Wide 208 (lb t.val-1) (basis t.val)

abbrev L2Cell := ℕ × ℕ × Bool × List ℕ × ℕ
def L2Cell.s (c : L2Cell) := c.1
def L2Cell.f (c : L2Cell) := c.2.1
def L2Cell.wide (c : L2Cell) := c.2.2.1
def L2Cell.av (c : L2Cell) := c.2.2.2.1
def L2Cell.tape (c : L2Cell) := c.2.2.2.2

def L2Cell.claim (c : L2Cell) := l2IH c.s → if c.wide then Wide 208 c.f c.av else Ban 208 c.f c.av

def l2Proj (s : ℕ) (h : s < 127) : Projection 208 208 := pinchProj 208 (rowsMask s) (firstRow s)
  (by have hh : ∀ t : Fin 127, rowsMask t.val < 2^208 := by decide +kernel
      exact hh ⟨s,h⟩)
  (by have hh : ∀ t : Fin 127, firstRow t.val < 208 := by decide +kernel
      exact hh ⟨s,h⟩)

def l2Extra (av : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n+1, c =>
    match av[c % 16]?, av[(c >>> 4) % 16]? with
    | some a, some b =>
      let z := combine ((c >>> 8) % 4) a b
      z :: l2Extra (av++[z]) n (c >>> 10)
    | _, _ => []

theorem l2ExtraOK (av n c) : extraTest av (l2Extra av n c)=true := by
  induction n generalizing av c with
  | zero => rfl
  | succ n ih =>
    simp only [l2Extra]; split
    · rename_i a b ha hb
      simp only [extraTest, Bool.and_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq]
      exact ⟨⟨a,List.mem_of_getElem? ha,b,List.mem_of_getElem? hb,_,Nat.mod_lt _ (by decide),rfl⟩,ih _ _⟩
    · rfl

abbrev L2Rule := ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ

def l2RT (r : L2Rule) := r.1
def l2RM (r : L2Rule) := r.2.1
def l2RB (r : L2Rule) := r.2.2.1
def l2RF (r : L2Rule) := r.2.2.2.1
def l2RG (r : L2Rule) := r.2.2.2.2.1
def l2RP (r : L2Rule) := r.2.2.2.2.2

def l2RCert (r : L2Rule) :=
  let t := l2RT r
  let ma := rowsMask t
  let ex := l2Extra (basis t) (l2RF r) (l2RG r)
  t < 127 && 0 < lb t && l2RB r == lb t-1 && l2RM r == ma ||| (ma <<< 208) &&
    (l2RM r).testBit (firstRow t) && (l2RM r).testBit (208+firstRow t) &&
    ex.length ≤ l2RF r && (l2RP r).all (fun y => (basis t ++ ex).contains (normaliser t y))

def l2RuleTest (r : L2Rule) (s f : ℕ) (v : List ℕ) :=
  let w := v.map (fun x => x &&& l2RM r)
  l2RT r < s && f + l2RF r ≤ l2RB r + w.count 0 && w.all (fun y => y == 0 || (l2RP r).contains y)

theorem l2Norm (t m : ℕ) (hm : m = rowsMask t ||| (rowsMask t <<< 208))
    (b : m.testBit (firstRow t) = true) (c : m.testBit (208+firstRow t) = true) (x : ℕ) :
    normaliser t (x &&& m) = normaliser t x := by
  simp only [normaliser,Nat.testBit_and,b,c,Bool.and_true,←hm,Nat.and_assoc,Nat.and_self]

theorem l2Zeros (t m : ℕ) (agree : ∀ x, normaliser t (x &&& m)=normaliser t x) (v : List ℕ) :
    (v.map (fun x => x &&& m)).count 0 ≤ (v.map (normaliser t)).count 0 := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    by_cases z : a &&& m = 0
    · have other : normaliser t a = 0 := by rw [←agree,z]; simp [normaliser]
      simpa [z,other] using ih
    · by_cases other : normaliser t a = 0 <;> simp [z,other] <;> omega

theorem l2RuleOK {r s f v} (cert : l2RCert r=true) (ih : l2IH s) (nd : List.Nodup v) (h : l2RuleTest r s f v=true) : Ban 208 f v := by
  simp only [l2RCert,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,List.contains_iff_mem] at cert
  obtain ⟨⟨⟨⟨⟨⟨⟨lt,pos⟩,bud⟩,mask⟩,b⟩,c⟩,len⟩,all⟩ := cert
  have agr := l2Norm _ _ mask b c
  simp only [l2RuleTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_map,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at h
  obtain ⟨⟨ls,cost⟩,ok⟩ := h
  apply cutTest_ok (l2Proj _ lt) (ih ⟨_,lt⟩ ls pos) nd (extra:=l2Extra (basis (l2RT r)) (l2RF r) (l2RG r))
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_map,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem]
  refine ⟨⟨?_,?_⟩,l2ExtraOK ..⟩
  · change f+_≤lb (l2RT r)-1+(v.map (normaliser (l2RT r))).count 0
    have := l2Zeros _ _ agr v; omega
  · rintro _ ⟨x,hx,rfl⟩
    change normaliser (l2RT r) x=0 ∨ _
    rw [←agr x]
    rcases ok _ ⟨x,hx,rfl⟩ with z|mem
    · left; rw [z]; simp [normaliser]
    · right
      change normaliser (l2RT r) x ∈ _
      rw [←agr x]; exact all _ mem

def l2M0 : ℕ := 0x130000000000000000000000000000000000000000000000000013
def l2M1 : ℕ := 0x401300004013000000000000000000000000000040130000000040130000401300000000000000000000000000004013
def l2M2 : ℕ := 0x84508450000000000000000084500000000000000000000000008450845000000000000000008450000
def l2M3 : ℕ := 0x48050000000048050000000048050000000000000000000000004805000000004805000000004805000000000000000000000000
def l2M4 : ℕ := 0x48030000000000004803000000004803000000000000000000004803000000000000480300000000480300000000000000000000
def l2M5 : ℕ := 0x583f0000583f583f583f0000583f583f0000000000000000583f583f0000583f583f583f0000583f583f0000000000000000583f
def l2M6 : ℕ := 0x4205000042050000000000000000000042050000000000000000420500004205000000000000000000004205000000000000
def l2M7 : ℕ := 0x21300000213000002130000000000000000000000000000000002130000021300000213
def l2M8 : ℕ := 0xc1ffc1ffc1ff000000000000000000000000c1ffc1ff00000000c1ffc1ffc1ff000000000000000000000000c1ffc1ff
def l2M9 : ℕ := 0xc8cf00000000c8cfc8cfc8cfc8cfc8cf000000000000c8cf0000c8cf00000000c8cfc8cfc8cfc8cfc8cf000000000000c8cf0000
def l2M10 : ℕ := 0x19ff19ff19ff00000000000019ff19ff0000000000000000000019ff19ff19ff00000000000019ff19ff
def l2M11 : ℕ := 0x4203000000004203000000000000000000004203000000000000420300000000420300000000000000000000420300000000
def l2M12 : ℕ := 0x480f00000000480f480f0000480f480f00000000000000000000480f00000000480f480f0000480f480f00000000000000000000
def l2M13 : ℕ := 0x403f403f403f0000000000000000000000000000403f00000000403f403f403f0000000000000000000000000000403f
def l2M14 : ℕ := 0x23f023f023f0000023f00000000000000000000000000000000023f023f023f0000023f
def l2M15 : ℕ := 0x420f0000420f420f0000000000000000420f420f000000000000420f0000420f420f0000000000000000420f420f00000000
def l2M16 : ℕ := 0x4211421100000000000000000000421100000000000000000000421142110000000000000000000042110000000000000000
def l2M17 : ℕ := 0x58350000583558350000000058350000000000000000000000005835000058355835000000005835000000000000000000000000
def l2M18 : ℕ := 0xd9d30000d9d30000d9d3d9d30000d9d30000000000000000d9d3d9d30000d9d30000d9d3d9d30000d9d30000000000000000d9d3
def l2M19 : ℕ := 0x58130000581300005813000000005813000000000000000058135813000058130000581300000000581300000000000000005813
def l2M20 : ℕ := 0x4213421300004213000000000000421300004213000042130000421342130000421300000000000042130000421300004213
def l2M21 : ℕ := 0xd9750000d975d9750000d975d9750000000000000000d9750000d9750000d975d9750000d975d9750000000000000000d9750000
def l2M22 : ℕ := 0xc84500000000c8450000c845c8450000000000000000c8450000c84500000000c8450000c845c8450000000000000000c8450000
def l2M23 : ℕ := 0x8cf08cf08cf00000000000008cf00000000000000000000000008cf08cf08cf00000000000008cf0000
def l2M24 : ℕ := 0xc8c3000000000000c8c3c8c30000c8c300000000000000000000c8c3000000000000c8c3c8c30000c8c300000000000000000000
def l2M25 : ℕ := 0x7ff07ff07ff07ff07ff0000000000000000000000000000000007ff07ff07ff07ff07ff
def l2M26 : ℕ := 0x6a056a0500006a05000000006a05000000006a050000000000006a056a0500006a05000000006a05000000006a05000000000000
def l2M27 : ℕ := 0x183f183f0000000000000000183f000000000000000000000000183f183f0000000000000000183f
def l2M28 : ℕ := 0x423f423f423f423f000000000000423f423f423f0000423f0000423f423f423f423f000000000000423f423f423f0000423f
def l2M29 : ℕ := 0xc0cfc0cf000000000000000000000000c0cf0000000000000000c0cfc0cf000000000000000000000000c0cf0000
def l2M30 : ℕ := 0xc6cf0000c6cfc6cf0000000000000000c6cfc6cfc6cf00000000c6cf0000c6cfc6cf0000000000000000c6cfc6cfc6cf0000
def l2M31 : ℕ := 0x6a036a03000000006a03000000006a03000000006a03000000006a036a03000000006a03000000006a03000000006a0300000000
def l2M32 : ℕ := 0xc6450000c64500000000000000000000c6450000c64500000000c6450000c64500000000000000000000c6450000c6450000
def l2M33 : ℕ := 0x3f753f7500003f753f7500003f750000000000000000000000003f753f7500003f753f7500003f750000
def l2M34 : ℕ := 0x3a3f3a3f3a3f3a3f3a3f00003a3f0000000000000000000000003a3f3a3f3a3f3a3f3a3f00003a3f
def l2M35 : ℕ := 0x6a0f6a0f00006a0f6a0f00006a0f6a0f00006a0f6a0f000000006a0f6a0f00006a0f6a0f00006a0f6a0f00006a0f6a0f00000000
def l2M36 : ℕ := 0xc7ffc7ffc7ffc7ff000000000000c7ffc7ffc7ffc7ffc7ff0000c7ffc7ffc7ffc7ff000000000000c7ffc7ffc7ffc7ffc7ff
def l2M37 : ℕ := 0x3a133a1300003a1300003a1300000000000000000000000000003a133a1300003a1300003a13
def l2M38 : ℕ := 0x7a137a137a1300007a13000000007a137a1300007a1300007a137a137a137a1300007a13000000007a137a1300007a1300007a13
def l2M39 : ℕ := 0xffd3ffd3ffd30000ffd3ffd30000ffd3ffd30000ffd30000ffd3ffd3ffd3ffd30000ffd3ffd30000ffd3ffd30000ffd30000ffd3
def l2M40 : ℕ := 0x7a357a357a357a35000000007a3500007a357a350000000000007a357a357a357a35000000007a3500007a357a35000000000000
def l2M41 : ℕ := 0x4235423542350000000000000000423542350000000000000000423542354235000000000000000042354235000000000000
def l2M42 : ℕ := 0xee45ee450000ee450000ee45ee4500000000ee450000ee450000ee45ee450000ee450000ee45ee4500000000ee450000ee450000
def l2M43 : ℕ := 0x3fff3fff3fff3fff3fff3fff3fff3fff000000000000000000003fff3fff3fff3fff3fff3fff3fff3fff
def l2M44 : ℕ := 0xff75ff75ff75ff750000ff75ff750000ff75ff750000ff750000ff75ff75ff75ff750000ff75ff750000ff75ff750000ff750000
def l2M45 : ℕ := 0xc775c775c7750000000000000000c775c7750000c77500000000c775c775c7750000000000000000c775c7750000c7750000
def l2M46 : ℕ := 0xd9ff0000d9ffd9ffd9ffd9ffd9ffd9ff000000000000d9ffd9ffd9ff0000d9ffd9ffd9ffd9ffd9ffd9ff000000000000d9ffd9ff
def l2M47 : ℕ := 0xeecfeecf0000eecfeecfeecfeecfeecf0000eecfeecfeecf0000eecfeecf0000eecfeecfeecfeecfeecf0000eecfeecfeecf0000
def l2M48 : ℕ := 0xd9510000d95100000000d9510000000000000000000000000000d9510000d95100000000d9510000000000000000000000000000
def l2M49 : ℕ := 0x7a117a117a11000000000000000000007a1100000000000000007a117a117a11000000000000000000007a110000000000000000
def l2M50 : ℕ := 0xeec3eec300000000eec3eec30000eec300000000eec300000000eec3eec300000000eec3eec30000eec300000000eec300000000
def l2M51 : ℕ := 0x7a3f7a3f7a3f7a3f7a3f00007a3f7a3f7a3f7a3f7a3f00007a3f7a3f7a3f7a3f7a3f7a3f00007a3f7a3f7a3f7a3f7a3f00007a3f
def l2M52 : ℕ := 0xc175c1750000000000000000000000000000c175000000000000c175c1750000000000000000000000000000c1750000
def l2M53 : ℕ := 0x6cf06cf06cf000000000000000000000000000000000000000006cf06cf06cf0000
def l2M54 : ℕ := 0x77507750000077500000000000000000000000000000000000007750775000007750000
def l2M55 : ℕ := 0x19d3000019d3000000000000000019d30000000000000000000019d3000019d3000000000000000019d3
def l2M56 : ℕ := 0x3fd300003fd33fd300003fd300003fd3000000000000000000003fd300003fd33fd300003fd300003fd3
def l2M57 : ℕ := 0x2e452e45000000002e4500002e450000000000000000000000002e452e45000000002e4500002e450000
def l2M58 : ℕ := 0x2ecf2ecf2ecf00002ecf2ecf2ecf0000000000000000000000002ecf2ecf2ecf00002ecf2ecf2ecf0000
def l2M59 : ℕ := 0x3a3500003a353a350000000000000000000000000000000000003a3500003a353a35000000000000
def l2M60 : ℕ := 0x1ff01ff0000000000000000000000000000000000000000000001ff01ff
def l2M61 : ℕ := 0x20f020f00000000000000000000000000000000000000000000020f020f00000000
def l2M62 : ℕ := 0x2a0f2a0f00002a0f2a0f000000000000000000000000000000002a0f2a0f00002a0f2a0f00000000
def l2M63 : ℕ := 0xc7d3c7d30000c7d3000000000000c7d30000c7d30000c7d30000c7d3c7d30000c7d3000000000000c7d30000c7d30000c7d3
def l2M64 : ℕ := 0x6450000064500000000000000000000000000000000000000000645000006450000
def l2M65 : ℕ := 0xc0450000000000000000000000000000c0450000000000000000c0450000000000000000000000000000c0450000
def l2M66 : ℕ := 0x23502350000000000000000000000000000000000000000000002350235000000000000
def l2M67 : ℕ := 0x403540350000000000000000000000000000000000000000000040354035000000000000000000000000000000000000
def l2M68 : ℕ := 0x400f400f00000000000000000000000000000000000000000000400f400f00000000000000000000000000000000
def l2M69 : ℕ := 0xc6c300000000c6c300000000000000000000c6c3000000000000c6c300000000c6c300000000000000000000c6c300000000
def l2M70 : ℕ := 0xc751c75100000000000000000000c75100000000000000000000c751c75100000000000000000000c7510000000000000000
def l2M71 : ℕ := 0x80f080f00000000000000000000000000000000000000000000080f080f00000000000000000000
def l2M72 : ℕ := 0xc1d30000c1d30000000000000000000000000000c1d300000000c1d30000c1d30000000000000000000000000000c1d3
def l2M73 : ℕ := 0x197519750000000000000000197500000000000000000000000019751975000000000000000019750000
def l2M74 : ℕ := 0x8c3000008c3000000000000000000000000000000000000000008c3000008c300000000000000000000
def l2M75 : ℕ := 0xc8410000000000000000c8410000000000000000000000000000c8410000000000000000c8410000000000000000000000000000
def l2M76 : ℕ := 0x58110000581100000000000000000000000000000000000000005811000058110000000000000000000000000000000000000000
def l2M77 : ℕ := 0x1813000000000000000018130000000000000000000000000000181300000000000000001813
def l2M78 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Sp (x : ℕ) : ℕ :=
  let x := (x ||| (x <<< 120)) &&& 0x1f000000000000000000000000000000ff
  let x := (x ||| (x <<< 60)) &&& 0x1000000000000000f000000000000000f000000000000000f
  let x := (x ||| (x <<< 30)) &&& 0x1000000030000000300000003000000030000000300000003
  let x := (x ||| (x <<< 15)) &&& 0x1000100010001000100010001000100010001000100010001
  x
def l2Flat (v : ℕ) := (l2Sp (v &&& 8191) * 65535) ||| (((v >>> 13) * 0x1000100010001000100010001000100010001000100010001) <<< 208)
def l2Key (m v : ℕ) := l2Flat v &&& m
def k0 : ℕ := l2Key l2M0 16385
def k1 : ℕ := l2Key l2M0 131073
def k2 : ℕ := l2Key l2M1 16641
def k3 : ℕ := l2Key l2M1 132097
def k4 : ℕ := l2Key l2M1 134219008
def k5 : ℕ := l2Key l2M2 32834
def k6 : ℕ := l2Key l2M2 524418
def k7 : ℕ := l2Key l2M2 16777408
def k8 : ℕ := l2Key l2M3 33344
def k9 : ℕ := l2Key l2M3 16781376
def k10 : ℕ := l2Key l2M3 134222336
def k11 : ℕ := l2Key l2M4 16672
def k12 : ℕ := l2Key l2M4 16781344
def k13 : ℕ := l2Key l2M4 134222080
def k14 : ℕ := l2Key l2M5 82209
def k15 : ℕ := l2Key l2M5 361024
def k16 : ℕ := l2Key l2M5 33948673
def k17 : ℕ := l2Key l2M5 50335840
def k18 : ℕ := l2Key l2M5 134223616
def k19 : ℕ := l2Key l2M6 33288
def k20 : ℕ := l2Key l2M6 4196360
def k21 : ℕ := l2Key l2M6 134220288
def k22 : ℕ := l2Key l2M5 377697
def k23 : ℕ := l2Key l2M7 16389
def k24 : ℕ := l2Key l2M7 131089
def k25 : ℕ := l2Key l2M7 4194324
def k26 : ℕ := l2Key l2M8 1130753
def k27 : ℕ := l2Key l2M8 360962
def k28 : ℕ := l2Key l2M8 2491393
def k29 : ℕ := l2Key l2M8 272105474
def k30 : ℕ := l2Key l2M8 402654976
def k31 : ℕ := l2Key l2M5 50730081
def k32 : ℕ := l2Key l2M9 1130784
def k33 : ℕ := l2Key l2M9 98882
def k34 : ℕ := l2Key l2M9 270008450
def k35 : ℕ := l2Key l2M9 16781536
def k36 : ℕ := l2Key l2M9 402658048
def k37 : ℕ := l2Key l2M9 1164130
def k38 : ℕ := l2Key l2M10 1130529
def k39 : ℕ := l2Key l2M10 360514
def k40 : ℕ := l2Key l2M10 36044801
def k41 : ℕ := l2Key l2M10 3670146
def k42 : ℕ := l2Key l2M10 50331872
def k43 : ℕ := l2Key l2M11 16644
def k44 : ℕ := l2Key l2M11 4196356
def k45 : ℕ := l2Key l2M11 134220032
def k46 : ℕ := l2Key l2M10 52822241
def k47 : ℕ := l2Key l2M9 404231042
def k48 : ℕ := l2Key l2M8 406324994
def k49 : ℕ := l2Key l2M12 82208
def k50 : ℕ := l2Key l2M12 98880
def k51 : ℕ := l2Key l2M12 16781408
def k52 : ℕ := l2Key l2M12 134222592
def k53 : ℕ := l2Key l2M13 82177
def k54 : ℕ := l2Key l2M13 360960
def k55 : ℕ := l2Key l2M13 394241
def k56 : ℕ := l2Key l2M13 134219520
def k57 : ℕ := l2Key l2M14 81925
def k58 : ℕ := l2Key l2M14 360456
def k59 : ℕ := l2Key l2M14 393233
def k60 : ℕ := l2Key l2M14 4194332
def k61 : ℕ := l2Key l2M8 1426179
def k62 : ℕ := l2Key l2M15 82180
def k63 : ℕ := l2Key l2M15 98824
def k64 : ℕ := l2Key l2M15 4196364
def k65 : ℕ := l2Key l2M15 134220544
def k66 : ℕ := l2Key l2M16 132112
def k67 : ℕ := l2Key l2M16 4196368
def k68 : ℕ := l2Key l2M16 134220800
def k69 : ℕ := l2Key l2M17 295488
def k70 : ℕ := l2Key l2M17 33948672
def k71 : ℕ := l2Key l2M17 50335808
def k72 : ℕ := l2Key l2M17 134223360
def k73 : ℕ := l2Key l2M18 1065249
def k74 : ℕ := l2Key l2M18 35783681
def k75 : ℕ := l2Key l2M18 272105600
def k76 : ℕ := l2Key l2M18 50335904
def k77 : ℕ := l2Key l2M18 402658560
def k78 : ℕ := l2Key l2M19 16673
def k79 : ℕ := l2Key l2M19 33686529
def k80 : ℕ := l2Key l2M19 50335776
def k81 : ℕ := l2Key l2M19 134223104
def k82 : ℕ := l2Key l2M20 16645
def k83 : ℕ := l2Key l2M20 132113
def k84 : ℕ := l2Key l2M20 4196372
def k85 : ℕ := l2Key l2M20 134221056
def k86 : ℕ := l2Key l2M20 134352145
def k87 : ℕ := l2Key l2M10 1425507
def k88 : ℕ := l2Key l2M21 295490
def k89 : ℕ := l2Key l2M21 36045824
def k90 : ℕ := l2Key l2M21 271057026
def k91 : ℕ := l2Key l2M21 50335936
def k92 : ℕ := l2Key l2M21 402658816
def k93 : ℕ := l2Key l2M22 33346
def k94 : ℕ := l2Key l2M22 268959874
def k95 : ℕ := l2Key l2M22 16781504
def k96 : ℕ := l2Key l2M22 402657792
def k97 : ℕ := l2Key l2M8 2590211
def k98 : ℕ := l2Key l2M23 1130528
def k99 : ℕ := l2Key l2M23 98370
def k100 : ℕ := l2Key l2M23 1572994
def k101 : ℕ := l2Key l2M23 16777440
def k102 : ℕ := l2Key l2M24 1065248
def k103 : ℕ := l2Key l2M24 270008448
def k104 : ℕ := l2Key l2M24 16781472
def k105 : ℕ := l2Key l2M24 402657536
def k106 : ℕ := l2Key l2M18 406328704
def k107 : ℕ := l2Key l2M21 52827328
def k108 : ℕ := l2Key l2M10 1572994
def k109 : ℕ := l2Key l2M8 272187651
def k110 : ℕ := l2Key l2M25 1130501
def k111 : ℕ := l2Key l2M25 360458
def k112 : ℕ := l2Key l2M25 2490385
def k113 : ℕ := l2Key l2M25 12058626
def k114 : ℕ := l2Key l2M25 12582940
def k115 : ℕ := l2Key l2M26 33352
def k116 : ℕ := l2Key l2M26 71305224
def k117 : ℕ := l2Key l2M26 83890240
def k118 : ℕ := l2Key l2M26 134224384
def k119 : ℕ := l2Key l2M8 272499715
def k120 : ℕ := l2Key l2M10 3752099
def k121 : ℕ := l2Key l2M20 4328469
def k122 : ℕ := l2Key l2M18 272122273
def k123 : ℕ := l2Key l2M27 81953
def k124 : ℕ := l2Key l2M27 360512
def k125 : ℕ := l2Key l2M27 33947649
def k126 : ℕ := l2Key l2M27 50331744
def k127 : ℕ := l2Key l2M28 82181
def k128 : ℕ := l2Key l2M28 360968
def k129 : ℕ := l2Key l2M28 394257
def k130 : ℕ := l2Key l2M28 4196380
def k131 : ℕ := l2Key l2M28 134221568
def k132 : ℕ := l2Key l2M28 134614801
def k133 : ℕ := l2Key l2M18 52565153
def k134 : ℕ := l2Key l2M29 1130752
def k135 : ℕ := l2Key l2M29 98818
def k136 : ℕ := l2Key l2M29 270008322
def k137 : ℕ := l2Key l2M29 402653952
def k138 : ℕ := l2Key l2M30 1130756
def k139 : ℕ := l2Key l2M30 98826
def k140 : ℕ := l2Key l2M30 278396930
def k141 : ℕ := l2Key l2M30 12584972
def k142 : ℕ := l2Key l2M30 402656000
def k143 : ℕ := l2Key l2M30 412617474
def k144 : ℕ := l2Key l2M20 148757
def k145 : ℕ := l2Key l2M31 16676
def k146 : ℕ := l2Key l2M31 71305220
def k147 : ℕ := l2Key l2M31 83890208
def k148 : ℕ := l2Key l2M31 134224128
def k149 : ℕ := l2Key l2M21 405280386
def k150 : ℕ := l2Key l2M21 36079170
def k151 : ℕ := l2Key l2M10 36143171
def k152 : ℕ := l2Key l2M20 138415380
def k153 : ℕ := l2Key l2M20 4213013
def k154 : ℕ := l2Key l2M20 134237445
def k155 : ℕ := l2Key l2M32 33290
def k156 : ℕ := l2Key l2M32 277348354
def k157 : ℕ := l2Key l2M32 12584968
def k158 : ℕ := l2Key l2M32 402655744
def k159 : ℕ := l2Key l2M33 294986
def k160 : ℕ := l2Key l2M33 36044816
def k161 : ℕ := l2Key l2M33 11010178
def k162 : ℕ := l2Key l2M33 79691800
def k163 : ℕ := l2Key l2M33 117440704
def k164 : ℕ := l2Key l2M33 44957842
def k165 : ℕ := l2Key l2M13 377601
def k166 : ℕ := l2Key l2M12 115552
def k167 : ℕ := l2Key l2M34 81957
def k168 : ℕ := l2Key l2M34 360520
def k169 : ℕ := l2Key l2M34 33947665
def k170 : ℕ := l2Key l2M34 71303196
def k171 : ℕ := l2Key l2M34 117440608
def k172 : ℕ := l2Key l2M28 138415900
def k173 : ℕ := l2Key l2M35 82212
def k174 : ℕ := l2Key l2M35 98888
def k175 : ℕ := l2Key l2M35 71305228
def k176 : ℕ := l2Key l2M35 83890272
def k177 : ℕ := l2Key l2M35 134224640
def k178 : ℕ := l2Key l2M10 37617795
def k179 : ℕ := l2Key l2M13 493057
def k180 : ℕ := l2Key l2M28 4590621
def k181 : ℕ := l2Key l2M28 134303493
def k182 : ℕ := l2Key l2M36 1130757
def k183 : ℕ := l2Key l2M36 360970
def k184 : ℕ := l2Key l2M36 2491409
def k185 : ℕ := l2Key l2M36 280494082
def k186 : ℕ := l2Key l2M36 12584988
def k187 : ℕ := l2Key l2M36 402657024
def k188 : ℕ := l2Key l2M36 405147409
def k189 : ℕ := l2Key l2M36 415108883
def k190 : ℕ := l2Key l2M28 4278557
def k191 : ℕ := l2Key l2M37 16421
def k192 : ℕ := l2Key l2M37 33685521
def k193 : ℕ := l2Key l2M37 71303188
def k194 : ℕ := l2Key l2M37 117440544
def k195 : ℕ := l2Key l2M38 16677
def k196 : ℕ := l2Key l2M38 33686545
def k197 : ℕ := l2Key l2M38 71305236
def k198 : ℕ := l2Key l2M38 117444640
def k199 : ℕ := l2Key l2M38 134225152
def k200 : ℕ := l2Key l2M38 167910673
def k201 : ℕ := l2Key l2M39 1065253
def k202 : ℕ := l2Key l2M39 35783697
def k203 : ℕ := l2Key l2M39 280494208
def k204 : ℕ := l2Key l2M39 79693844
def k205 : ℕ := l2Key l2M39 117444768
def k206 : ℕ := l2Key l2M39 402660608
def k207 : ℕ := l2Key l2M39 438443281
def k208 : ℕ := l2Key l2M39 448404881
def k209 : ℕ := l2Key l2M28 377613
def k210 : ℕ := l2Key l2M28 493081
def k211 : ℕ := l2Key l2M25 12451859
def k212 : ℕ := l2Key l2M5 34047553
def k213 : ℕ := l2Key l2M5 134305569
def k214 : ℕ := l2Key l2M28 476437
def k215 : ℕ := l2Key l2M17 50730048
def k216 : ℕ := l2Key l2M40 295496
def k217 : ℕ := l2Key l2M40 33948688
def k218 : ℕ := l2Key l2M40 71305240
def k219 : ℕ := l2Key l2M40 117444672
def k220 : ℕ := l2Key l2M40 134225408
def k221 : ℕ := l2Key l2M41 295432
def k222 : ℕ := l2Key l2M41 394256
def k223 : ℕ := l2Key l2M41 4196376
def k224 : ℕ := l2Key l2M41 134221312
def k225 : ℕ := l2Key l2M42 33354
def k226 : ℕ := l2Key l2M42 277348482
def k227 : ℕ := l2Key l2M42 79693832
def k228 : ℕ := l2Key l2M42 83890368
def k229 : ℕ := l2Key l2M42 402659840
def k230 : ℕ := l2Key l2M42 411572866
def k231 : ℕ := l2Key l2M8 394241
def k232 : ℕ := l2Key l2M43 1130533
def k233 : ℕ := l2Key l2M43 360522
def k234 : ℕ := l2Key l2M43 36044817
def k235 : ℕ := l2Key l2M43 12058754
def k236 : ℕ := l2Key l2M43 79691804
def k237 : ℕ := l2Key l2M43 117440736
def k238 : ℕ := l2Key l2M43 46006419
def k239 : ℕ := l2Key l2M44 295498
def k240 : ℕ := l2Key l2M44 36045840
def k241 : ℕ := l2Key l2M44 279445634
def k242 : ℕ := l2Key l2M44 79693848
def k243 : ℕ := l2Key l2M44 117444800
def k244 : ℕ := l2Key l2M44 402660864
def k245 : ℕ := l2Key l2M44 438705680
def k246 : ℕ := l2Key l2M44 447618706
def k247 : ℕ := l2Key l2M45 295434
def k248 : ℕ := l2Key l2M45 2491408
def k249 : ℕ := l2Key l2M45 279445506
def k250 : ℕ := l2Key l2M45 12584984
def k251 : ℕ := l2Key l2M45 402656768
def k252 : ℕ := l2Key l2M14 376845
def k253 : ℕ := l2Key l2M10 33947649
def k254 : ℕ := l2Key l2M23 1163362
def k255 : ℕ := l2Key l2M15 115468
def k256 : ℕ := l2Key l2M46 1130785
def k257 : ℕ := l2Key l2M46 361026
def k258 : ℕ := l2Key l2M46 36045825
def k259 : ℕ := l2Key l2M46 272105602
def k260 : ℕ := l2Key l2M46 50335968
def k261 : ℕ := l2Key l2M46 402659072
def k262 : ℕ := l2Key l2M46 406329218
def k263 : ℕ := l2Key l2M46 404231042
def k264 : ℕ := l2Key l2M43 1425519
def k265 : ℕ := l2Key l2M25 2588699
def k266 : ℕ := l2Key l2M25 1425423
def k267 : ℕ := l2Key l2M47 1130788
def k268 : ℕ := l2Key l2M47 98890
def k269 : ℕ := l2Key l2M47 278397058
def k270 : ℕ := l2Key l2M47 79693836
def k271 : ℕ := l2Key l2M47 83890400
def k272 : ℕ := l2Key l2M47 402660096
def k273 : ℕ := l2Key l2M47 412621698
def k274 : ℕ := l2Key l2M9 270090658
def k275 : ℕ := l2Key l2M25 16252958
def k276 : ℕ := l2Key l2M48 35783680
def k277 : ℕ := l2Key l2M48 271057024
def k278 : ℕ := l2Key l2M48 50335872
def k279 : ℕ := l2Key l2M48 402658304
def k280 : ℕ := l2Key l2M33 8913026
def k281 : ℕ := l2Key l2M30 282593294
def k282 : ℕ := l2Key l2M25 12140551
def k283 : ℕ := l2Key l2M5 184555360
def k284 : ℕ := l2Key l2M49 33686544
def k285 : ℕ := l2Key l2M49 71305232
def k286 : ℕ := l2Key l2M49 117444608
def k287 : ℕ := l2Key l2M49 134224896
def k288 : ℕ := l2Key l2M47 1164142
def k289 : ℕ := l2Key l2M23 1654946
def k290 : ℕ := l2Key l2M8 3622145
def k291 : ℕ := l2Key l2M9 419435488
def k292 : ℕ := l2Key l2M36 414715650
def k293 : ℕ := l2Key l2M36 412617474
def k294 : ℕ := l2Key l2M20 1024
def k295 : ℕ := l2Key l2M50 1065252
def k296 : ℕ := l2Key l2M50 278397056
def k297 : ℕ := l2Key l2M50 79693828
def k298 : ℕ := l2Key l2M50 83890336
def k299 : ℕ := l2Key l2M50 402659584
def k300 : ℕ := l2Key l2M50 412621184
def k301 : ℕ := l2Key l2M19 50467873
def k302 : ℕ := l2Key l2M9 16880354
def k303 : ℕ := l2Key l2M10 16777440
def k304 : ℕ := l2Key l2M31 88086564
def k305 : ℕ := l2Key l2M45 283641882
def k306 : ℕ := l2Key l2M45 413666818
def k307 : ℕ := l2Key l2M14 491545
def k308 : ℕ := l2Key l2M8 270008322
def k309 : ℕ := l2Key l2M8 405145345
def k310 : ℕ := l2Key l2M30 1164046
def k311 : ℕ := l2Key l2M36 280888339
def k312 : ℕ := l2Key l2M36 12451859
def k313 : ℕ := l2Key l2M24 404230528
def k314 : ℕ := l2Key l2M51 82213
def k315 : ℕ := l2Key l2M51 361032
def k316 : ℕ := l2Key l2M51 33948689
def k317 : ℕ := l2Key l2M51 71305244
def k318 : ℕ := l2Key l2M51 117444704
def k319 : ℕ := l2Key l2M51 134225664
def k320 : ℕ := l2Key l2M51 168173329
def k321 : ℕ := l2Key l2M46 438703873
def k322 : ℕ := l2Key l2M46 440276867
def k323 : ℕ := l2Key l2M20 134220032
def k324 : ℕ := l2Key l2M40 121641048
def k325 : ℕ := l2Key l2M44 413671042
def k326 : ℕ := l2Key l2M44 411572866
def k327 : ℕ := l2Key l2M40 33982040
def k328 : ℕ := l2Key l2M39 314180753
def k329 : ℕ := l2Key l2M39 45744273
def k330 : ℕ := l2Key l2M20 132112
def k331 : ℕ := l2Key l2M20 132097
def k332 : ℕ := l2Key l2M39 414719360
def k333 : ℕ := l2Key l2M39 412621184
def k334 : ℕ := l2Key l2M32 411568642
def k335 : ℕ := l2Key l2M28 134221312
def k336 : ℕ := l2Key l2M28 134219520
def k337 : ℕ := l2Key l2M5 98880
def k338 : ℕ := l2Key l2M5 33686529
def k339 : ℕ := l2Key l2M32 281544714
def k340 : ℕ := l2Key l2M28 393233
def k341 : ℕ := l2Key l2M10 2490369
def k342 : ℕ := l2Key l2M9 286789858
def k343 : ℕ := l2Key l2M45 2524698
def k344 : ℕ := l2Key l2M10 294978
def k345 : ℕ := l2Key l2M18 36848929
def k346 : ℕ := l2Key l2M37 121634868
def k347 : ℕ := l2Key l2M51 117838961
def k348 : ℕ := l2Key l2M51 252059505
def k349 : ℕ := l2Key l2M46 306054275
def k350 : ℕ := l2Key l2M46 37617795
def k351 : ℕ := l2Key l2M36 2590235
def k352 : ℕ := l2Key l2M36 405245723
def k353 : ℕ := l2Key l2M10 54001890
def k354 : ℕ := l2Key l2M46 52827361
def k355 : ℕ := l2Key l2M46 455481313
def k356 : ℕ := l2Key l2M52 295426
def k357 : ℕ := l2Key l2M52 2491392
def k358 : ℕ := l2Key l2M52 271056898
def k359 : ℕ := l2Key l2M52 402654720
def k360 : ℕ := l2Key l2M17 33982016
def k361 : ℕ := l2Key l2M38 121641012
def k362 : ℕ := l2Key l2M46 36144707
def k363 : ℕ := l2Key l2M46 438802243
def k364 : ℕ := l2Key l2M38 117576753
def k365 : ℕ := l2Key l2M18 452990368
def k366 : ℕ := l2Key l2M38 33685521
def k367 : ℕ := l2Key l2M38 33703221
def k368 : ℕ := l2Key l2M38 134241573
def k369 : ℕ := l2Key l2M51 34047577
def k370 : ℕ := l2Key l2M51 168271705
def k371 : ℕ := l2Key l2M21 452990656
def k372 : ℕ := l2Key l2M38 71321909
def k373 : ℕ := l2Key l2M38 205528340
def k374 : ℕ := l2Key l2M8 403785473
def k375 : ℕ := l2Key l2M10 1064993
def k376 : ℕ := l2Key l2M25 3620885
def k377 : ℕ := l2Key l2M8 271056898
def k378 : ℕ := l2Key l2M9 82208
def k379 : ℕ := l2Key l2M8 1065217
def k380 : ℕ := l2Key l2M18 51401121
def k381 : ℕ := l2Key l2M10 35782657
def k382 : ℕ := l2Key l2M9 268959874
def k383 : ℕ := l2Key l2M8 134219520
def k384 : ℕ := l2Key l2M53 1130500
def k385 : ℕ := l2Key l2M53 98314
def k386 : ℕ := l2Key l2M53 9961474
def k387 : ℕ := l2Key l2M53 12582924
def k388 : ℕ := l2Key l2M25 9961474
def k389 : ℕ := l2Key l2M22 403182210
def k390 : ℕ := l2Key l2M38 104991765
def k391 : ℕ := l2Key l2M36 1426191
def k392 : ℕ := l2Key l2M39 119674033
def k393 : ℕ := l2Key l2M39 522329521
def k394 : ℕ := l2Key l2M8 3670018
def k395 : ℕ := l2Key l2M10 98370
def k396 : ℕ := l2Key l2M18 403723553
def k397 : ℕ := l2Key l2M10 51462369
def k398 : ℕ := l2Key l2M47 96475372
def k399 : ℕ := l2Key l2M43 119931121
def k400 : ℕ := l2Key l2M43 36143195
def k401 : ℕ := l2Key l2M28 509725
def k402 : ℕ := l2Key l2M21 271352514
def k403 : ℕ := l2Key l2M18 305792129
def k404 : ℕ := l2Key l2M38 134223104
def k405 : ℕ := l2Key l2M38 134224896
def k406 : ℕ := l2Key l2M46 1426275
def k407 : ℕ := l2Key l2M44 313394322
def k408 : ℕ := l2Key l2M44 44957842
def k409 : ℕ := l2Key l2M25 393233
def k410 : ℕ := l2Key l2M10 4030658
def k411 : ℕ := l2Key l2M54 294922
def k412 : ℕ := l2Key l2M54 2490384
def k413 : ℕ := l2Key l2M54 11010050
def k414 : ℕ := l2Key l2M54 12582936
def k415 : ℕ := l2Key l2M55 1064993
def k416 : ℕ := l2Key l2M55 35782657
def k417 : ℕ := l2Key l2M55 3670144
def k418 : ℕ := l2Key l2M55 50331808
def k419 : ℕ := l2Key l2M25 13713437
def k420 : ℕ := l2Key l2M25 15073309
def k421 : ℕ := l2Key l2M18 16673
def k422 : ℕ := l2Key l2M24 270025120
def k423 : ℕ := l2Key l2M49 121640976
def k424 : ℕ := l2Key l2M44 119936208
def k425 : ℕ := l2Key l2M44 522591952
def k426 : ℕ := l2Key l2M8 82177
def k427 : ℕ := l2Key l2M8 295426
def k428 : ℕ := l2Key l2M21 402953794
def k429 : ℕ := l2Key l2M21 305005698
def k430 : ℕ := l2Key l2M56 1064997
def k431 : ℕ := l2Key l2M56 35782673
def k432 : ℕ := l2Key l2M56 12058752
def k433 : ℕ := l2Key l2M56 79691796
def k434 : ℕ := l2Key l2M56 117440672
def k435 : ℕ := l2Key l2M56 45744273
def k436 : ℕ := l2Key l2M57 32842
def k437 : ℕ := l2Key l2M57 8913026
def k438 : ℕ := l2Key l2M57 79691784
def k439 : ℕ := l2Key l2M57 83886272
def k440 : ℕ := l2Key l2M41 427544
def k441 : ℕ := l2Key l2M21 50631362
def k442 : ℕ := l2Key l2M10 2621570
def k443 : ℕ := l2Key l2M44 36079194
def k444 : ℕ := l2Key l2M30 415238924
def k445 : ℕ := l2Key l2M41 33288
def k446 : ℕ := l2Key l2M10 3670018
def k447 : ℕ := l2Key l2M44 438738522
def k448 : ℕ := l2Key l2M19 132097
def k449 : ℕ := l2Key l2M18 33686529
def k450 : ℕ := l2Key l2M18 270008448
def k451 : ℕ := l2Key l2M8 2229249
def k452 : ℕ := l2Key l2M13 132097
def k453 : ℕ := l2Key l2M23 524418
def k454 : ℕ := l2Key l2M58 1130532
def k455 : ℕ := l2Key l2M58 98378
def k456 : ℕ := l2Key l2M58 9961602
def k457 : ℕ := l2Key l2M58 79691788
def k458 : ℕ := l2Key l2M58 83886304
def k459 : ℕ := l2Key l2M45 415239704
def k460 : ℕ := l2Key l2M5 16673
def k461 : ℕ := l2Key l2M18 438441217
def k462 : ℕ := l2Key l2M35 115564
def k463 : ℕ := l2Key l2M43 130023676
def k464 : ℕ := l2Key l2M23 81952
def k465 : ℕ := l2Key l2M13 98816
def k466 : ℕ := l2Key l2M12 33344
def k467 : ℕ := l2Key l2M21 33346
def k468 : ℕ := l2Key l2M5 295488
def k469 : ℕ := l2Key l2M5 168171265
def k470 : ℕ := l2Key l2M9 16781504
def k471 : ℕ := l2Key l2M8 403015426
def k472 : ℕ := l2Key l2M5 134223104
def k473 : ℕ := l2Key l2M40 205528600
def k474 : ℕ := l2Key l2M47 9961602
def k475 : ℕ := l2Key l2M43 9961602
def k476 : ℕ := l2Key l2M10 81953
def k477 : ℕ := l2Key l2M5 34030881
def k478 : ℕ := l2Key l2M21 321392834
def k479 : ℕ := l2Key l2M56 33685521
def k480 : ℕ := l2Key l2M56 9961600
def k481 : ℕ := l2Key l2M30 13715724
def k482 : ℕ := l2Key l2M30 403786500
def k483 : ℕ := l2Key l2M19 16781344
def k484 : ℕ := l2Key l2M17 33344
def k485 : ℕ := l2Key l2M8 2491392
def k486 : ℕ := l2Key l2M22 524418
def k487 : ℕ := l2Key l2M21 33948672
def k488 : ℕ := l2Key l2M21 268959874
def k489 : ℕ := l2Key l2M35 88086636
def k490 : ℕ := l2Key l2M34 121634940
def k491 : ℕ := l2Key l2M34 376941
def k492 : ℕ := l2Key l2M20 134219008
def k493 : ℕ := l2Key l2M20 131089
def k494 : ℕ := l2Key l2M32 33288
def k495 : ℕ := l2Key l2M8 98818
def k496 : ℕ := l2Key l2M9 33346
def k497 : ℕ := l2Key l2M18 1065248
def k498 : ℕ := l2Key l2M10 3670144
def k499 : ℕ := l2Key l2M9 16777440
def k500 : ℕ := l2Key l2M5 134219520
def k501 : ℕ := l2Key l2M49 117576720
def k502 : ℕ := l2Key l2M51 134224640
def k503 : ℕ := l2Key l2M47 412703654
def k504 : ℕ := l2Key l2M36 416811806
def k505 : ℕ := l2Key l2M45 15076376
def k506 : ℕ := l2Key l2M45 405147152
def k507 : ℕ := l2Key l2M9 1065248
def k508 : ℕ := l2Key l2M40 117838928
def k509 : ℕ := l2Key l2M51 33947665
def k510 : ℕ := l2Key l2M23 1064992
def k511 : ℕ := l2Key l2M32 268959746
def k512 : ℕ := l2Key l2M32 8912898
def k513 : ℕ := l2Key l2M15 33288
def k514 : ℕ := l2Key l2M28 134220544
def k515 : ℕ := l2Key l2M20 4194324
def k516 : ℕ := l2Key l2M13 295424
def k517 : ℕ := l2Key l2M12 16672
def k518 : ℕ := l2Key l2M43 1064997
def k519 : ℕ := l2Key l2M43 294986
def k520 : ℕ := l2Key l2M47 402758474
def k521 : ℕ := l2Key l2M47 486546400
def k522 : ℕ := l2Key l2M39 483924372
def k523 : ℕ := l2Key l2M28 394241
def k524 : ℕ := l2Key l2M28 4196364
def k525 : ℕ := l2Key l2M20 134220800
def k526 : ℕ := l2Key l2M17 33686528
def k527 : ℕ := l2Key l2M18 1064993
def k528 : ℕ := l2Key l2M5 50696800
def k529 : ℕ := l2Key l2M5 50418017
def k530 : ℕ := l2Key l2M10 50692322
def k531 : ℕ := l2Key l2M10 50331744
def k532 : ℕ := l2Key l2M59 294984
def k533 : ℕ := l2Key l2M59 33947664
def k534 : ℕ := l2Key l2M59 71303192
def k535 : ℕ := l2Key l2M59 117440576
def k536 : ℕ := l2Key l2M47 1065252
def k537 : ℕ := l2Key l2M47 33354
def k538 : ℕ := l2Key l2M44 482876058
def k539 : ℕ := l2Key l2M33 33947664
def k540 : ℕ := l2Key l2M8 2490369
def k541 : ℕ := l2Key l2M30 278479110
def k542 : ℕ := l2Key l2M20 2048
def k543 : ℕ := l2Key l2M18 3670144
def k544 : ℕ := l2Key l2M22 134222336
def k545 : ℕ := l2Key l2M10 37175329
def k546 : ℕ := l2Key l2M9 403788576
def k547 : ℕ := l2Key l2M10 50331840
def k548 : ℕ := l2Key l2M18 134223104
def k549 : ℕ := l2Key l2M9 402756418
def k550 : ℕ := l2Key l2M5 134584128
def k551 : ℕ := l2Key l2M38 121773109
def k552 : ℕ := l2Key l2M36 1065221
def k553 : ℕ := l2Key l2M36 295434
def k554 : ℕ := l2Key l2M36 414060050
def k555 : ℕ := l2Key l2M36 403017482
def k556 : ℕ := l2Key l2M39 532290993
def k557 : ℕ := l2Key l2M36 404226818
def k558 : ℕ := l2Key l2M36 411568642
def k559 : ℕ := l2Key l2M36 415207195
def k560 : ℕ := l2Key l2M20 16
def k561 : ℕ := l2Key l2M20 4196356
def k562 : ℕ := l2Key l2M13 16641
def k563 : ℕ := l2Key l2M23 32834
def k564 : ℕ := l2Key l2M21 295488
def k565 : ℕ := l2Key l2M8 272466434
def k566 : ℕ := l2Key l2M9 270107330
def k567 : ℕ := l2Key l2M9 17912288
def k568 : ℕ := l2Key l2M10 50331808
def k569 : ℕ := l2Key l2M46 1065249
def k570 : ℕ := l2Key l2M46 295490
def k571 : ℕ := l2Key l2M46 439228034
def k572 : ℕ := l2Key l2M46 403019586
def k573 : ℕ := l2Key l2M46 452990944
def k574 : ℕ := l2Key l2M39 130029748
def k575 : ℕ := l2Key l2M46 403182210
def k576 : ℕ := l2Key l2M47 483924878
def k577 : ℕ := l2Key l2M28 4194332
def k578 : ℕ := l2Key l2M45 279839762
def k579 : ℕ := l2Key l2M20 256
def k580 : ℕ := l2Key l2M20 4196368
def k581 : ℕ := l2Key l2M21 295426
def k582 : ℕ := l2Key l2M18 1065217
def k583 : ℕ := l2Key l2M10 360450
def k584 : ℕ := l2Key l2M21 2491392
def k585 : ℕ := l2Key l2M21 16781504
def k586 : ℕ := l2Key l2M24 16781344
def k587 : ℕ := l2Key l2M17 134222336
def k588 : ℕ := l2Key l2M5 134223360
def k589 : ℕ := l2Key l2M26 88086600
def k590 : ℕ := l2Key l2M34 117833841
def k591 : ℕ := l2Key l2M38 251796785
def k592 : ℕ := l2Key l2M39 447356048
def k593 : ℕ := l2Key l2M39 520101280
def k594 : ℕ := l2Key l2M44 130029784
def k595 : ℕ := l2Key l2M39 404230528
def k596 : ℕ := l2Key l2M39 411572352
def k597 : ℕ := l2Key l2M28 4196376
def k598 : ℕ := l2Key l2M28 81925
def k599 : ℕ := l2Key l2M20 16641
def k600 : ℕ := l2Key l2M47 411572866
def k601 : ℕ := l2Key l2M44 402955850
def k602 : ℕ := l2Key l2M44 520101568
def k603 : ℕ := l2Key l2M44 531504850
def k604 : ℕ := l2Key l2M44 403182210
def k605 : ℕ := l2Key l2M46 440375235
def k606 : ℕ := l2Key l2M37 117571633
def k607 : ℕ := l2Key l2M28 82177
def k608 : ℕ := l2Key l2M8 402654720
def k609 : ℕ := l2Key l2M20 4
def k610 : ℕ := l2Key l2M20 1
def k611 : ℕ := l2Key l2M20 16389
def k612 : ℕ := l2Key l2M17 394240
def k613 : ℕ := l2Key l2M24 16672
def k614 : ℕ := l2Key l2M24 268959872
def k615 : ℕ := l2Key l2M21 294978
def k616 : ℕ := l2Key l2M18 271057024
def k617 : ℕ := l2Key l2M5 394241
def k618 : ℕ := l2Key l2M5 16781408
def k619 : ℕ := l2Key l2M21 50331840
def k620 : ℕ := l2Key l2M18 322441376
def k621 : ℕ := l2Key l2M18 402654464
def k622 : ℕ := l2Key l2M34 34046041
def k623 : ℕ := l2Key l2M47 412720074
def k624 : ℕ := l2Key l2M47 496507874
def k625 : ℕ := l2Key l2M43 10043559
def k626 : ℕ := l2Key l2M43 81264798
def k627 : ℕ := l2Key l2M8 1130497
def k628 : ℕ := l2Key l2M18 402658304
def k629 : ℕ := l2Key l2M21 438703616
def k630 : ℕ := l2Key l2M8 402654464
def k631 : ℕ := l2Key l2M5 33947649
def k632 : ℕ := l2Key l2M40 168173072
def k633 : ℕ := l2Key l2M51 377709
def k634 : ℕ := l2Key l2M43 12451859
def k635 : ℕ := l2Key l2M47 412617474
def k636 : ℕ := l2Key l2M43 45744273
def k637 : ℕ := l2Key l2M47 412621184
def k638 : ℕ := l2Key l2M43 44957842
def k639 : ℕ := l2Key l2M20 16644
def k640 : ℕ := l2Key l2M8 402653952
def k641 : ℕ := l2Key l2M25 3670018
def k642 : ℕ := l2Key l2M28 98824
def k643 : ℕ := l2Key l2M9 1572994
def k644 : ℕ := l2Key l2M21 35783680
def k645 : ℕ := l2Key l2M21 50335872
def k646 : ℕ := l2Key l2M18 2229249
def k647 : ℕ := l2Key l2M18 16781472
def k648 : ℕ := l2Key l2M9 134222592
def k649 : ℕ := l2Key l2M40 105253912
def k650 : ℕ := l2Key l2M46 457054179
def k651 : ℕ := l2Key l2M44 447651546
def k652 : ℕ := l2Key l2M14 98312
def k653 : ℕ := l2Key l2M30 9961474
def k654 : ℕ := l2Key l2M28 295432
def k655 : ℕ := l2Key l2M24 1572992
def k656 : ℕ := l2Key l2M10 1130497
def k657 : ℕ := l2Key l2M10 2
def k658 : ℕ := l2Key l2M10 128
def k659 : ℕ := l2Key l2M40 33947664
def k660 : ℕ := l2Key l2M26 16781376
def k661 : ℕ := l2Key l2M14 294920
def k662 : ℕ := l2Key l2M28 82180
def k663 : ℕ := l2Key l2M28 394256
def k664 : ℕ := l2Key l2M8 1130752
def k665 : ℕ := l2Key l2M21 2621570
def k666 : ℕ := l2Key l2M24 134222080
def k667 : ℕ := l2Key l2M8 1
def k668 : ℕ := l2Key l2M21 134223360
def k669 : ℕ := l2Key l2M5 81953
def k670 : ℕ := l2Key l2M8 377601
def k671 : ℕ := l2Key l2M10 1163362
def k672 : ℕ := l2Key l2M40 134223360
def k673 : ℕ := l2Key l2M36 402656000
def k674 : ℕ := l2Key l2M39 448421301
def k675 : ℕ := l2Key l2M43 46088375
def k676 : ℕ := l2Key l2M46 440358819
def k677 : ℕ := l2Key l2M36 415190807
def k678 : ℕ := l2Key l2M43 46104795
def k679 : ℕ := l2Key l2M43 129892595
def k680 : ℕ := l2Key l2M51 121641084
def k681 : ℕ := l2Key l2M39 412637605
def k682 : ℕ := l2Key l2M46 404312995
def k683 : ℕ := l2Key l2M36 412699399
def k684 : ℕ := l2Key l2M57 80216202
def k685 : ℕ := l2Key l2M25 12582936
def k686 : ℕ := l2Key l2M25 11010050
def k687 : ℕ := l2Key l2M25 12582924
def k688 : ℕ := l2Key l2M13 134219008
def k689 : ℕ := l2Key l2M17 16781376
def k690 : ℕ := l2Key l2M10 64
def k691 : ℕ := l2Key l2M10 1048576
def k692 : ℕ := l2Key l2M10 360512
def k693 : ℕ := l2Key l2M9 16781472
def k694 : ℕ := l2Key l2M38 16676
def k695 : ℕ := l2Key l2M38 33686544
def k696 : ℕ := l2Key l2M36 2490385
def k697 : ℕ := l2Key l2M36 1024
def k698 : ℕ := l2Key l2M51 16677
def k699 : ℕ := l2Key l2M51 295496
def k700 : ℕ := l2Key l2M30 270008322
def k701 : ℕ := l2Key l2M45 271056898
def k702 : ℕ := l2Key l2M45 11010050
def k703 : ℕ := l2Key l2M45 402654720
def k704 : ℕ := l2Key l2M30 402653952
def k705 : ℕ := l2Key l2M25 2490384
def k706 : ℕ := l2Key l2M45 12582936
def k707 : ℕ := l2Key l2M25 1130500
def k708 : ℕ := l2Key l2M30 12582924
def k709 : ℕ := l2Key l2M25 1130497
def k710 : ℕ := l2Key l2M25 2490369
def k711 : ℕ := l2Key l2M32 2
def k712 : ℕ := l2Key l2M28 115468
def k713 : ℕ := l2Key l2M28 132112
def k714 : ℕ := l2Key l2M28 16644
def k715 : ℕ := l2Key l2M28 427544
def k716 : ℕ := l2Key l2M10 32
def k717 : ℕ := l2Key l2M10 262144
def k718 : ℕ := l2Key l2M18 35783680
def k719 : ℕ := l2Key l2M10 65536
def k720 : ℕ := l2Key l2M9 98818
def k721 : ℕ := l2Key l2M8 262144
def k722 : ℕ := l2Key l2M8 2097152
def k723 : ℕ := l2Key l2M23 16777408
def k724 : ℕ := l2Key l2M10 2097152
def k725 : ℕ := l2Key l2M10 33554432
def k726 : ℕ := l2Key l2M5 134222592
def k727 : ℕ := l2Key l2M9 16781408
def k728 : ℕ := l2Key l2M8 406324480
def k729 : ℕ := l2Key l2M10 52822208
def k730 : ℕ := l2Key l2M30 134220544
def k731 : ℕ := l2Key l2M36 9961474
def k732 : ℕ := l2Key l2M46 406718211
def k733 : ℕ := l2Key l2M51 134221568
def k734 : ℕ := l2Key l2M51 134225152
def k735 : ℕ := l2Key l2M51 168173072
def k736 : ℕ := l2Key l2M46 404312994
def k737 : ℕ := l2Key l2M33 130023640
def k738 : ℕ := l2Key l2M36 12058626
def k739 : ℕ := l2Key l2M36 393233
def k740 : ℕ := l2Key l2M51 117833841
def k741 : ℕ := l2Key l2M51 134222592
def k742 : ℕ := l2Key l2M51 134224384
def k743 : ℕ := l2Key l2M51 81957
def k744 : ℕ := l2Key l2M38 134224128
def k745 : ℕ := l2Key l2M51 34046041
def k746 : ℕ := l2Key l2M39 402659584
def k747 : ℕ := l2Key l2M57 71303176
def k748 : ℕ := l2Key l2M37 83886112
def k749 : ℕ := l2Key l2M45 2491392
def k750 : ℕ := l2Key l2M30 1130752
def k751 : ℕ := l2Key l2M45 2490384
def k752 : ℕ := l2Key l2M30 1130500
def k753 : ℕ := l2Key l2M25 16
def k754 : ℕ := l2Key l2M28 520
def k755 : ℕ := l2Key l2M25 4
def k756 : ℕ := l2Key l2M14 4194324
def k757 : ℕ := l2Key l2M25 16252948
def k758 : ℕ := l2Key l2M10 1
def k759 : ℕ := l2Key l2M10 1130528
def k760 : ℕ := l2Key l2M21 271057024
def k761 : ℕ := l2Key l2M18 50335872
def k762 : ℕ := l2Key l2M21 402658304
def k763 : ℕ := l2Key l2M8 65536
def k764 : ℕ := l2Key l2M8 1048576
def k765 : ℕ := l2Key l2M21 402654720
def k766 : ℕ := l2Key l2M10 36044800
def k767 : ℕ := l2Key l2M9 270008322
def k768 : ℕ := l2Key l2M9 402653952
def k769 : ℕ := l2Key l2M18 50331808
def k770 : ℕ := l2Key l2M5 50331744
def k771 : ℕ := l2Key l2M8 360450
def k772 : ℕ := l2Key l2M5 360512
def k773 : ℕ := l2Key l2M5 256
def k774 : ℕ := l2Key l2M5 512
def k775 : ℕ := l2Key l2M5 1024
def k776 : ℕ := l2Key l2M9 32
def k777 : ℕ := l2Key l2M9 64
def k778 : ℕ := l2Key l2M9 1130752
def k779 : ℕ := l2Key l2M21 403182210
def k780 : ℕ := l2Key l2M18 50467873
def k781 : ℕ := l2Key l2M28 1
def k782 : ℕ := l2Key l2M28 262144
def k783 : ℕ := l2Key l2M28 16
def k784 : ℕ := l2Key l2M28 1024
def k785 : ℕ := l2Key l2M20 4197396
def k786 : ℕ := l2Key l2M20 17669
def k787 : ℕ := l2Key l2M28 360456
def k788 : ℕ := l2Key l2M28 256
def k789 : ℕ := l2Key l2M28 512
def k790 : ℕ := l2Key l2M28 2048
def k791 : ℕ := l2Key l2M40 71303192
def k792 : ℕ := l2Key l2M28 134220032
def k793 : ℕ := l2Key l2M28 134713113
def k794 : ℕ := l2Key l2M40 134520392
def k795 : ℕ := l2Key l2M50 9961600
def k796 : ℕ := l2Key l2M39 1024
def k797 : ℕ := l2Key l2M51 262656
def k798 : ℕ := l2Key l2M51 81956
def k799 : ℕ := l2Key l2M51 98376
def k800 : ℕ := l2Key l2M51 257
def k801 : ℕ := l2Key l2M51 394257
def k802 : ℕ := l2Key l2M51 251666272
def k803 : ℕ := l2Key l2M51 33558528
def k804 : ℕ := l2Key l2M51 2064
def k805 : ℕ := l2Key l2M51 262144
def k806 : ℕ := l2Key l2M36 414846225
def k807 : ℕ := l2Key l2M51 512
def k808 : ℕ := l2Key l2M51 33686545
def k809 : ℕ := l2Key l2M51 134586184
def k810 : ℕ := l2Key l2M51 1
def k811 : ℕ := l2Key l2M51 256
def k812 : ℕ := l2Key l2M51 33948688
def k813 : ℕ := l2Key l2M51 134225408
def k814 : ℕ := l2Key l2M51 168255285
def k815 : ℕ := l2Key l2M47 81956
def k816 : ℕ := l2Key l2M51 167910673
def k817 : ℕ := l2Key l2M51 134614801
def k818 : ℕ := l2Key l2M51 50335840
def k819 : ℕ := l2Key l2M43 262146
def k820 : ℕ := l2Key l2M28 134582024
def k821 : ℕ := l2Key l2M38 251665696
def k822 : ℕ := l2Key l2M51 4196380
def k823 : ℕ := l2Key l2M36 1048577
def k824 : ℕ := l2Key l2M36 262146
def k825 : ℕ := l2Key l2M36 8388624
def k826 : ℕ := l2Key l2M36 82180
def k827 : ℕ := l2Key l2M36 98824
def k828 : ℕ := l2Key l2M36 268436480
def k829 : ℕ := l2Key l2M36 4196364
def k830 : ℕ := l2Key l2M36 278396930
def k831 : ℕ := l2Key l2M36 134220544
def k832 : ℕ := l2Key l2M51 105253917
def k833 : ℕ := l2Key l2M51 134223616
def k834 : ℕ := l2Key l2M51 34030901
def k835 : ℕ := l2Key l2M51 1024
def k836 : ℕ := l2Key l2M51 134306597
def k837 : ℕ := l2Key l2M51 134307621
def k838 : ℕ := l2Key l2M51 71303196
def k839 : ℕ := l2Key l2M51 33948673
def k840 : ℕ := l2Key l2M51 205527836
def k841 : ℕ := l2Key l2M51 205528860
def k842 : ℕ := l2Key l2M47 482351884
def k843 : ℕ := l2Key l2M36 81925
def k844 : ℕ := l2Key l2M36 360456
def k845 : ℕ := l2Key l2M36 4194332
def k846 : ℕ := l2Key l2M36 1048832
def k847 : ℕ := l2Key l2M36 514
def k848 : ℕ := l2Key l2M36 2098176
def k849 : ℕ := l2Key l2M36 8390656
def k850 : ℕ := l2Key l2M36 98826
def k851 : ℕ := l2Key l2M36 491545
def k852 : ℕ := l2Key l2M36 412616960
def k853 : ℕ := l2Key l2M36 2588699
def k854 : ℕ := l2Key l2M36 402655488
abbrev LCR := { p : Bool × (ℕ → ℕ → List ℕ → Bool) // ∀ s f v,
  p.1=true → l2IH s → List.Nodup v → p.2 s f v=true → Ban 208 f v }
def lcFab (r : L2Rule) : LCR := ⟨(l2RCert r,l2RuleTest r),fun _ _ _ c ih nd h => l2RuleOK c ih nd h⟩
def lcVide : LCR := ⟨(false,fun _ _ _ => false),by simp⟩
def l2Q0 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨5,l2M0,0,n,g,[k0,k1]++u⟩
def l2Q1 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨69,l2M1,3,n,g,[k2,k3,k4]++u⟩
def l2Q2 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨42,l2M2,3,n,g,[k5,k6,k7]++u⟩
def l2Q3 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨98,l2M3,3,n,g,[k8,k9,k10]++u⟩
def l2Q4 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨97,l2M4,3,n,g,[k11,k12,k13]++u⟩
def l2Q5 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨103,l2M5,6,n,g,[k14,k15,k16,k17,k18]++u⟩
def l2Q6 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨82,l2M6,3,n,g,[k19,k20,k21]++u⟩
def l2Q7 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨21,l2M7,3,n,g,[k23,k24,k25]++u⟩
def l2Q8 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨79,l2M8,6,n,g,[k26,k27,k28,k29,k30]++u⟩
def l2Q9 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨107,l2M9,6,n,g,[k32,k33,k34,k35,k36]++u⟩
def l2Q10 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨47,l2M10,6,n,g,[k38,k39,k40,k41,k42]++u⟩
def l2Q11 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨81,l2M11,3,n,g,[k43,k44,k45]++u⟩
def l2Q12 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨99,l2M12,4,n,g,[k49,k50,k51,k52]++u⟩
def l2Q13 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨71,l2M13,4,n,g,[k53,k54,k55,k56]++u⟩
def l2Q14 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨23,l2M14,4,n,g,[k57,k58,k59,k60]++u⟩
def l2Q15 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨83,l2M15,4,n,g,[k62,k63,k64,k65]++u⟩
def l2Q16 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨84,l2M16,3,n,g,[k66,k67,k68]++u⟩
def l2Q17 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨102,l2M17,4,n,g,[k69,k70,k71,k72]++u⟩
def l2Q18 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨109,l2M18,6,n,g,[k73,k74,k75,k76,k77]++u⟩
def l2Q19 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨101,l2M19,4,n,g,[k78,k79,k80,k81]++u⟩
def l2Q20 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨85,l2M20,6,n,g,[k82,k83,k84,k85]++u⟩
def l2Q21 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨110,l2M21,6,n,g,[k88,k89,k90,k91,k92]++u⟩
def l2Q22 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨106,l2M22,4,n,g,[k93,k94,k95,k96]++u⟩
def l2Q23 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨43,l2M23,4,n,g,[k98,k99,k100,k101]++u⟩
def l2Q24 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨105,l2M24,4,n,g,[k102,k103,k104,k105]++u⟩
def l2Q25 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨31,l2M25,6,n,g,[k110,k111,k112,k113,k114]++u⟩
def l2Q26 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨114,l2M26,4,n,g,[k115,k116,k117,k118]++u⟩
def l2Q27 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨39,l2M27,3,n,g,[k123,k124,k125,k126]++u⟩
def l2Q28 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨87,l2M28,7,n,g,[k127,k128,k129,k130,k131]++u⟩
def l2Q29 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨75,l2M29,3,n,g,[k134,k135,k136,k137]++u⟩
def l2Q30 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨91,l2M30,6,n,g,[k138,k139,k140,k141,k142]++u⟩
def l2Q31 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨113,l2M31,4,n,g,[k145,k146,k147,k148]++u⟩
def l2Q32 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨90,l2M32,4,n,g,[k155,k156,k157,k158]++u⟩
def l2Q33 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨62,l2M33,6,n,g,[k159,k160,k161,k162,k163]++u⟩
def l2Q34 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨55,l2M34,5,n,g,[k167,k168,k169,k170,k171]++u⟩
def l2Q35 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨115,l2M35,5,n,g,[k173,k174,k175,k176,k177]++u⟩
def l2Q36 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨95,l2M36,9,n,g,[k182,k183,k184,k185,k186,k187]++u⟩
def l2Q37 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨53,l2M37,4,n,g,[k191,k192,k193,k194]++u⟩
def l2Q38 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨117,l2M38,7,n,g,[k195,k196,k197,k198,k199]++u⟩
def l2Q39 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨125,l2M39,9,n,g,[k201,k202,k203,k204,k205,k206]++u⟩
def l2Q40 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨118,l2M40,6,n,g,[k216,k217,k218,k219,k220]++u⟩
def l2Q41 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨86,l2M41,4,n,g,[k221,k222,k223,k224]++u⟩
def l2Q42 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨122,l2M42,6,n,g,[k225,k226,k227,k228,k229]++u⟩
def l2Q43 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨63,l2M43,8,n,g,[k232,k233,k234,k235,k236,k237]++u⟩
def l2Q44 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨126,l2M44,9,n,g,[k239,k240,k241,k242,k243,k244]++u⟩
def l2Q45 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨94,l2M45,6,n,g,[k247,k248,k249,k250,k251]++u⟩
def l2Q46 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨111,l2M46,9,n,g,[k256,k257,k258,k259,k260,k261]++u⟩
def l2Q47 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨123,l2M47,8,n,g,[k267,k268,k269,k270,k271,k272]++u⟩
def l2Q48 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨108,l2M48,3,n,g,[k276,k277,k278,k279]++u⟩
def l2Q49 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨116,l2M49,4,n,g,[k284,k285,k286,k287]++u⟩
def l2Q50 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨121,l2M50,6,n,g,[k295,k296,k297,k298,k299]++u⟩
def l2Q51 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨119,l2M51,9,n,g,[k314,k315,k316,k317,k318,k319]++u⟩
def l2Q52 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨78,l2M52,3,n,g,[k356,k357,k358,k359]++u⟩
def l2Q53 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨27,l2M53,3,n,g,[k384,k385,k386,k387]++u⟩
def l2Q54 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨30,l2M54,3,n,g,[k411,k412,k413,k414]++u⟩
def l2Q55 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨45,l2M55,3,n,g,[k415,k416,k417,k418]++u⟩
def l2Q56 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨61,l2M56,6,n,g,[k430,k431,k432,k433,k434]++u⟩
def l2Q57 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨58,l2M57,4,n,g,[k436,k437,k438,k439]++u⟩
def l2Q58 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨59,l2M58,5,n,g,[k454,k455,k456,k457,k458]++u⟩
def l2Q59 (n g : ℕ) (u : List ℕ) : LCR := lcFab ⟨54,l2M59,3,n,g,[k532,k533,k534,k535]++u⟩
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB0 : Array LCR := #[l2Q0 0 0 [],l2Q1 0 0 [],l2Q2 0 0 [],l2Q3 0 0 [],l2Q4 0 0 [],l2Q5 0 0 [],l2Q6 0 0 [],l2Q5 1 272 [k22],l2Q7 0 0 [],l2Q8 0 0 [],l2Q5 1 306 [k31],l2Q9 1 272 [k37],l2Q10 0 0 [],l2Q11 0 0 [],l2Q9 0 0 [],l2Q10 1 322 [k46],l2Q9 1 322 [k47],l2Q8 1 323 [k48],l2Q12 0 0 [],l2Q13 0 0 [],l2Q14 0 0 [],l2Q8 1 272 [k61],l2Q15 0 0 [],l2Q16 0 0 [],l2Q17 0 0 [],l2Q18 0 0 [],l2Q19 0 0 [],l2Q20 1 305 [k86],l2Q10 1 272 [k87],l2Q20 0 0 [],l2Q21 0 0 [],l2Q22 0 0 []]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB1 : Array LCR := #[l2Q8 1 289 [k97],l2Q23 0 0 [],l2Q24 0 0 [],l2Q18 1 322 [k106],l2Q21 1 305 [k107],l2Q10 1 818 [k108],l2Q8 1 304 [k109],l2Q25 0 0 [],l2Q26 0 0 [],l2Q8 1 306 [k119],l2Q10 1 304 [k120],l2Q20 1 289 [k121],l2Q18 1 288 [k122],l2Q27 0 0 [],l2Q28 1 322 [k132],l2Q28 0 0 [],l2Q18 1 305 [k133],l2Q29 0 0 [],l2Q30 1 322 [k143],l2Q20 1 272 [k144],l2Q31 0 0 [],l2Q21 1 322 [k149],l2Q30 0 0 [],l2Q21 1 272 [k150],l2Q10 1 289 [k151],l2Q20 1 306 [k152],l2Q20 1 288 [k153],l2Q20 1 304 [k154],l2Q32 0 0 [],l2Q33 1 289 [k164],l2Q13 1 272 [k165],l2Q12 1 272 [k166]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB2 : Array LCR := #[l2Q34 0 0 [],l2Q28 1 323 [k172],l2Q35 0 0 [],l2Q10 1 306 [k178],l2Q13 1 289 [k179],l2Q28 1 306 [k180],l2Q28 1 320 [k181],l2Q36 2 363858 [k188,k189],l2Q28 1 304 [k190],l2Q37 0 0 [],l2Q38 1 321 [k200],l2Q39 2 362833 [k207,k208],l2Q28 1 272 [k209],l2Q28 1 289 [k210],l2Q25 1 306 [k211],l2Q5 1 289 [k212],l2Q5 1 320 [k213],l2Q28 1 288 [k214],l2Q17 1 289 [k215],l2Q40 0 0 [],l2Q41 0 0 [],l2Q42 1 321 [k230],l2Q8 1 562 [k231],l2Q43 1 306 [k238],l2Q44 2 362833 [k245,k246],l2Q45 0 0 [],l2Q14 1 272 [k252],l2Q10 1 562 [k253],l2Q23 1 272 [k254],l2Q15 1 272 [k255],l2Q46 2 887123 [k262,k263],l2Q43 2 313616 [k264,k238]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB3 : Array LCR := #[l2Q25 1 289 [k265],l2Q25 1 272 [k266],l2Q28 2 327952 [k209,k181],l2Q28 2 311568 [k209,k190],l2Q47 1 338 [k273],l2Q9 1 288 [k274],l2Q25 1 323 [k275],l2Q48 0 0 [],l2Q33 1 801 [k280],l2Q30 1 306 [k281],l2Q25 1 304 [k282],l2Q5 1 323 [k283],l2Q49 0 0 [],l2Q47 2 346384 [k288,k273],l2Q23 1 288 [k289],l2Q8 1 288 [k290],l2Q9 1 323 [k291],l2Q36 2 887123 [k292,k293],l2Q20 1 49 [k294],l2Q50 1 321 [k300],l2Q19 1 289 [k301],l2Q9 1 305 [k302],l2Q10 1 834 [k303],l2Q31 1 289 [k304],l2Q45 1 306 [k305],l2Q45 1 322 [k306],l2Q14 1 289 [k307],l2Q8 1 818 [k308],l2Q8 1 322 [k309],l2Q30 1 272 [k310],l2Q36 2 890162 [k311,k312],l2Q24 1 305 [k313]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB4 : Array LCR := #[l2Q51 1 338 [k320],l2Q46 2 363858 [k321,k322],l2Q36 2 362835 [k292,k189],l2Q28 2 330017 [k210,k132],l2Q20 1 817 [k323],l2Q38 0 0 [],l2Q40 1 306 [k324],l2Q36 1 338 [k188],l2Q44 2 886098 [k325,k326],l2Q40 1 272 [k327],l2Q51 0 0 [],l2Q39 2 890145 [k328,k329],l2Q20 1 784 [k330],l2Q20 1 545 [k331],l2Q36 2 365874 [k311,k189],l2Q39 2 886098 [k332,k333],l2Q32 1 305 [k334],l2Q28 1 832 [k335],l2Q28 1 835 [k336],l2Q5 1 545 [k337],l2Q5 1 801 [k338],l2Q32 1 289 [k339],l2Q28 1 578 [k340],l2Q10 1 578 [k341],l2Q5 2 331058 [k31,k283],l2Q9 1 306 [k342],l2Q36 1 339 [k292],l2Q9 2 331074 [k47,k291],l2Q45 1 272 [k343],l2Q10 1 784 [k344],l2Q18 1 272 [k345],l2Q37 1 306 [k346]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB5 : Array LCR := #[l2Q51 2 365890 [k347,k348],l2Q46 2 890162 [k349,k350],l2Q36 2 365857 [k351,k352],l2Q10 1 323 [k353],l2Q36 0 0 [],l2Q46 2 365890 [k354,k355],l2Q52 0 0 [],l2Q17 1 272 [k360],l2Q38 1 306 [k361],l2Q39 2 361810 [k332,k208],l2Q46 2 365857 [k362,k363],l2Q8 2 331024 [k61,k48],l2Q18 2 330033 [k133,k106],l2Q38 1 305 [k364],l2Q18 1 323 [k365],l2Q38 1 577 [k366],l2Q38 1 272 [k367],l2Q38 1 320 [k368],l2Q46 1 338 [k321],l2Q51 2 365857 [k369,k370],l2Q21 1 323 [k371],l2Q38 1 288 [k372],l2Q38 1 322 [k373],l2Q39 1 337 [k207],l2Q36 1 306 [k311],l2Q46 2 365874 [k349,k322],l2Q46 2 362835 [k262,k322],l2Q28 2 313633 [k210,k180],l2Q8 1 320 [k374],l2Q10 1 528 [k375],l2Q36 3 389368097 [k351,k188,k189],l2Q46 3 389368130 [k354,k321,k322]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB6 : Array LCR := #[l2Q51 1 322 [k347],l2Q39 2 365857 [k328,k208],l2Q36 2 347425 [k351,k292],l2Q25 1 288 [k376],l2Q8 1 816 [k377],l2Q9 1 544 [k378],l2Q8 1 528 [k379],l2Q18 1 304 [k380],l2Q10 1 801 [k381],l2Q9 1 800 [k382],l2Q21 2 330033 [k107,k149],l2Q8 1 835 [k383],l2Q38 2 313632 [k372,k361],l2Q38 2 330034 [k361,k373],l2Q46 2 346434 [k354,k321],l2Q46 1 322 [k354],l2Q53 0 0 [],l2Q25 1 818 [k388],l2Q22 1 305 [k389],l2Q38 1 289 [k390],l2Q51 2 346434 [k347,k320],l2Q36 3 285576530 [k188,k189,k391],l2Q39 2 365889 [k392,k393],l2Q46 2 347458 [k354,k262],l2Q36 1 289 [k351],l2Q8 1 579 [k394],l2Q10 1 545 [k395],l2Q18 1 320 [k396],l2Q10 1 320 [k397],l2Q36 3 928353618 [k188,k189,k312],l2Q47 2 346435 [k398,k273],l2Q43 1 338 [k399]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB7 : Array LCR := #[l2Q36 2 346401 [k351,k188],l2Q43 1 289 [k400],l2Q28 2 331072 [k181,k172],l2Q28 2 346384 [k209,k401],l2Q21 1 288 [k402],l2Q5 2 313616 [k22,k31],l2Q10 2 330000 [k87,k46],l2Q18 1 289 [k403],l2Q38 1 834 [k404],l2Q38 1 832 [k405],l2Q46 3 285576530 [k321,k322,k406],l2Q46 2 346401 [k362,k321],l2Q39 2 346433 [k392,k332],l2Q44 2 890145 [k407,k408],l2Q39 1 338 [k332],l2Q51 1 289 [k369],l2Q46 1 289 [k362],l2Q25 1 562 [k409],l2Q5 2 327952 [k22,k213],l2Q10 1 305 [k410],l2Q39 3 928352593 [k207,k208,k329],l2Q36 3 925207890 [k188,k189,k293],l2Q39 3 388318529 [k392,k207,k208],l2Q46 3 389368097 [k362,k321,k322],l2Q46 2 347425 [k362,k262],l2Q54 0 0 [],l2Q55 0 0 [],l2Q25 1 320 [k419],l2Q25 1 322 [k420],l2Q28 2 331024 [k209,k172],l2Q28 2 344353 [k210,k401],l2Q18 1 544 [k421]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB8 : Array LCR := #[l2Q24 1 272 [k422],l2Q49 1 289 [k423],l2Q46 0 0 [],l2Q51 2 346401 [k369,k320],l2Q44 2 365889 [k424,k425],l2Q8 1 560 [k426],l2Q8 1 784 [k427],l2Q21 1 320 [k428],l2Q21 1 289 [k429],l2Q39 3 924158289 [k207,k208,k333],l2Q46 1 306 [k349],l2Q44 2 365857 [k407,k246],l2Q46 1 339 [k262],l2Q44 2 361810 [k325,k246],l2Q56 1 289 [k435],l2Q57 0 0 [],l2Q41 1 272 [k440],l2Q20 2 313632 [k153,k152],l2Q28 2 327969 [k210,k181],l2Q10 2 575760 [k87,k253],l2Q10 2 837904 [k87,k108],l2Q21 1 304 [k441],l2Q10 2 330546 [k108,k46],l2Q10 1 816 [k442],l2Q39 0 0 [],l2Q46 3 928353618 [k321,k322,k350],l2Q46 3 925207890 [k321,k322,k263],l2Q44 3 388318480 [k443,k245,k246],l2Q30 1 323 [k444],l2Q41 1 528 [k445],l2Q9 2 330000 [k37,k47],l2Q10 1 579 [k446]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB9 : Array LCR := #[l2Q44 3 388318529 [k424,k245,k246],l2Q44 2 346433 [k424,k325],l2Q44 2 365840 [k443,k447],l2Q20 2 312592 [k144,k86],l2Q19 1 545 [k448],l2Q18 1 545 [k449],l2Q8 2 575760 [k61,k231],l2Q18 1 801 [k450],l2Q8 2 837904 [k61,k308],l2Q8 1 801 [k451],l2Q13 1 801 [k452],l2Q23 1 800 [k453],l2Q44 3 928352593 [k245,k246,k408],l2Q44 3 924158289 [k245,k246,k326],l2Q39 1 321 [k392],l2Q39 1 289 [k328],l2Q44 2 346384 [k443,k325],l2Q56 0 0 [],l2Q58 0 0 [],l2Q45 1 323 [k459],l2Q28 3 339018000 [k209,k181,k172],l2Q5 1 528 [k460],l2Q8 2 331314 [k231,k48],l2Q18 1 321 [k461],l2Q35 1 272 [k462],l2Q43 2 348466 [k238,k463],l2Q39 2 345409 [k392,k207],l2Q23 1 544 [k464],l2Q13 1 545 [k465],l2Q12 1 784 [k466],l2Q21 1 528 [k467],l2Q5 1 784 [k468]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB10 : Array LCR := #[l2Q5 1 322 [k469],l2Q9 1 816 [k470],l2Q8 1 321 [k471],l2Q5 1 833 [k472],l2Q40 2 330034 [k324,k473],l2Q50 0 0 [],l2Q44 1 337 [k245],l2Q47 2 346706 [k474,k273],l2Q43 1 818 [k475],l2Q10 1 560 [k476],l2Q5 1 288 [k477],l2Q21 1 306 [k478],l2Q40 1 322 [k473],l2Q43 2 314162 [k475,k238],l2Q56 1 545 [k479],l2Q56 1 801 [k480],l2Q30 1 304 [k481],l2Q30 1 320 [k482],l2Q19 1 801 [k483],l2Q17 1 528 [k484],l2Q47 1 594 [k474],l2Q44 2 345409 [k424,k245],l2Q44 1 321 [k424],l2Q43 2 348978 [k475,k463],l2Q43 2 837904 [k264,k475],l2Q8 1 800 [k485],l2Q22 1 561 [k486],l2Q21 1 545 [k487],l2Q21 1 801 [k488],l2Q35 1 306 [k489],l2Q34 1 323 [k490],l2Q34 1 272 [k491]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB11 : Array LCR := #[l2Q44 2 345360 [k443,k245],l2Q44 1 289 [k407],l2Q44 1 338 [k325],l2Q44 1 272 [k443],l2Q28 2 313632 [k214,k180],l2Q28 2 330016 [k214,k132],l2Q28 2 311584 [k214,k190],l2Q28 2 327968 [k214,k181],l2Q28 2 331056 [k190,k172],l2Q28 2 331058 [k180,k172],l2Q20 2 313633 [k121,k152],l2Q28 2 331074 [k132,k172],l2Q28 2 330000 [k209,k132],l2Q20 1 818 [k492],l2Q20 1 561 [k493],l2Q32 1 528 [k494],l2Q8 1 545 [k495],l2Q9 1 784 [k496],l2Q18 1 528 [k497],l2Q10 1 817 [k498],l2Q9 1 579 [k499],l2Q5 1 835 [k500],l2Q49 1 288 [k501],l2Q51 1 850 [k502],l2Q47 2 360786 [k273,k503],l2Q36 3 390957395 [k292,k293,k504],l2Q36 3 928352595 [k292,k189,k312],l2Q39 3 928351570 [k332,k208,k329],l2Q45 1 305 [k505],l2Q45 1 321 [k506],l2Q9 1 528 [k507],l2Q40 1 305 [k508]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB12 : Array LCR := #[l2Q47 0 0 [],l2Q51 1 594 [k509],l2Q33 0 0 [],l2Q23 1 528 [k510],l2Q32 1 545 [k511],l2Q32 1 561 [k512],l2Q20 2 311568 [k144,k154],l2Q28 2 311585 [k210,k190],l2Q28 2 313616 [k209,k180],l2Q15 1 784 [k513],l2Q8 2 327952 [k61,k374],l2Q28 1 834 [k514],l2Q20 1 562 [k515],l2Q28 2 331041 [k210,k172],l2Q13 1 784 [k516],l2Q12 1 528 [k517],l2Q10 2 330288 [k476,k46],l2Q10 2 330544 [k442,k46],l2Q42 0 0 [],l2Q43 2 313872 [k518,k238],l2Q43 2 314128 [k519,k238],l2Q33 2 296737 [k280,k164],l2Q47 2 346449 [k520,k273],l2Q47 3 354764048 [k288,k520,k273],l2Q47 2 348498 [k273,k521],l2Q47 3 356862275 [k398,k273,k521],l2Q39 3 389907794 [k332,k333,k522],l2Q25 2 327952 [k266,k419],l2Q28 1 562 [k523],l2Q28 1 818 [k524],l2Q25 2 330017 [k265,k420],l2Q20 2 313648 [k154,k152]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB13 : Array LCR := #[l2Q20 2 313649 [k86,k152],l2Q8 2 330017 [k97,k309],l2Q20 1 816 [k525],l2Q17 1 784 [k526],l2Q8 2 331297 [k495,k48],l2Q18 1 576 [k527],l2Q8 2 331553 [k451,k48],l2Q5 1 305 [k528],l2Q5 1 304 [k529],l2Q10 1 321 [k530],l2Q10 1 835 [k531],l2Q59 0 0 [],l2Q38 2 329009 [k364,k200],l2Q47 2 346640 [k536,k273],l2Q47 2 346896 [k537,k273],l2Q47 2 279122 [k474,k288],l2Q39 3 924161313 [k328,k208,k333],l2Q36 3 925209906 [k311,k189,k293],l2Q44 3 389907794 [k325,k326,k538],l2Q33 1 545 [k539],l2Q20 2 296208 [k144,k121],l2Q20 2 295184 [k144,k153],l2Q20 2 312609 [k121,k86],l2Q8 1 578 [k540],l2Q30 1 288 [k541],l2Q20 1 50 [k542],l2Q18 1 578 [k543],l2Q22 1 817 [k544],l2Q10 1 288 [k545],l2Q10 2 330016 [k545,k46],l2Q9 1 320 [k546],l2Q10 1 832 [k547]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB14 : Array LCR := #[l2Q5 2 330034 [k31,k469],l2Q18 1 834 [k548],l2Q9 1 321 [k549],l2Q5 1 321 [k550],l2Q38 2 330048 [k368,k373],l2Q38 2 327986 [k361,k368],l2Q38 2 345394 [k361,k551],l2Q44 0 0 [],l2Q43 0 0 [],l2Q51 2 346706 [k509,k320],l2Q51 2 346962 [k502,k320],l2Q36 3 554011986 [k188,k189,k552],l2Q36 3 822447442 [k188,k189,k553],l2Q36 3 923110738 [k188,k189,k554],l2Q36 3 353733970 [k188,k189,k555],l2Q39 3 392513857 [k392,k332,k556],l2Q36 3 286102834 [k311,k312,k391],l2Q36 3 927828307 [k292,k293,k557],l2Q36 3 923634003 [k292,k293,k558],l2Q36 3 286099795 [k292,k293,k391],l2Q36 3 392514849 [k351,k292,k559],l2Q28 3 339001616 [k209,k190,k172],l2Q20 2 311584 [k153,k154],l2Q28 3 339003681 [k210,k180,k172],l2Q28 3 339020065 [k210,k132,k172],l2Q20 1 33 [k560],l2Q20 1 801 [k561],l2Q8 2 331041 [k97,k48],l2Q13 1 528 [k562],l2Q23 1 784 [k563],l2Q21 1 544 [k564],l2Q5 2 313632 [k477,k31]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB15 : Array LCR := #[l2Q8 1 305 [k565],l2Q9 2 330017 [k566,k47],l2Q8 2 331057 [k565,k48],l2Q9 1 304 [k567],l2Q10 1 833 [k568],l2Q46 3 554011986 [k321,k322,k569],l2Q46 3 822447442 [k321,k322,k570],l2Q46 3 923110738 [k321,k322,k571],l2Q46 3 353733970 [k321,k322,k572],l2Q46 3 356879698 [k321,k322,k573],l2Q39 3 339052881 [k207,k208,k574],l2Q46 3 286102834 [k349,k350,k406],l2Q44 3 924161313 [k407,k246,k326],l2Q46 3 925209906 [k349,k322,k263],l2Q46 3 923634003 [k262,k263,k575],l2Q47 2 363858 [k273,k576],l2Q39 3 339576146 [k332,k333,k574],l2Q46 3 286099795 [k262,k263,k406],l2Q44 3 928351570 [k325,k246,k408],l2Q46 3 928352595 [k262,k322,k350],l2Q20 2 296224 [k153,k121],l2Q20 2 312624 [k154,k86],l2Q28 1 579 [k577],l2Q45 1 289 [k578],l2Q20 1 48 [k579],l2Q20 1 800 [k580],l2Q25 2 331024 [k266,k275],l2Q25 2 331041 [k265,k275],l2Q21 1 560 [k581],l2Q18 1 560 [k582],l2Q10 1 577 [k583],l2Q21 1 561 [k584]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB16 : Array LCR := #[l2Q10 2 279106 [k341,k87],l2Q21 1 817 [k585],l2Q10 2 854288 [k87,k303],l2Q24 1 801 [k586],l2Q18 3 339020081 [k133,k106,k365],l2Q9 2 330034 [k342,k47],l2Q17 1 817 [k587],l2Q21 2 331074 [k149,k371],l2Q5 1 832 [k588],l2Q10 2 311585 [k151,k120],l2Q26 1 289 [k589],l2Q38 3 337969458 [k361,k368,k373],l2Q34 1 322 [k590],l2Q38 2 330033 [k364,k373],l2Q38 2 346417 [k364,k551],l2Q38 2 348465 [k364,k591],l2Q5 2 313633 [k212,k31],l2Q43 2 346418 [k238,k399],l2Q43 2 313633 [k400,k238],l2Q39 3 923109713 [k207,k208,k592],l2Q36 4 292980886866 [k188,k189,k554,k391],l2Q36 4 292411510098 [k188,k189,k555,k391],l2Q39 3 356878673 [k207,k208,k593],l2Q39 4 347175487825 [k207,k208,k593,k574],l2Q44 3 339052881 [k245,k246,k594],l2Q39 3 926778706 [k332,k333,k595],l2Q39 3 923632978 [k332,k333,k596],l2Q44 3 339576146 [k325,k326,k594],l2Q28 1 816 [k597],l2Q28 1 576 [k598],l2Q20 1 544 [k599],l2Q18 2 312592 [k345,k133]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB17 : Array LCR := #[l2Q9 1 289 [k566],l2Q18 2 331057 [k133,k365],l2Q21 3 339020081 [k107,k149,k371],l2Q18 2 329009 [k133,k461],l2Q8 2 311585 [k97,k109],l2Q40 2 312592 [k327,k508],l2Q39 4 967829701953 [k392,k207,k208,k329],l2Q36 4 967830751521 [k351,k188,k189,k312],l2Q46 4 292980886866 [k321,k322,k571,k406],l2Q47 2 885074 [k273,k600],l2Q44 3 352684369 [k245,k246,k601],l2Q46 4 292411510098 [k321,k322,k572,k406],l2Q44 3 356878673 [k245,k246,k602],l2Q44 4 347175487825 [k245,k246,k602,k594],l2Q44 3 392513857 [k424,k325,k603],l2Q44 3 926778706 [k325,k326,k604],l2Q46 3 392514849 [k362,k262,k605],l2Q37 1 305 [k606],l2Q28 1 560 [k607],l2Q8 1 832 [k608],l2Q20 1 32 [k609],l2Q20 1 16 [k610],l2Q20 1 560 [k611],l2Q17 1 545 [k612],l2Q8 2 279107 [k394,k61],l2Q24 1 528 [k613],l2Q24 1 784 [k614],l2Q21 1 576 [k615],l2Q18 1 800 [k616],l2Q5 1 562 [k617],l2Q18 2 313121 [k450,k133],l2Q5 1 818 [k618]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB18 : Array LCR := #[l2Q21 1 579 [k619],l2Q8 2 855312 [k61,k383],l2Q21 2 330034 [k478,k149],l2Q18 2 330034 [k620,k106],l2Q18 1 835 [k621],l2Q18 2 331074 [k106,k365],l2Q34 1 289 [k622],l2Q51 2 870994 [k509,k502],l2Q46 4 967830751554 [k354,k321,k322,k350],l2Q44 4 967829701904 [k443,k245,k246,k408],l2Q47 2 361810 [k273,k623],l2Q47 2 364882 [k273,k624],l2Q43 2 361266 [k475,k625],l2Q43 2 365362 [k475,k626],l2Q8 1 576 [k627],l2Q30 2 313616 [k310,k281],l2Q30 2 330000 [k310,k143],l2Q18 2 312864 [k421,k133],l2Q18 1 832 [k628],l2Q5 2 575760 [k22,k617],l2Q21 2 330273 [k487,k149],l2Q18 2 313120 [k616,k133],l2Q21 2 330016 [k402,k149],l2Q5 2 837904 [k22,k618],l2Q21 2 331057 [k107,k371],l2Q21 2 329009 [k107,k629],l2Q18 1 306 [k620],l2Q8 1 833 [k630],l2Q5 1 578 [k631],l2Q40 1 321 [k632],l2Q44 4 967829701953 [k424,k245,k246,k408],l2Q46 4 967830751521 [k362,k321,k322,k350]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB19 : Array LCR := #[l2Q51 2 870672 [k633,k502],l2Q43 2 890162 [k238,k634],l2Q47 2 889170 [k273,k635],l2Q43 2 886066 [k238,k636],l2Q47 2 886098 [k273,k637],l2Q43 2 885042 [k238,k638],l2Q20 1 528 [k639],l2Q30 2 311568 [k310,k481],l2Q8 1 834 [k640],l2Q45 2 312592 [k343,k505],l2Q30 2 327952 [k310,k482],l2Q25 1 579 [k641],l2Q45 2 328976 [k343,k506],l2Q28 1 545 [k642],l2Q9 1 578 [k643],l2Q21 1 784 [k644],l2Q21 1 816 [k645],l2Q18 1 561 [k646],l2Q18 1 817 [k647],l2Q9 1 834 [k648],l2Q21 1 321 [k629],l2Q35 2 313616 [k462,k489],l2Q40 1 289 [k649],l2Q51 2 279122 [k509,k633],l2Q46 3 392514882 [k354,k262,k650],l2Q44 3 392513808 [k443,k325,k651],l2Q14 1 545 [k652],l2Q30 1 578 [k653],l2Q28 1 784 [k654],l2Q45 2 313616 [k343,k305],l2Q45 2 330000 [k343,k306],l2Q24 1 561 [k655]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB20 : Array LCR := #[l2Q9 2 279106 [k643,k37],l2Q24 2 312848 [k613,k313],l2Q21 2 330256 [k467,k149],l2Q10 1 576 [k656],l2Q10 1 49 [k657],l2Q9 2 312592 [k37,k302],l2Q18 2 330273 [k449,k106],l2Q21 2 330512 [k644,k149],l2Q9 2 854288 [k37,k648],l2Q10 1 67 [k658],l2Q40 1 577 [k659],l2Q26 1 801 [k660],l2Q51 3 354715218 [k509,k369,k320],l2Q43 3 923060496 [k264,k238,k638],l2Q43 3 911561010 [k238,k463,k634],l2Q43 3 924109072 [k264,k238,k636],l2Q47 3 923093264 [k288,k273,k600],l2Q14 1 784 [k661],l2Q28 1 544 [k662],l2Q28 1 800 [k663],l2Q8 1 544 [k664],l2Q20 2 295474 [k515,k153],l2Q21 1 578 [k665],l2Q18 2 312898 [k543,k133],l2Q24 1 817 [k666],l2Q5 2 312592 [k22,k528],l2Q9 2 327952 [k37,k546],l2Q18 2 330289 [k646,k106],l2Q5 2 330017 [k212,k469],l2Q21 2 313121 [k488,k107],l2Q18 2 330545 [k647,k106],l2Q8 1 32 [k667]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB21 : Array LCR := #[l2Q21 1 834 [k668],l2Q18 2 854321 [k133,k548],l2Q5 1 576 [k669],l2Q8 2 871696 [k61,k670],l2Q10 2 870672 [k87,k671],l2Q40 1 834 [k672],l2Q36 1 850 [k673],l2Q51 3 354749010 [k509,k347,k320],l2Q39 3 386238801 [k207,k208,k674],l2Q43 2 360754 [k238,k675],l2Q46 3 386239826 [k321,k322,k676],l2Q36 3 386239826 [k188,k189,k677],l2Q43 2 361778 [k238,k678],l2Q43 2 365874 [k238,k679],l2Q51 2 870723 [k680,k502],l2Q51 1 272 [k633],l2Q39 3 386762066 [k332,k333,k681],l2Q46 3 386763091 [k262,k263,k682],l2Q36 3 386763091 [k292,k293,k683],l2Q57 1 289 [k684],l2Q20 2 295472 [k611,k153],l2Q20 2 311840 [k599,k154],l2Q20 2 296720 [k330,k121],l2Q20 2 803361 [k331,k330],l2Q25 1 832 [k685],l2Q20 2 312113 [k323,k154],l2Q28 2 331584 [k335,k172],l2Q25 1 816 [k686],l2Q28 2 279104 [k598,k209],l2Q25 1 834 [k687],l2Q13 1 817 [k688],l2Q28 2 279107 [k577,k209]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB22 : Array LCR := #[l2Q28 2 331536 [k654,k172],l2Q17 1 801 [k689],l2Q21 2 312898 [k665,k107],l2Q10 1 65 [k690],l2Q10 1 48 [k691],l2Q10 1 561 [k692],l2Q23 2 819472 [k254,k453],l2Q10 2 328976 [k87,k530],l2Q8 2 328976 [k61,k471],l2Q10 2 327952 [k87,k397],l2Q21 2 330289 [k584,k149],l2Q10 2 330032 [k120,k46],l2Q21 2 330545 [k585,k149],l2Q21 2 854321 [k107,k668],l2Q9 1 817 [k693],l2Q38 1 528 [k694],l2Q38 1 784 [k695],l2Q36 1 594 [k696],l2Q36 3 389368402 [k696,k188,k189],l2Q51 3 355289682 [k509,k502,k320],l2Q36 3 389367890 [k697,k188,k189],l2Q51 2 346384 [k633,k320],l2Q51 2 346640 [k698,k320],l2Q51 2 346896 [k699,k320],l2Q47 3 910512466 [k273,k521,k635],l2Q47 3 927287619 [k398,k273,k635],l2Q47 3 924141905 [k520,k273,k637],l2Q47 3 924141840 [k288,k273,k637],l2Q10 2 313616 [k87,k178],l2Q43 3 321702160 [k264,k475,k238],l2Q47 1 340 [k521],l2Q47 1 337 [k520]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB23 : Array LCR := #[l2Q30 1 562 [k700],l2Q28 2 345376 [k214,k401],l2Q45 1 562 [k701],l2Q45 1 578 [k702],l2Q45 1 835 [k703],l2Q20 2 295713 [k561,k153],l2Q20 2 296736 [k580,k121],l2Q20 2 295440 [k639,k153],l2Q28 2 279088 [k607,k209],l2Q30 1 835 [k704],l2Q28 2 331570 [k524,k172],l2Q20 2 296497 [k493,k121],l2Q20 2 312865 [k331,k86],l2Q25 1 800 [k705],l2Q45 1 579 [k706],l2Q20 2 313136 [k525,k86],l2Q28 2 328515 [k336,k181],l2Q28 3 336399632 [k209,k336,k181],l2Q28 2 296512 [k598,k210],l2Q28 2 328225 [k642,k181],l2Q28 2 852257 [k210,k335],l2Q20 2 311824 [k639,k154],l2Q25 1 544 [k707],l2Q30 1 579 [k708],l2Q28 2 854288 [k209,k514],l2Q20 2 313104 [k330,k86],l2Q28 2 296514 [k340,k210],l2Q25 1 576 [k709],l2Q25 1 578 [k710],l2Q28 2 855312 [k209,k336],l2Q20 2 314144 [k580,k152],l2Q20 2 314161 [k323,k152]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB24 : Array LCR := #[l2Q20 2 314145 [k561,k152],l2Q32 1 16 [k711],l2Q20 2 279073 [k331,k144],l2Q20 2 312114 [k492,k154],l2Q20 2 279089 [k493,k144],l2Q20 2 296498 [k515,k121],l2Q28 2 870672 [k209,k712],l2Q28 2 608528 [k209,k713],l2Q28 2 606497 [k210,k714],l2Q28 2 868641 [k210,k715],l2Q17 2 296464 [k484,k215],l2Q10 1 64 [k716],l2Q10 1 33 [k717],l2Q18 1 784 [k718],l2Q13 2 820496 [k165,k452],l2Q9 2 328976 [k37,k549],l2Q5 2 328976 [k22,k550],l2Q9 2 311568 [k37,k567],l2Q5 2 311568 [k22,k529],l2Q18 2 313632 [k122,k620],l2Q9 2 313632 [k274,k342],l2Q10 2 331056 [k120,k353],l2Q10 1 16 [k719],l2Q18 2 312624 [k380,k133],l2Q5 2 313648 [k529,k31],l2Q9 1 561 [k720],l2Q8 1 33 [k721],l2Q8 1 50 [k722],l2Q23 1 816 [k723],l2Q21 2 330048 [k428,k149],l2Q9 2 330049 [k549,k47],l2Q10 1 50 [k724]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB25 : Array LCR := #[l2Q10 1 66 [k725],l2Q5 1 834 [k726],l2Q9 1 818 [k727],l2Q8 2 869699 [k48,k728],l2Q10 2 868674 [k46,k729],l2Q40 2 329009 [k508,k632],l2Q40 2 328976 [k327,k632],l2Q30 1 834 [k730],l2Q36 2 626002 [k188,k731],l2Q44 4 345599478097 [k245,k246,k408,k424],l2Q39 4 345599478097 [k207,k208,k329,k392],l2Q46 4 346673220946 [k321,k322,k350,k354],l2Q28 2 330306 [k340,k132],l2Q44 4 292986128721 [k245,k246,k408,k443],l2Q38 2 329281 [k366,k200],l2Q46 4 311239740754 [k321,k322,k350,k362],l2Q36 4 311239740754 [k188,k189,k312,k351],l2Q46 3 927305042 [k321,k322,k732],l2Q51 2 346964 [k733,k320],l2Q51 2 346961 [k734,k320],l2Q51 2 885074 [k320,k735],l2Q46 4 964606397778 [k321,k322,k676,k736],l2Q44 3 386238801 [k245,k246,k651],l2Q46 3 387288402 [k321,k322,k605],l2Q36 3 387288402 [k188,k189,k559],l2Q44 3 390433105 [k245,k246,k603],l2Q39 3 390433105 [k207,k208,k556],l2Q46 3 390434130 [k321,k322,k650],l2Q33 2 331041 [k164,k737],l2Q36 3 389368080 [k391,k188,k189],l2Q36 1 595 [k738],l2Q43 2 363858 [k399,k679]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB26 : Array LCR := #[l2Q36 2 624979 [k292,k739],l2Q51 2 890178 [k347,k740],l2Q51 2 888658 [k502,k741],l2Q51 2 885586 [k502,k742],l2Q51 2 870992 [k743,k502],l2Q51 1 323 [k680],l2Q38 1 833 [k744],l2Q43 2 363809 [k400,k678],l2Q51 2 890145 [k369,k745],l2Q39 1 849 [k746],l2Q57 1 801 [k747],l2Q37 1 817 [k748],l2Q28 2 295474 [k523,k214],l2Q28 2 314144 [k663,k180],l2Q28 2 295490 [k340,k214],l2Q28 2 330528 [k663,k132],l2Q28 2 295472 [k607,k214],l2Q28 2 311840 [k662,k190],l2Q28 2 295488 [k598,k214],l2Q28 2 328224 [k662,k181],l2Q45 1 561 [k749],l2Q28 2 311875 [k577,k190],l2Q28 2 331568 [k597,k172],l2Q28 3 319046211 [k577,k209,k190],l2Q28 2 296496 [k607,k210],l2Q28 2 311841 [k642,k190],l2Q28 2 835873 [k210,k597],l2Q20 2 541216 [k599,k639],l2Q30 1 560 [k750],l2Q28 2 313923 [k577,k180],l2Q28 3 321160771 [k577,k210,k180],l2Q28 2 314128 [k654,k180]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB27 : Array LCR := #[l2Q28 2 575760 [k209,k523],l2Q28 2 837904 [k209,k524],l2Q28 2 296498 [k523,k210],l2Q45 1 577 [k751],l2Q20 2 541232 [k611,k639],l2Q30 1 576 [k752],l2Q28 2 330563 [k336,k132],l2Q28 2 331586 [k514,k172],l2Q28 3 338496801 [k210,k336,k132],l2Q28 2 279106 [k340,k209],l2Q28 2 330512 [k654,k132],l2Q25 1 66 [k753],l2Q28 2 83267 [k172,k754],l2Q25 1 64 [k755],l2Q14 1 817 [k756],l2Q25 2 869699 [k275,k757],l2Q20 2 314160 [k525,k152],l2Q28 2 296515 [k577,k210],l2Q28 2 331297 [k642,k172],l2Q28 2 855329 [k210,k336],l2Q20 2 279072 [k599,k144],l2Q20 2 313138 [k492,k86],l2Q20 2 279088 [k611,k144],l2Q10 1 32 [k758],l2Q10 1 544 [k759],l2Q21 1 800 [k760],l2Q18 1 816 [k761],l2Q21 1 832 [k762],l2Q8 2 576067 [k394,k231],l2Q21 2 328976 [k150,k629],l2Q10 2 838210 [k341,k108],l2Q8 1 16 [k763]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB28 : Array LCR := #[l2Q8 1 48 [k764],l2Q21 1 835 [k765],l2Q10 1 800 [k766],l2Q9 1 562 [k767],l2Q9 1 835 [k768],l2Q18 1 579 [k769],l2Q5 1 579 [k770],l2Q8 1 577 [k771],l2Q5 1 577 [k772],l2Q5 1 64 [k773],l2Q5 1 65 [k774],l2Q5 1 66 [k775],l2Q9 1 48 [k776],l2Q9 1 49 [k777],l2Q9 1 560 [k778],l2Q21 2 869698 [k149,k779],l2Q18 2 870705 [k133,k780],l2Q28 1 32 [k781],l2Q28 1 33 [k782],l2Q28 1 50 [k783],l2Q28 1 66 [k784],l2Q20 2 329777 [k294,k785],l2Q20 2 327729 [k294,k786],l2Q28 1 577 [k787],l2Q28 1 64 [k788],l2Q28 1 65 [k789],l2Q28 1 67 [k790],l2Q5 2 279104 [k669,k22],l2Q40 1 578 [k791],l2Q38 2 328208 [k694,k368],l2Q28 2 330273 [k642,k132],l2Q28 2 610593 [k210,k792]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB29 : Array LCR := #[l2Q28 2 854305 [k210,k514],l2Q28 2 348449 [k210,k793],l2Q20 2 820786 [k515,k561],l2Q40 2 327952 [k327,k794],l2Q36 4 415892801106 [k696,k351,k188,k189],l2Q50 1 577 [k795],l2Q39 3 388318289 [k796,k207,k208],l2Q36 3 389368658 [k673,k188,k189],l2Q36 3 657803553 [k351,k188,k731],l2Q20 2 312881 [k493,k86],l2Q51 2 541266 [k509,k698],l2Q51 2 870928 [k698,k502],l2Q36 3 389368336 [k552,k188,k189],l2Q51 2 803410 [k509,k699],l2Q51 2 871184 [k699,k502],l2Q36 3 389368592 [k553,k188,k189],l2Q51 3 118835472 [k633,k320,k797],l2Q51 2 622930 [k320,k798],l2Q51 2 623954 [k320,k799],l2Q51 2 98642 [k320,k800],l2Q51 2 99666 [k320,k797],l2Q51 2 346690 [k801,k320],l2Q51 3 356862804 [k733,k320,k802],l2Q51 3 105206098 [k320,k802,k803],l2Q51 2 348498 [k320,k802],l2Q51 2 364882 [k320,k348],l2Q51 3 120932675 [k680,k320,k804],l2Q51 3 121981251 [k680,k320,k803],l2Q51 2 346145 [k805,k320],l2Q36 3 924159314 [k188,k189,k806],l2Q51 2 346193 [k807,k320],l2Q51 2 346913 [k808,k320]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB30 : Array LCR := #[l2Q51 2 361810 [k320,k370],l2Q51 3 118835537 [k809,k320,k797],l2Q51 2 346449 [k809,k320],l2Q51 3 354764625 [k734,k809,k320],l2Q51 3 117786896 [k633,k320,k800],l2Q51 3 923093264 [k633,k320,k735],l2Q51 2 346144 [k810,k320],l2Q51 2 346192 [k811,k320],l2Q51 2 346912 [k812,k320],l2Q51 2 346960 [k813,k320],l2Q51 2 360786 [k320,k814],l2Q47 2 622930 [k273,k815],l2Q51 2 886098 [k320,k816],l2Q51 2 889170 [k320,k817],l2Q51 2 346947 [k818,k320],l2Q51 2 345938 [k502,k809],l2Q43 3 118802704 [k264,k238,k819],l2Q51 3 354240784 [k633,k502,k809],l2Q28 3 337970448 [k209,k820,k132],l2Q51 2 349010 [k502,k802],l2Q51 3 357386563 [k680,k502,k802],l2Q38 3 339019058 [k361,k200,k821],l2Q51 2 331346 [k509,k680],l2Q51 2 346691 [k822,k320],l2Q38 2 329010 [k361,k200],l2Q20 2 313137 [k323,k86],l2Q51 3 891568722 [k509,k633,k502],l2Q51 3 355289872 [k699,k502,k320],l2Q38 2 329537 [k744,k200],l2Q36 2 296530 [k696,k351],l2Q36 2 98610 [k311,k823],l2Q36 2 99634 [k311,k824]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB31 : Array LCR := #[l2Q36 2 102706 [k311,k825],l2Q36 2 313938 [k696,k311],l2Q36 2 622898 [k311,k826],l2Q36 2 623922 [k311,k827],l2Q36 2 313426 [k697,k311],l2Q36 2 103730 [k311,k828],l2Q36 2 626994 [k311,k829],l2Q36 1 818 [k830],l2Q36 2 628018 [k311,k831],l2Q36 3 391433010 [k830,k311,k189],l2Q51 2 628018 [k832,k741],l2Q51 2 887635 [k833,k741],l2Q51 2 628000 [k834,k742],l2Q51 2 887632 [k813,k742],l2Q51 2 870432 [k810,k502],l2Q51 2 870482 [k835,k502],l2Q51 2 871200 [k812,k502],l2Q51 2 361298 [k502,k836],l2Q51 2 344914 [k502,k837],l2Q51 2 870995 [k838,k502],l2Q51 2 870962 [k839,k502],l2Q51 2 364370 [k502,k840],l2Q51 2 347986 [k502,k841],l2Q51 1 595 [k838],l2Q47 2 362835 [k842,k576],l2Q51 1 339 [k841],l2Q51 2 871235 [k818,k502],l2Q51 2 346435 [k680,k320],l2Q36 2 622931 [k292,k843],l2Q36 2 623955 [k292,k844],l2Q36 2 627027 [k292,k845],l2Q36 2 98643 [k292,k846]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2RuleB32 : Array LCR := #[l2Q36 2 99667 [k292,k847],l2Q36 2 347218 [k697,k292],l2Q36 2 100691 [k292,k848],l2Q36 2 102739 [k292,k849],l2Q36 2 347986 [k673,k292],l2Q36 3 388320851 [k738,k292,k189],l2Q36 2 296531 [k738,k351],l2Q36 2 347681 [k850,k292],l2Q36 3 660950305 [k351,k292,k851],l2Q36 3 929385761 [k351,k292,k852],l2Q36 1 545 [k850],l2Q36 2 890145 [k351,k853],l2Q36 2 628001 [k351,k854]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Rule (i : ℕ) : LCR :=
  let bloc := (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then l2RuleB0 else l2RuleB1) else (if i < 96 then l2RuleB2 else l2RuleB3)) else (if i < 192 then (if i < 160 then l2RuleB4 else l2RuleB5) else (if i < 224 then l2RuleB6 else l2RuleB7))) else (if i < 384 then (if i < 320 then (if i < 288 then l2RuleB8 else l2RuleB9) else (if i < 352 then l2RuleB10 else l2RuleB11)) else (if i < 448 then (if i < 416 then l2RuleB12 else l2RuleB13) else (if i < 480 then l2RuleB14 else l2RuleB15)))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then l2RuleB16 else l2RuleB17) else (if i < 608 then l2RuleB18 else l2RuleB19)) else (if i < 704 then (if i < 672 then l2RuleB20 else l2RuleB21) else (if i < 736 then l2RuleB22 else l2RuleB23))) else (if i < 896 then (if i < 832 then (if i < 800 then l2RuleB24 else l2RuleB25) else (if i < 864 then l2RuleB26 else l2RuleB27)) else (if i < 960 then (if i < 928 then l2RuleB28 else l2RuleB29) else (if i < 992 then l2RuleB30 else (if i < 1024 then l2RuleB31 else l2RuleB32))))))
  bloc.getD (i % 32) lcVide
abbrev lcInterval (P : ℕ → Bool) (a n : ℕ) := ∀ j : Fin n, P (a+j.val)=true
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem lcJoin {P a n k} (g : lcInterval P a n) (d : lcInterval P (a+n) k) : lcInterval P a (n+k) := by
  intro j
  by_cases h : j.val<n
  · exact g ⟨j.val,h⟩
  · have H := d ⟨j.val-n,by omega⟩
    simpa only [show a+n+(j.val-n)=a+j.val by omega] using H
def lcRule (i : ℕ) := (l2Rule i).val.1
theorem lcR0 : lcInterval lcRule 0 16 := by decide +kernel
theorem lcR16 : lcInterval lcRule 16 16 := by decide +kernel
theorem lcR32 : lcInterval lcRule 32 16 := by decide +kernel
theorem lcR48 : lcInterval lcRule 48 16 := by decide +kernel
theorem lcR64 : lcInterval lcRule 64 16 := by decide +kernel
theorem lcR80 : lcInterval lcRule 80 16 := by decide +kernel
theorem lcR96 : lcInterval lcRule 96 16 := by decide +kernel
theorem lcR112 : lcInterval lcRule 112 16 := by decide +kernel
theorem lcR128 : lcInterval lcRule 128 16 := by decide +kernel
theorem lcR144 : lcInterval lcRule 144 16 := by decide +kernel
theorem lcR160 : lcInterval lcRule 160 16 := by decide +kernel
theorem lcR176 : lcInterval lcRule 176 16 := by decide +kernel
theorem lcR192 : lcInterval lcRule 192 16 := by decide +kernel
theorem lcR208 : lcInterval lcRule 208 16 := by decide +kernel
theorem lcR224 : lcInterval lcRule 224 16 := by decide +kernel
theorem lcR240 : lcInterval lcRule 240 16 := by decide +kernel
theorem lcR256 : lcInterval lcRule 256 16 := by decide +kernel
theorem lcR272 : lcInterval lcRule 272 16 := by decide +kernel
theorem lcR288 : lcInterval lcRule 288 16 := by decide +kernel
theorem lcR304 : lcInterval lcRule 304 16 := by decide +kernel
theorem lcR320 : lcInterval lcRule 320 16 := by decide +kernel
theorem lcR336 : lcInterval lcRule 336 16 := by decide +kernel
theorem lcR352 : lcInterval lcRule 352 16 := by decide +kernel
theorem lcR368 : lcInterval lcRule 368 16 := by decide +kernel
theorem lcR384 : lcInterval lcRule 384 16 := by decide +kernel
theorem lcR400 : lcInterval lcRule 400 16 := by decide +kernel
theorem lcR416 : lcInterval lcRule 416 16 := by decide +kernel
theorem lcR432 : lcInterval lcRule 432 16 := by decide +kernel
theorem lcR448 : lcInterval lcRule 448 16 := by decide +kernel
theorem lcR464 : lcInterval lcRule 464 16 := by decide +kernel
theorem lcR480 : lcInterval lcRule 480 16 := by decide +kernel
theorem lcR496 : lcInterval lcRule 496 16 := by decide +kernel
theorem lcR512 : lcInterval lcRule 512 16 := by decide +kernel
theorem lcR528 : lcInterval lcRule 528 16 := by decide +kernel
theorem lcR544 : lcInterval lcRule 544 16 := by decide +kernel
theorem lcR560 : lcInterval lcRule 560 16 := by decide +kernel
theorem lcR576 : lcInterval lcRule 576 16 := by decide +kernel
theorem lcR592 : lcInterval lcRule 592 16 := by decide +kernel
theorem lcR608 : lcInterval lcRule 608 16 := by decide +kernel
theorem lcR624 : lcInterval lcRule 624 16 := by decide +kernel
theorem lcR640 : lcInterval lcRule 640 16 := by decide +kernel
theorem lcR656 : lcInterval lcRule 656 16 := by decide +kernel
theorem lcR672 : lcInterval lcRule 672 16 := by decide +kernel
theorem lcR688 : lcInterval lcRule 688 16 := by decide +kernel
theorem lcR704 : lcInterval lcRule 704 16 := by decide +kernel
theorem lcR720 : lcInterval lcRule 720 16 := by decide +kernel
theorem lcR736 : lcInterval lcRule 736 16 := by decide +kernel
theorem lcR752 : lcInterval lcRule 752 16 := by decide +kernel
theorem lcR768 : lcInterval lcRule 768 16 := by decide +kernel
theorem lcR784 : lcInterval lcRule 784 16 := by decide +kernel
theorem lcR800 : lcInterval lcRule 800 16 := by decide +kernel
theorem lcR816 : lcInterval lcRule 816 16 := by decide +kernel
theorem lcR832 : lcInterval lcRule 832 16 := by decide +kernel
theorem lcR848 : lcInterval lcRule 848 16 := by decide +kernel
theorem lcR864 : lcInterval lcRule 864 16 := by decide +kernel
theorem lcR880 : lcInterval lcRule 880 16 := by decide +kernel
theorem lcR896 : lcInterval lcRule 896 16 := by decide +kernel
theorem lcR912 : lcInterval lcRule 912 16 := by decide +kernel
theorem lcR928 : lcInterval lcRule 928 16 := by decide +kernel
theorem lcR944 : lcInterval lcRule 944 16 := by decide +kernel
theorem lcR960 : lcInterval lcRule 960 16 := by decide +kernel
theorem lcR976 : lcInterval lcRule 976 16 := by decide +kernel
theorem lcR992 : lcInterval lcRule 992 16 := by decide +kernel
theorem lcR1008 : lcInterval lcRule 1008 16 := by decide +kernel
theorem lcR1024 : lcInterval lcRule 1024 13 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem lcTout : lcInterval lcRule 0 1037 := (lcJoin (a:=0) (n:=512) (k:=525) (lcJoin (a:=0) (n:=256) (k:=256) (lcJoin (a:=0) (n:=128) (k:=128) (lcJoin (a:=0) (n:=64) (k:=64) (lcJoin (a:=0) (n:=32) (k:=32) (lcJoin (a:=0) (n:=16) (k:=16) lcR0 lcR16) (lcJoin (a:=32) (n:=16) (k:=16) lcR32 lcR48)) (lcJoin (a:=64) (n:=32) (k:=32) (lcJoin (a:=64) (n:=16) (k:=16) lcR64 lcR80) (lcJoin (a:=96) (n:=16) (k:=16) lcR96 lcR112))) (lcJoin (a:=128) (n:=64) (k:=64) (lcJoin (a:=128) (n:=32) (k:=32) (lcJoin (a:=128) (n:=16) (k:=16) lcR128 lcR144) (lcJoin (a:=160) (n:=16) (k:=16) lcR160 lcR176)) (lcJoin (a:=192) (n:=32) (k:=32) (lcJoin (a:=192) (n:=16) (k:=16) lcR192 lcR208) (lcJoin (a:=224) (n:=16) (k:=16) lcR224 lcR240)))) (lcJoin (a:=256) (n:=128) (k:=128) (lcJoin (a:=256) (n:=64) (k:=64) (lcJoin (a:=256) (n:=32) (k:=32) (lcJoin (a:=256) (n:=16) (k:=16) lcR256 lcR272) (lcJoin (a:=288) (n:=16) (k:=16) lcR288 lcR304)) (lcJoin (a:=320) (n:=32) (k:=32) (lcJoin (a:=320) (n:=16) (k:=16) lcR320 lcR336) (lcJoin (a:=352) (n:=16) (k:=16) lcR352 lcR368))) (lcJoin (a:=384) (n:=64) (k:=64) (lcJoin (a:=384) (n:=32) (k:=32) (lcJoin (a:=384) (n:=16) (k:=16) lcR384 lcR400) (lcJoin (a:=416) (n:=16) (k:=16) lcR416 lcR432)) (lcJoin (a:=448) (n:=32) (k:=32) (lcJoin (a:=448) (n:=16) (k:=16) lcR448 lcR464) (lcJoin (a:=480) (n:=16) (k:=16) lcR480 lcR496))))) (lcJoin (a:=512) (n:=256) (k:=269) (lcJoin (a:=512) (n:=128) (k:=128) (lcJoin (a:=512) (n:=64) (k:=64) (lcJoin (a:=512) (n:=32) (k:=32) (lcJoin (a:=512) (n:=16) (k:=16) lcR512 lcR528) (lcJoin (a:=544) (n:=16) (k:=16) lcR544 lcR560)) (lcJoin (a:=576) (n:=32) (k:=32) (lcJoin (a:=576) (n:=16) (k:=16) lcR576 lcR592) (lcJoin (a:=608) (n:=16) (k:=16) lcR608 lcR624))) (lcJoin (a:=640) (n:=64) (k:=64) (lcJoin (a:=640) (n:=32) (k:=32) (lcJoin (a:=640) (n:=16) (k:=16) lcR640 lcR656) (lcJoin (a:=672) (n:=16) (k:=16) lcR672 lcR688)) (lcJoin (a:=704) (n:=32) (k:=32) (lcJoin (a:=704) (n:=16) (k:=16) lcR704 lcR720) (lcJoin (a:=736) (n:=16) (k:=16) lcR736 lcR752)))) (lcJoin (a:=768) (n:=128) (k:=141) (lcJoin (a:=768) (n:=64) (k:=64) (lcJoin (a:=768) (n:=32) (k:=32) (lcJoin (a:=768) (n:=16) (k:=16) lcR768 lcR784) (lcJoin (a:=800) (n:=16) (k:=16) lcR800 lcR816)) (lcJoin (a:=832) (n:=32) (k:=32) (lcJoin (a:=832) (n:=16) (k:=16) lcR832 lcR848) (lcJoin (a:=864) (n:=16) (k:=16) lcR864 lcR880))) (lcJoin (a:=896) (n:=64) (k:=77) (lcJoin (a:=896) (n:=32) (k:=32) (lcJoin (a:=896) (n:=16) (k:=16) lcR896 lcR912) (lcJoin (a:=928) (n:=16) (k:=16) lcR928 lcR944)) (lcJoin (a:=960) (n:=32) (k:=45) (lcJoin (a:=960) (n:=16) (k:=16) lcR960 lcR976) (lcJoin (a:=992) (n:=16) (k:=29) lcR992 (lcJoin (a:=1008) (n:=16) (k:=13) lcR1008 lcR1024)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2Rules (i : Fin 1037) : (l2Rule i.val).val.1=true := by
  simpa only [Nat.zero_add,lcRule] using lcTout i
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Leaf (get : ℕ → L2Cell) (i s f code : ℕ) (v : List ℕ) :=
  if code = 0 then vitesseZero f v
  else if code < 1037 then (l2Rule code).val.2 s f v
  else
    let j := code-1037
    let c := get j
    j < i && c.s≤s && (if c.wide then
      c.s < 127 && cutTest f c.f (normaliser c.s) c.av v []
    else c.f = f && v.all (fun w => c.av.contains w) && c.av.all v.contains)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2LeafOK {get : ℕ → L2Cell} {i s f code v} (before : ∀ j < i, (get j).claim) (ih : l2IH s)
    (nd : List.Nodup v) (h : l2Leaf get i s f code v = true) : Ban 208 f v := by
  unfold l2Leaf at h
  split at h
  · exact vitesseZero_ok h nd
  split at h
  · exact (l2Rule code).property s f v (l2Rules ⟨code,by assumption⟩) ih nd h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨lt,le⟩,ok⟩ := h
  have H := before _ lt (fun t ht hp => ih t (lt_of_lt_of_le ht le) hp)
  split at ok <;> rename_i flag
  · simp only [flag,ite_true] at H
    simp only [Bool.and_eq_true,decide_eq_true_eq] at ok
    exact cutTest_ok (l2Proj _ ok.1) H nd ok.2
  · simp [flag] at H
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem] at ok
    obtain ⟨⟨eq,sub⟩,rev⟩ := ok
    have e : v.toFinset=(get (code-1037)).av.toFinset := by ext x; simp only [List.mem_toFinset]; exact ⟨sub x,rev x⟩
    simpa only [Ban,eq,←e] using H

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Walk (get : ℕ → L2Cell) (i s f : ℕ) : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | v::vs, n =>
    l2Leaf get i s f (n &&& 4095) v && l2Walk get i s f vs (n >>> 12)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2WalkOK {get : ℕ → L2Cell} {i s f vs n} (before : ∀ j < i, (get j).claim) (ih : l2IH s)
    (h : l2Walk get i s f vs n = true) : ∀ v∈vs, v.Nodup → Ban 208 f v := by
  induction vs generalizing n with
  | nil => simp
  | cons a vs rec =>
    simp only [l2Walk,Bool.and_eq_true] at h
    intro v hv nd
    rcases List.mem_cons.mp hv with rfl|hx
    · exact l2LeafOK before ih nd h.1
    · exact rec h.2 _ hx nd

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Check (get : ℕ → L2Cell) (i : ℕ) :=
  let c := get i
  decide c.av.Nodup &&
    (if c.wide then l2Walk get i c.s c.f (l2Subs c.f c.av) c.tape
    else 0<c.f && !(terminal 208 c.av) && l2Walk get i c.s (c.f-1) (l2Children 208 (c.f-1) c.av) c.tape)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2CheckOK {get : ℕ → L2Cell} {i} (before : ∀ j < i, (get j).claim) (h : l2Check get i = true) : (get i).claim := by
  intro ih
  simp only [l2Check,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨nd,h⟩ := h
  split at h <;> rename_i flag
  · simp only [flag,ite_true]; exact l2Wide nd (l2WalkOK before ih h)
  · simp [flag]; simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
    obtain ⟨⟨pos,no⟩,kids⟩ := h
    have B := l2Branch nd no (l2WalkOK before ih kids)
    simpa only [Nat.sub_add_cancel pos] using B

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Scatter : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, w => (w &&& 1) ||| (l2Scatter k (w >>> 1) <<< 16)

def l2Expand (s w : ℕ) := normaliser s ((l2Scatter 13 w * 65535) |||
  (((w >>> 13) * ((2^208-1)/65535)) <<< 208))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Unpack (get : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k+1, w => if w=0 then [] else get (w &&& 2047) :: l2Unpack get k (w >>> 11)

abbrev l2Span (get : ℕ → L2Cell) (a n : ℕ) := ∀ j : Fin n, l2Check get (a+j.val)=true

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2SpanAdd {get a n k} (left : l2Span get a n) (right : l2Span get (a+n) k) : l2Span get a (n+k) := by
  intro j
  by_cases h : j.val<n
  · exact left ⟨j.val,h⟩
  · have H := right ⟨j.val-n,by omega⟩
    simpa only [show a+n+(j.val-n)=a+j.val by omega] using H

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2Global {get n} (span : l2Span get 0 n) (i : ℕ) (hi : i<n) : (get i).claim := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    apply l2CheckOK (fun j lt => ih j lt (lt_trans lt hi))
    simpa using span ⟨i,hi⟩

def l2Pl (m v : ℕ) := (l2Flat v &&& m) ||| ((2^208-1) ^^^ (m &&& (2^208-1)))
def w0 : ℕ := 0
def w1 : ℕ := l2Pl l2M0 131073
def w2 : ℕ := l2Pl l2M0 16385
def w3 : ℕ := l2Key l2M60 3670018
def w4 : ℕ := l2Pl l2M60 2490369
def w5 : ℕ := l2Key l2M60 360450
def w6 : ℕ := l2Pl l2M60 1130497
def w7 : ℕ := l2Pl l2M61 4194316
def w8 : ℕ := l2Key l2M61 98312
def w9 : ℕ := l2Pl l2M61 81924
def w10 : ℕ := l2Key l2M7 4194324
def w11 : ℕ := l2Pl l2M7 131089
def w12 : ℕ := l2Pl l2M7 16389
def w13 : ℕ := l2Key l2M14 4194332
def w14 : ℕ := l2Pl l2M14 393233
def w15 : ℕ := l2Key l2M14 360456
def w16 : ℕ := l2Pl l2M14 81925
def w17 : ℕ := l2Key l2M53 12582924
def w18 : ℕ := l2Pl l2M53 9961474
def w19 : ℕ := l2Pl l2M53 98314
def w20 : ℕ := l2Key l2M53 1130500
def w21 : ℕ := l2Key l2M25 12582940
def w22 : ℕ := l2Pl l2M25 12140551
def w23 : ℕ := l2Pl l2M25 2490385
def w24 : ℕ := l2Key l2M25 360458
def w25 : ℕ := l2Pl l2M25 1130501
def w26 : ℕ := l2Key l2M25 12058626
def w27 : ℕ := l2Pl l2M25 1425423
def w28 : ℕ := l2Pl l2M25 2588699
def w29 : ℕ := l2Pl l2M25 12451859
def w30 : ℕ := l2Key l2M25 16252958
def w31 : ℕ := l2Key l2M62 83886176
def w32 : ℕ := l2Pl l2M62 71303180
def w33 : ℕ := l2Key l2M62 98376
def w34 : ℕ := l2Pl l2M62 81956
def w35 : ℕ := l2Key l2M34 117440608
def w36 : ℕ := l2Key l2M34 71303196
def w37 : ℕ := l2Pl l2M34 33947665
def w38 : ℕ := l2Key l2M34 360520
def w39 : ℕ := l2Pl l2M34 81957
def w40 : ℕ := l2Pl l2M25 81925
def w41 : ℕ := l2Key l2M10 50331872
def w42 : ℕ := l2Pl l2M10 3752099
def w43 : ℕ := l2Key l2M10 3670146
def w44 : ℕ := l2Pl l2M10 36143171
def w45 : ℕ := l2Pl l2M10 36044801
def w46 : ℕ := l2Key l2M10 98370
def w47 : ℕ := l2Pl l2M10 1130529
def w48 : ℕ := l2Key l2M33 119931088
def w49 : ℕ := l2Key l2M33 83886272
def w50 : ℕ := l2Key l2M33 79691800
def w51 : ℕ := l2Pl l2M33 11010178
def w52 : ℕ := l2Pl l2M33 294986
def w53 : ℕ := l2Pl l2M33 82313370
def w54 : ℕ := l2Key l2M33 36044816
def w55 : ℕ := l2Pl l2M25 393233
def w56 : ℕ := l2Pl l2M10 37617795
def w57 : ℕ := l2Pl l2M10 1425507
def w58 : ℕ := l2Key l2M10 360514
def w59 : ℕ := l2Key l2M10 1572994
def w60 : ℕ := l2Key l2M43 117440736
def w61 : ℕ := l2Key l2M43 79691804
def w62 : ℕ := l2Pl l2M43 46006419
def w63 : ℕ := l2Key l2M43 12058754
def w64 : ℕ := l2Pl l2M43 36044817
def w65 : ℕ := l2Key l2M43 360522
def w66 : ℕ := l2Pl l2M43 1130533
def w67 : ℕ := l2Key l2M43 9961602
def w68 : ℕ := l2Pl l2M43 33947665
def w69 : ℕ := l2Pl l2M56 119668913
def w70 : ℕ := l2Key l2M56 83361940
def w71 : ℕ := l2Key l2M56 12058752
def w72 : ℕ := l2Pl l2M56 35782673
def w73 : ℕ := l2Pl l2M56 1064997
def w74 : ℕ := l2Key l2M56 117440672
def w75 : ℕ := l2Key l2M56 71303188
def w76 : ℕ := l2Key l2M15 134220544
def w77 : ℕ := l2Pl l2M15 4196364
def w78 : ℕ := l2Key l2M15 98824
def w79 : ℕ := l2Pl l2M15 82180
def w80 : ℕ := l2Key l2M20 134221056
def w81 : ℕ := l2Pl l2M20 4213013
def w82 : ℕ := l2Key l2M20 4196372
def w83 : ℕ := l2Pl l2M20 148757
def w84 : ℕ := l2Pl l2M20 132113
def w85 : ℕ := l2Pl l2M20 134237445
def w86 : ℕ := l2Pl l2M20 4328469
def w87 : ℕ := l2Pl l2M20 16645
def w88 : ℕ := l2Pl l2M20 134352145
def w89 : ℕ := l2Key l2M20 138415380
def w90 : ℕ := l2Key l2M28 134221568
def w91 : ℕ := l2Key l2M28 4196380
def w92 : ℕ := l2Pl l2M28 394257
def w93 : ℕ := l2Key l2M28 360968
def w94 : ℕ := l2Pl l2M28 82181
def w95 : ℕ := l2Pl l2M30 412617474
def w96 : ℕ := l2Key l2M30 402656000
def w97 : ℕ := l2Key l2M30 12584972
def w98 : ℕ := l2Pl l2M30 98826
def w99 : ℕ := l2Key l2M30 1130756
def w100 : ℕ := l2Pl l2M30 282593294
def w101 : ℕ := l2Pl l2M30 278396930
def w102 : ℕ := l2Pl l2M60 3653635
def w103 : ℕ := l2Pl l2M25 13713437
def w104 : ℕ := l2Pl l2M25 3620885
def w105 : ℕ := l2Key l2M36 402657024
def w106 : ℕ := l2Pl l2M36 284772639
def w107 : ℕ := l2Pl l2M36 13715741
def w108 : ℕ := l2Key l2M36 12584988
def w109 : ℕ := l2Pl l2M36 3622165
def w110 : ℕ := l2Pl l2M36 2491409
def w111 : ℕ := l2Key l2M36 360970
def w112 : ℕ := l2Key l2M36 280494082
def w113 : ℕ := l2Pl l2M25 15073309
def w114 : ℕ := l2Pl l2M36 414797575
def w115 : ℕ := l2Pl l2M36 403787525
def w116 : ℕ := l2Key l2M32 402655744
def w117 : ℕ := l2Key l2M32 12584968
def w118 : ℕ := l2Pl l2M32 33290
def w119 : ℕ := l2Key l2M32 33288
def w120 : ℕ := l2Key l2M6 134220288
def w121 : ℕ := l2Pl l2M6 4196360
def w122 : ℕ := l2Pl l2M6 33288
def w123 : ℕ := l2Key l2M6 33280
def w124 : ℕ := l2Pl l2M6 32776
def w125 : ℕ := l2Pl l2M36 3655455
def w126 : ℕ := l2Pl l2M36 1130757
def w127 : ℕ := l2Pl l2M36 285084703
def w128 : ℕ := l2Pl l2M36 15076381
def w129 : ℕ := l2Pl l2M36 415108883
def w130 : ℕ := l2Pl l2M36 405147409
def w131 : ℕ := l2Pl l2M30 412699398
def w132 : ℕ := l2Pl l2M30 282675470
def w133 : ℕ := l2Pl l2M30 278479110
def w134 : ℕ := l2Pl l2M7 4341781
def w135 : ℕ := l2Pl l2M28 4672797
def w136 : ℕ := l2Pl l2M1 134366465
def w137 : ℕ := l2Key l2M1 134219008
def w138 : ℕ := l2Pl l2M1 132097
def w139 : ℕ := l2Pl l2M1 16641
def w140 : ℕ := l2Pl l2M28 134696725
def w141 : ℕ := l2Pl l2M25 12533783
def w142 : ℕ := l2Pl l2M30 416811790
def w143 : ℕ := l2Key l2M36 418909982
def w144 : ℕ := l2Key l2M36 414715650
def w145 : ℕ := l2Key l2M8 402654976
def w146 : ℕ := l2Pl l2M8 272581891
def w147 : ℕ := l2Pl l2M8 2491393
def w148 : ℕ := l2Key l2M8 360962
def w149 : ℕ := l2Pl l2M8 1130753
def w150 : ℕ := l2Key l2M36 284690462
def w151 : ℕ := l2Key l2M20 138414080
def w152 : ℕ := l2Key l2M36 415239964
def w153 : ℕ := l2Pl l2M11 138430724
def w154 : ℕ := l2Key l2M11 134220032
def w155 : ℕ := l2Pl l2M11 4196356
def w156 : ℕ := l2Pl l2M11 16644
def w157 : ℕ := l2Pl l2M20 138431765
def w158 : ℕ := l2Pl l2M63 418925845
def w159 : ℕ := l2Key l2M63 402656512
def w160 : ℕ := l2Key l2M63 12584980
def w161 : ℕ := l2Pl l2M63 2229265
def w162 : ℕ := l2Pl l2M63 1065221
def w163 : ℕ := l2Pl l2M25 3751939
def w164 : ℕ := l2Pl l2M36 280576263
def w165 : ℕ := l2Pl l2M30 14239758
def w166 : ℕ := l2Pl l2M30 12683790
def w167 : ℕ := l2Pl l2M30 10043398
def w168 : ℕ := l2Pl l2M30 402754314
def w169 : ℕ := l2Pl l2M8 3751939
def w170 : ℕ := l2Pl l2M30 270090498
def w171 : ℕ := l2Pl l2M30 404310786
def w172 : ℕ := l2Pl l2M60 3751939
def w173 : ℕ := l2Pl l2M60 2588675
def w174 : ℕ := l2Key l2M60 1654786
def w175 : ℕ := l2Pl l2M28 134303493
def w176 : ℕ := l2Pl l2M28 4278557
def w177 : ℕ := l2Pl l2M28 493081
def w178 : ℕ := l2Key l2M30 13715724
def w179 : ℕ := l2Pl l2M30 1164046
def w180 : ℕ := l2Key l2M28 115468
def w181 : ℕ := l2Pl l2M8 1426179
def w182 : ℕ := l2Pl l2M8 377601
def w183 : ℕ := l2Pl l2M28 134598413
def w184 : ℕ := l2Pl l2M28 377613
def w185 : ℕ := l2Pl l2M8 272499715
def w186 : ℕ := l2Key l2M8 406324994
def w187 : ℕ := l2Pl l2M36 1426191
def w188 : ℕ := l2Pl l2M8 272187651
def w189 : ℕ := l2Pl l2M28 138497821
def w190 : ℕ := l2Pl l2M36 416370461
def w191 : ℕ := l2Pl l2M20 4210709
def w192 : ℕ := l2Pl l2M28 4276253
def w193 : ℕ := l2Pl l2M36 2590235
def w194 : ℕ := l2Key l2M45 402656768
def w195 : ℕ := l2Key l2M45 15076376
def w196 : ℕ := l2Key l2M45 12584984
def w197 : ℕ := l2Pl l2M45 279445506
def w198 : ℕ := l2Pl l2M45 2524698
def w199 : ℕ := l2Key l2M45 405147152
def w200 : ℕ := l2Pl l2M8 2590211
def w201 : ℕ := l2Pl l2M8 493057
def w202 : ℕ := l2Key l2M30 415238924
def w203 : ℕ := l2Pl l2M45 414060050
def w204 : ℕ := l2Key l2M45 2491408
def w205 : ℕ := l2Pl l2M45 295434
def w206 : ℕ := l2Pl l2M45 284036122
def w207 : ℕ := l2Pl l2M45 279839762
def w208 : ℕ := l2Pl l2M28 4590621
def w209 : ℕ := l2Pl l2M16 138546192
def w210 : ℕ := l2Key l2M16 134220800
def w211 : ℕ := l2Pl l2M16 4196368
def w212 : ℕ := l2Pl l2M16 132112
def w213 : ℕ := l2Pl l2M36 16207133
def w214 : ℕ := l2Key l2M20 4212996
def w215 : ℕ := l2Pl l2M8 405145345
def w216 : ℕ := l2Pl l2M8 403785473
def w217 : ℕ := l2Key l2M8 272105474
def w218 : ℕ := l2Pl l2M36 418991903
def w219 : ℕ := l2Key l2M36 282675470
def w220 : ℕ := l2Key l2M52 402654720
def w221 : ℕ := l2Key l2M52 2491392
def w222 : ℕ := l2Pl l2M52 295426
def w223 : ℕ := l2Pl l2M52 2621442
def w224 : ℕ := l2Key l2M30 403786500
def w225 : ℕ := l2Pl l2M25 376845
def w226 : ℕ := l2Pl l2M28 4573981
def w227 : ℕ := l2Pl l2M20 134235393
def w228 : ℕ := l2Pl l2M28 134301441
def w229 : ℕ := l2Pl l2M25 491545
def w230 : ℕ := l2Pl l2M28 134614801
def w231 : ℕ := l2Pl l2M36 406277909
def w232 : ℕ := l2Key l2M20 134236420
def w233 : ℕ := l2Key l2M36 412699398
def w234 : ℕ := l2Key l2M54 12582936
def w235 : ℕ := l2Key l2M54 2490384
def w236 : ℕ := l2Pl l2M54 294922
def w237 : ℕ := l2Pl l2M54 2621442
def w238 : ℕ := l2Pl l2M45 413666818
def w239 : ℕ := l2Pl l2M45 33290
def w240 : ℕ := l2Pl l2M45 283641882
def w241 : ℕ := l2Key l2M45 415239704
def w242 : ℕ := l2Key l2M45 2524696
def w243 : ℕ := l2Key l2M45 12880408
def w244 : ℕ := l2Key l2M45 402951688
def w245 : ℕ := l2Pl l2M64 12615690
def w246 : ℕ := l2Key l2M64 12582920
def w247 : ℕ := l2Key l2M64 32776
def w248 : ℕ := l2Pl l2M65 402686466
def w249 : ℕ := l2Key l2M65 402653696
def w250 : ℕ := l2Key l2M65 33280
def w251 : ℕ := l2Key l2M52 295424
def w252 : ℕ := l2Key l2M54 294920
def w253 : ℕ := l2Key l2M45 295432
def w254 : ℕ := l2Key l2M28 394256
def w255 : ℕ := l2Pl l2M28 509725
def w256 : ℕ := l2Pl l2M66 4587544
def w257 : ℕ := l2Pl l2M66 4489240
def w258 : ℕ := l2Key l2M66 393232
def w259 : ℕ := l2Pl l2M66 294920
def w260 : ℕ := l2Key l2M16 4196352
def w261 : ℕ := l2Key l2M28 138415900
def w262 : ℕ := l2Pl l2M67 134612480
def w263 : ℕ := l2Pl l2M67 134514176
def w264 : ℕ := l2Key l2M67 394240
def w265 : ℕ := l2Pl l2M67 295424
def w266 : ℕ := l2Key l2M16 134219776
def w267 : ℕ := l2Key l2M25 9961474
def w268 : ℕ := l2Key l2M25 3670018
def w269 : ℕ := l2Key l2M8 270008322
def w270 : ℕ := l2Key l2M8 3670018
def w271 : ℕ := l2Key l2M60 1163266
def w272 : ℕ := l2Pl l2M60 1425411
def w273 : ℕ := l2Pl l2M60 376833
def w274 : ℕ := l2Pl l2M60 4063235
def w275 : ℕ := l2Pl l2M30 33290
def w276 : ℕ := l2Key l2M28 427544
def w277 : ℕ := l2Pl l2M28 134713113
def w278 : ℕ := l2Pl l2M20 138546453
def w279 : ℕ := l2Pl l2M28 138809117
def w280 : ℕ := l2Pl l2M36 417730333
def w281 : ℕ := l2Pl l2M20 4325397
def w282 : ℕ := l2Pl l2M28 4587549
def w283 : ℕ := l2Key l2M20 132112
def w284 : ℕ := l2Pl l2M28 4689437
def w285 : ℕ := l2Pl l2M20 134350081
def w286 : ℕ := l2Pl l2M28 134612737
def w287 : ℕ := l2Key l2M29 402653952
def w288 : ℕ := l2Pl l2M29 98818
def w289 : ℕ := l2Key l2M29 98816
def w290 : ℕ := l2Key l2M29 1130752
def w291 : ℕ := l2Key l2M53 98312
def w292 : ℕ := l2Key l2M30 1164044
def w293 : ℕ := l2Key l2M30 12683788
def w294 : ℕ := l2Key l2M30 402754312
def w295 : ℕ := l2Key l2M30 98824
def w296 : ℕ := l2Key l2M28 82180
def w297 : ℕ := l2Pl l2M61 4292620
def w298 : ℕ := l2Pl l2M61 4276236
def w299 : ℕ := l2Key l2M11 4196352
def w300 : ℕ := l2Pl l2M68 134316800
def w301 : ℕ := l2Pl l2M68 134300416
def w302 : ℕ := l2Key l2M68 98816
def w303 : ℕ := l2Pl l2M68 82176
def w304 : ℕ := l2Key l2M11 134219776
def w305 : ℕ := l2Key l2M25 11010050
def w306 : ℕ := l2Key l2M8 271056898
def w307 : ℕ := l2Key l2M60 2523138
def w308 : ℕ := l2Pl l2M60 491521
def w309 : ℕ := l2Pl l2M63 419040533
def w310 : ℕ := l2Pl l2M25 4063235
def w311 : ℕ := l2Pl l2M36 280888339
def w312 : ℕ := l2Pl l2M45 15599642
def w313 : ℕ := l2Pl l2M45 12880410
def w314 : ℕ := l2Pl l2M45 11403282
def w315 : ℕ := l2Pl l2M45 402951690
def w316 : ℕ := l2Pl l2M8 4063235
def w317 : ℕ := l2Pl l2M45 271451138
def w318 : ℕ := l2Pl l2M45 405671426
def w319 : ℕ := l2Key l2M60 3014658
def w320 : ℕ := l2Key l2M20 4328464
def w321 : ℕ := l2Pl l2M36 419303199
def w322 : ℕ := l2Key l2M36 284036122
def w323 : ℕ := l2Pl l2M29 1572866
def w324 : ℕ := l2Key l2M20 134351888
def w325 : ℕ := l2Key l2M36 414060050
def w326 : ℕ := l2Pl l2M53 1572866
def w327 : ℕ := l2Key l2M63 413666304
def w328 : ℕ := l2Pl l2M63 3294485
def w329 : ℕ := l2Pl l2M63 13650197
def w330 : ℕ := l2Pl l2M63 14814229
def w331 : ℕ := l2Pl l2M20 134351889
def w332 : ℕ := l2Key l2M20 138415124
def w333 : ℕ := l2Key l2M63 412616960
def w334 : ℕ := l2Pl l2M20 134236421
def w335 : ℕ := l2Key l2M20 138414356
def w336 : ℕ := l2Pl l2M69 416811268
def w337 : ℕ := l2Key l2M69 402655488
def w338 : ℕ := l2Pl l2M69 12584964
def w339 : ℕ := l2Pl l2M69 1065220
def w340 : ℕ := l2Key l2M63 418909460
def w341 : ℕ := l2Pl l2M70 417860624
def w342 : ℕ := l2Key l2M70 402656256
def w343 : ℕ := l2Pl l2M70 12584976
def w344 : ℕ := l2Pl l2M70 2229264
def w345 : ℕ := l2Pl l2M63 403721477
def w346 : ℕ := l2Key l2M20 138415120
def w347 : ℕ := l2Pl l2M63 404884753
def w348 : ℕ := l2Key l2M20 138414340
def w349 : ℕ := l2Pl l2M45 417861146
def w350 : ℕ := l2Key l2M14 4194324
def w351 : ℕ := l2Key l2M63 406324480
def w352 : ℕ := l2Pl l2M20 134235397
def w353 : ℕ := l2Pl l2M20 134350097
def w354 : ℕ := l2Key l2M63 283641872
def w355 : ℕ := l2Pl l2M63 283773969
def w356 : ℕ := l2Key l2M63 417860880
def w357 : ℕ := l2Key l2M63 282593284
def w358 : ℕ := l2Pl l2M63 282609925
def w359 : ℕ := l2Key l2M63 416812292
def w360 : ℕ := l2Key l2M13 134219520
def w361 : ℕ := l2Key l2M13 134219008
def w362 : ℕ := l2Pl l2M13 394241
def w363 : ℕ := l2Pl l2M13 82177
def w364 : ℕ := l2Pl l2M63 16269589
def w365 : ℕ := l2Key l2M63 16252948
def w366 : ℕ := l2Pl l2M63 16385045
def w367 : ℕ := l2Key l2M7 4210692
def w368 : ℕ := l2Key l2M36 418909722
def w369 : ℕ := l2Key l2M36 415239704
def w370 : ℕ := l2Key l2M7 4325392
def w371 : ℕ := l2Key l2M36 418908942
def w372 : ℕ := l2Key l2M36 415238924
def w373 : ℕ := l2Key l2M8 405276162
def w374 : ℕ := l2Key l2M36 418909460
def w375 : ℕ := l2Key l2M8 404226818
def w376 : ℕ := l2Key l2M5 134223616
def w377 : ℕ := l2Key l2M5 50335840
def w378 : ℕ := l2Pl l2M5 33948673
def w379 : ℕ := l2Key l2M5 361024
def w380 : ℕ := l2Pl l2M5 82209
def w381 : ℕ := l2Key l2M19 134223104
def w382 : ℕ := l2Pl l2M19 50352417
def w383 : ℕ := l2Key l2M19 50335776
def w384 : ℕ := l2Pl l2M19 33703201
def w385 : ℕ := l2Pl l2M19 33686529
def w386 : ℕ := l2Pl l2M13 476417
def w387 : ℕ := l2Pl l2M13 377601
def w388 : ℕ := l2Key l2M13 360960
def w389 : ℕ := l2Pl l2M10 52822241
def w390 : ℕ := l2Pl l2M10 37175329
def w391 : ℕ := l2Key l2M46 402659072
def w392 : ℕ := l2Key l2M46 50335968
def w393 : ℕ := l2Key l2M46 272105602
def w394 : ℕ := l2Pl l2M46 37176609
def w395 : ℕ := l2Pl l2M46 36045825
def w396 : ℕ := l2Pl l2M46 1426275
def w397 : ℕ := l2Key l2M46 361026
def w398 : ℕ := l2Pl l2M46 36144707
def w399 : ℕ := l2Pl l2M46 1130785
def w400 : ℕ := l2Key l2M23 17907936
def w401 : ℕ := l2Key l2M23 16777440
def w402 : ℕ := l2Pl l2M23 1572994
def w403 : ℕ := l2Pl l2M23 1163362
def w404 : ℕ := l2Key l2M21 402658816
def w405 : ℕ := l2Key l2M21 50335936
def w406 : ℕ := l2Pl l2M21 271057026
def w407 : ℕ := l2Pl l2M21 36079170
def w408 : ℕ := l2Pl l2M21 33346
def w409 : ℕ := l2Pl l2M5 50845537
def w410 : ℕ := l2Pl l2M5 34064225
def w411 : ℕ := l2Pl l2M46 37209955
def w412 : ℕ := l2Key l2M17 134223360
def w413 : ℕ := l2Pl l2M17 50730048
def w414 : ℕ := l2Pl l2M17 50631232
def w415 : ℕ := l2Key l2M17 33948672
def w416 : ℕ := l2Pl l2M17 295488
def w417 : ℕ := l2Key l2M2 16777408
def w418 : ℕ := l2Key l2M2 16810048
def w419 : ℕ := l2Pl l2M2 32834
def w420 : ℕ := l2Key l2M46 50696930
def w421 : ℕ := l2Pl l2M5 50730081
def w422 : ℕ := l2Key l2M5 50730048
def w423 : ℕ := l2Pl l2M5 34030881
def w424 : ℕ := l2Pl l2M46 52926179
def w425 : ℕ := l2Pl l2M46 52827361
def w426 : ℕ := l2Key l2M2 16777344
def w427 : ℕ := l2Pl l2M2 524418
def w428 : ℕ := l2Pl l2M21 305005698
def w429 : ℕ := l2Key l2M21 36045824
def w430 : ℕ := l2Pl l2M21 295490
def w431 : ℕ := l2Key l2M9 402658048
def w432 : ℕ := l2Key l2M9 16781536
def w433 : ℕ := l2Pl l2M9 270008450
def w434 : ℕ := l2Pl l2M9 98882
def w435 : ℕ := l2Key l2M9 1130784
def w436 : ℕ := l2Pl l2M23 1654946
def w437 : ℕ := l2Pl l2M23 98370
def w438 : ℕ := l2Key l2M9 17912288
def w439 : ℕ := l2Key l2M12 134222592
def w440 : ℕ := l2Pl l2M12 16880224
def w441 : ℕ := l2Pl l2M12 16863584
def w442 : ℕ := l2Key l2M12 98880
def w443 : ℕ := l2Pl l2M12 82208
def w444 : ℕ := l2Key l2M9 16781472
def w445 : ℕ := l2Pl l2M9 270090658
def w446 : ℕ := l2Key l2M18 402658560
def w447 : ℕ := l2Key l2M18 50335904
def w448 : ℕ := l2Pl l2M18 272122273
def w449 : ℕ := l2Pl l2M18 2229249
def w450 : ℕ := l2Pl l2M18 1065249
def w451 : ℕ := l2Pl l2M21 2621570
def w452 : ℕ := l2Pl l2M46 272187811
def w453 : ℕ := l2Pl l2M9 270124002
def w454 : ℕ := l2Pl l2M46 272483299
def w455 : ℕ := l2Pl l2M9 16880354
def w456 : ℕ := l2Pl l2M17 50335808
def w457 : ℕ := l2Pl l2M17 33982016
def w458 : ℕ := l2Pl l2M71 16875616
def w459 : ℕ := l2Pl l2M71 16859232
def w460 : ℕ := l2Key l2M71 98368
def w461 : ℕ := l2Pl l2M71 81952
def w462 : ℕ := l2Key l2M13 134579968
def w463 : ℕ := l2Pl l2M13 493057
def w464 : ℕ := l2Key l2M5 184555360
def w465 : ℕ := l2Key l2M5 134584128
def w466 : ℕ := l2Key l2M5 50696800
def w467 : ℕ := l2Pl l2M72 406340865
def w468 : ℕ := l2Key l2M72 402654464
def w469 : ℕ := l2Pl l2M72 2229249
def w470 : ℕ := l2Pl l2M72 1065217
def w471 : ℕ := l2Key l2M9 419435488
def w472 : ℕ := l2Pl l2M3 151032384
def w473 : ℕ := l2Key l2M3 134222336
def w474 : ℕ := l2Pl l2M3 16781376
def w475 : ℕ := l2Pl l2M3 33344
def w476 : ℕ := l2Key l2M12 134320960
def w477 : ℕ := l2Pl l2M12 134304544
def w478 : ℕ := l2Pl l2M12 16781408
def w479 : ℕ := l2Pl l2M9 404312994
def w480 : ℕ := l2Pl l2M9 402756418
def w481 : ℕ := l2Key l2M46 403019586
def w482 : ℕ := l2Key l2M21 52827328
def w483 : ℕ := l2Pl l2M21 271352514
def w484 : ℕ := l2Pl l2M73 52854978
def w485 : ℕ := l2Key l2M73 50331840
def w486 : ℕ := l2Pl l2M73 2621570
def w487 : ℕ := l2Pl l2M73 294978
def w488 : ℕ := l2Pl l2M21 52860610
def w489 : ℕ := l2Key l2M21 52565120
def w490 : ℕ := l2Pl l2M21 402953794
def w491 : ℕ := l2Pl l2M21 405280386
def w492 : ℕ := l2Key l2M21 452990656
def w493 : ℕ := l2Key l2M21 134223360
def w494 : ℕ := l2Pl l2M21 321392834
def w495 : ℕ := l2Key l2M21 50331840
def w496 : ℕ := l2Pl l2M21 321787074
def w497 : ℕ := l2Key l2M21 50730048
def w498 : ℕ := l2Key l2M21 52822208
def w499 : ℕ := l2Pl l2M9 403182210
def w500 : ℕ := l2Pl l2M29 404308738
def w501 : ℕ := l2Key l2M72 405275648
def w502 : ℕ := l2Pl l2M72 272122113
def w503 : ℕ := l2Pl l2M18 406345121
def w504 : ℕ := l2Pl l2M18 35783681
def w505 : ℕ := l2Key l2M17 134222336
def w506 : ℕ := l2Key l2M46 452990944
def w507 : ℕ := l2Pl l2M46 406411171
def w508 : ℕ := l2Pl l2M9 1654946
def w509 : ℕ := l2Pl l2M46 322523619
def w510 : ℕ := l2Pl l2M5 34047553
def w511 : ℕ := l2Key l2M17 168171008
def w512 : ℕ := l2Key l2M24 402657536
def w513 : ℕ := l2Pl l2M24 286789792
def w514 : ℕ := l2Pl l2M24 16781472
def w515 : ℕ := l2Pl l2M24 270025120
def w516 : ℕ := l2Pl l2M18 16673
def w517 : ℕ := l2Pl l2M9 404345826
def w518 : ℕ := l2Pl l2M5 16673
def w519 : ℕ := l2Pl l2M8 82177
def w520 : ℕ := l2Pl l2M5 394241
def w521 : ℕ := l2Key l2M5 16781408
def w522 : ℕ := l2Pl l2M8 406406915
def w523 : ℕ := l2Key l2M1 134234368
def w524 : ℕ := l2Pl l2M5 50418017
def w525 : ℕ := l2Pl l2M5 377697
def w526 : ℕ := l2Pl l2M4 151015712
def w527 : ℕ := l2Key l2M4 134222080
def w528 : ℕ := l2Pl l2M4 16781344
def w529 : ℕ := l2Pl l2M4 16672
def w530 : ℕ := l2Pl l2M24 403722528
def w531 : ℕ := l2Key l2M24 270008448
def w532 : ℕ := l2Pl l2M46 403789601
def w533 : ℕ := l2Key l2M46 406329218
def w534 : ℕ := l2Pl l2M9 1164130
def w535 : ℕ := l2Key l2M5 295488
def w536 : ℕ := l2Key l2M46 272466626
def w537 : ℕ := l2Pl l2M21 50631362
def w538 : ℕ := l2Pl l2M5 134305569
def w539 : ℕ := l2Pl l2M9 286789858
def w540 : ℕ := l2Key l2M46 322441442
def w541 : ℕ := l2Pl l2M18 402674977
def w542 : ℕ := l2Key l2M18 272105600
def w543 : ℕ := l2Key l2M18 406328704
def w544 : ℕ := l2Pl l2M46 82209
def w545 : ℕ := l2Pl l2M10 376931
def w546 : ℕ := l2Pl l2M10 81953
def w547 : ℕ := l2Key l2M10 4030658
def w548 : ℕ := l2Key l2M10 50692322
def w549 : ℕ := l2Key l2M10 54001890
def w550 : ℕ := l2Pl l2M18 403723553
def w551 : ℕ := l2Key l2M18 271057024
def w552 : ℕ := l2Key l2M18 405280128
def w553 : ℕ := l2Key l2M46 271057026
def w554 : ℕ := l2Key l2M10 2621570
def w555 : ℕ := l2Key l2M10 2982082
def w556 : ℕ := l2Pl l2M10 36569219
def w557 : ℕ := l2Key l2M10 52953314
def w558 : ℕ := l2Key l2M9 403788576
def w559 : ℕ := l2Key l2M9 115552
def w560 : ℕ := l2Key l2M23 96
def w561 : ℕ := l2Pl l2M23 1163266
def w562 : ℕ := l2Key l2M9 1130848
def w563 : ℕ := l2Pl l2M74 17842336
def w564 : ℕ := l2Key l2M74 1572992
def w565 : ℕ := l2Pl l2M74 1048608
def w566 : ℕ := l2Pl l2M74 18350240
def w567 : ℕ := l2Key l2M74 1048704
def w568 : ℕ := l2Pl l2M74 1064992
def w569 : ℕ := l2Pl l2M9 404231042
def w570 : ℕ := l2Pl l2M23 18350306
def w571 : ℕ := l2Key l2M23 16777312
def w572 : ℕ := l2Key l2M9 16863584
def w573 : ℕ := l2Key l2M23 17842336
def w574 : ℕ := l2Pl l2M46 51466721
def w575 : ℕ := l2Pl l2M5 50828897
def w576 : ℕ := l2Pl l2M21 50369218
def w577 : ℕ := l2Key l2M21 35783680
def w578 : ℕ := l2Key l2M21 52565184
def w579 : ℕ := l2Pl l2M9 17945570
def w580 : ℕ := l2Pl l2M5 50713441
def w581 : ℕ := l2Pl l2M46 51762147
def w582 : ℕ := l2Pl l2M46 51401121
def w583 : ℕ := l2Pl l2M10 51462369
def w584 : ℕ := l2Key l2M8 403015426
def w585 : ℕ := l2Pl l2M21 305039042
def w586 : ℕ := l2Pl l2M23 17940706
def w587 : ℕ := l2Key l2M23 1130528
def w588 : ℕ := l2Key l2M4 150999040
def w589 : ℕ := l2Key l2M9 420565984
def w590 : ℕ := l2Pl l2M46 454121441
def w591 : ℕ := l2Pl l2M1 16385
def w592 : ℕ := l2Pl l2M46 51462369
def w593 : ℕ := l2Key l2M10 294978
def w594 : ℕ := l2Key l2M10 1163362
def w595 : ℕ := l2Pl l2M10 4047075
def w596 : ℕ := l2Pl l2M10 51757283
def w597 : ℕ := l2Pl l2M2 32770
def w598 : ℕ := l2Pl l2M23 1671362
def w599 : ℕ := l2Key l2M2 32832
def w600 : ℕ := l2Pl l2M18 305792129
def w601 : ℕ := l2Key l2M24 404230528
def w602 : ℕ := l2Pl l2M24 1065248
def w603 : ℕ := l2Pl l2M5 134600545
def w604 : ℕ := l2Pl l2M9 403821410
def w605 : ℕ := l2Pl l2M46 404084579
def w606 : ℕ := l2Key l2M5 134304544
def w607 : ℕ := l2Pl l2M24 421007776
def w608 : ℕ := l2Pl l2M73 53346498
def w609 : ℕ := l2Pl l2M75 419434624
def w610 : ℕ := l2Key l2M75 402657280
def w611 : ℕ := l2Pl l2M75 285741184
def w612 : ℕ := l2Pl l2M75 268959872
def w613 : ℕ := l2Pl l2M8 1065217
def w614 : ℕ := l2Pl l2M8 3655427
def w615 : ℕ := l2Pl l2M8 404080387
def w616 : ℕ := l2Key l2M5 115552
def w617 : ℕ := l2Key l2M13 768
def w618 : ℕ := l2Pl l2M13 376833
def w619 : ℕ := l2Key l2M5 361280
def w620 : ℕ := l2Pl l2M67 262656
def w621 : ℕ := l2Key l2M67 263168
def w622 : ℕ := l2Pl l2M13 134612737
def w623 : ℕ := l2Key l2M13 134218496
def w624 : ℕ := l2Key l2M5 134320960
def w625 : ℕ := l2Key l2M46 1164130
def w626 : ℕ := l2Pl l2M60 4046851
def w627 : ℕ := l2Pl l2M46 406706147
def w628 : ℕ := l2Pl l2M46 377697
def w629 : ℕ := l2Pl l2M46 1425507
def w630 : ℕ := l2Pl l2M18 305808801
def w631 : ℕ := l2Pl l2M18 440014209
def w632 : ℕ := l2Pl l2M10 33947649
def w633 : ℕ := l2Pl l2M46 33948673
def w634 : ℕ := l2Key l2M46 270008450
def w635 : ℕ := l2Key l2M18 16781472
def w636 : ℕ := l2Pl l2M46 438703873
def w637 : ℕ := l2Pl l2M76 184554496
def w638 : ℕ := l2Pl l2M76 167908352
def w639 : ℕ := l2Key l2M76 50335744
def w640 : ℕ := l2Pl l2M76 33686528
def w641 : ℕ := l2Pl l2M18 36848929
def w642 : ℕ := l2Pl l2M18 51401121
def w643 : ℕ := l2Key l2M18 405279872
def w644 : ℕ := l2Pl l2M18 52565153
def w645 : ℕ := l2Key l2M18 452990368
def w646 : ℕ := l2Pl l2M18 438441217
def w647 : ℕ := l2Key l2M18 404230528
def w648 : ℕ := l2Key l2M18 402654464
def w649 : ℕ := l2Key l2M18 406324480
def w650 : ℕ := l2Key l2M46 3670146
def w651 : ℕ := l2Key l2M46 134223616
def w652 : ℕ := l2Pl l2M46 53991395
def w653 : ℕ := l2Pl l2M46 1426179
def w654 : ℕ := l2Pl l2M8 394241
def w655 : ℕ := l2Pl l2M46 2491393
def w656 : ℕ := l2Key l2M46 16781536
def w657 : ℕ := l2Key l2M8 272466434
def w658 : ℕ := l2Key l2M1 16640
def w659 : ℕ := l2Key l2M13 134514176
def w660 : ℕ := l2Pl l2M8 2229249
def w661 : ℕ := l2Key l2M1 134218752
def w662 : ℕ := l2Pl l2M9 33346
def w663 : ℕ := l2Key l2M8 295426
def w664 : ℕ := l2Key l2M46 295490
def w665 : ℕ := l2Key l2M9 1065248
def w666 : ℕ := l2Pl l2M10 1064993
def w667 : ℕ := l2Pl l2M46 1065249
def w668 : ℕ := l2Key l2M5 134223360
def w669 : ℕ := l2Pl l2M5 50467873
def w670 : ℕ := l2Pl l2M27 50823265
def w671 : ℕ := l2Key l2M27 50331744
def w672 : ℕ := l2Key l2M27 360512
def w673 : ℕ := l2Pl l2M27 81953
def w674 : ℕ := l2Key l2M73 52560000
def w675 : ℕ := l2Pl l2M73 36077634
def w676 : ℕ := l2Pl l2M24 16781344
def w677 : ℕ := l2Pl l2M5 493057
def w678 : ℕ := l2Pl l2M46 438802243
def w679 : ℕ := l2Pl l2M10 52920547
def w680 : ℕ := l2Pl l2M9 1572994
def w681 : ℕ := l2Key l2M9 134222592
def w682 : ℕ := l2Pl l2M5 168171265
def w683 : ℕ := l2Pl l2M8 3622145
def w684 : ℕ := l2Key l2M8 98818
def w685 : ℕ := l2Pl l2M8 1164035
def w686 : ℕ := l2Key l2M46 98882
def w687 : ℕ := l2Pl l2M8 3360001
def w688 : ℕ := l2Pl l2M8 272237571
def w689 : ℕ := l2Pl l2M8 404883201
def w690 : ℕ := l2Pl l2M46 35783681
def w691 : ℕ := l2Pl l2M22 402690626
def w692 : ℕ := l2Key l2M22 402657792
def w693 : ℕ := l2Key l2M22 16781504
def w694 : ℕ := l2Pl l2M22 268993218
def w695 : ℕ := l2Pl l2M22 268959874
def w696 : ℕ := l2Key l2M9 404230528
def w697 : ℕ := l2Pl l2M9 270107330
def w698 : ℕ := l2Pl l2M17 184948288
def w699 : ℕ := l2Pl l2M72 406455553
def w700 : ℕ := l2Key l2M9 16880224
def w701 : ℕ := l2Key l2M3 150999040
def w702 : ℕ := l2Key l2M5 184915808
def w703 : ℕ := l2Key l2M46 402953794
def w704 : ℕ := l2Pl l2M13 134596353
def w705 : ℕ := l2Key l2M46 453351394
def w706 : ℕ := l2Key l2M46 403015426
def w707 : ℕ := l2Pl l2M46 322835683
def w708 : ℕ := l2Pl l2M46 306054275
def w709 : ℕ := l2Pl l2M73 36569218
def w710 : ℕ := l2Key l2M73 50724928
def w711 : ℕ := l2Pl l2M72 272237569
def w712 : ℕ := l2Key l2M72 404226304
def w713 : ℕ := l2Pl l2M46 50730209
def w714 : ℕ := l2Pl l2M10 34046019
def w715 : ℕ := l2Pl l2M8 270090499
def w716 : ℕ := l2Key l2M46 404232066
def w717 : ℕ := l2Key l2M46 52827328
def w718 : ℕ := l2Key l2M21 438703616
def w719 : ℕ := l2Pl l2M17 50724928
def w720 : ℕ := l2Pl l2M9 404329410
def w721 : ℕ := l2Key l2M9 16781408
def w722 : ℕ := l2Key l2M21 419435200
def w723 : ℕ := l2Pl l2M46 455481313
def w724 : ℕ := l2Pl l2M46 52822241
def w725 : ℕ := l2Key l2M1 132096
def w726 : ℕ := l2Pl l2M46 52565153
def w727 : ℕ := l2Pl l2M5 50812257
def w728 : ℕ := l2Pl l2M46 457054179
def w729 : ℕ := l2Pl l2M10 50724961
def w730 : ℕ := l2Key l2M10 50331840
def w731 : ℕ := l2Pl l2M10 52560033
def w732 : ℕ := l2Key l2M46 456660962
def w733 : ℕ := l2Pl l2M18 322573473
def w734 : ℕ := l2Pl l2M46 50730081
def w735 : ℕ := l2Key l2M2 16777280
def w736 : ℕ := l2Key l2M1 134349824
def w737 : ℕ := l2Pl l2M1 131073
def w738 : ℕ := l2Pl l2M46 440276867
def w739 : ℕ := l2Key l2M1 134217984
def w740 : ℕ := l2Key l2M22 419435200
def w741 : ℕ := l2Key l2M22 16781440
def w742 : ℕ := l2Pl l2M22 33346
def w743 : ℕ := l2Key l2M19 184554784
def w744 : ℕ := l2Pl l2M19 167908609
def w745 : ℕ := l2Pl l2M19 16673
def w746 : ℕ := l2Key l2M46 406328704
def w747 : ℕ := l2Key l2M5 134222592
def w748 : ℕ := l2Key l2M18 322441376
def w749 : ℕ := l2Key l2M24 404226304
def w750 : ℕ := l2Key l2M18 184554784
def w751 : ℕ := l2Key l2M46 406324994
def w752 : ℕ := l2Key l2M2 524416
def w753 : ℕ := l2Key l2M46 405280386
def w754 : ℕ := l2Key l2M46 404231042
def w755 : ℕ := l2Key l2M8 402654464
def w756 : ℕ := l2Key l2M2 17301632
def w757 : ℕ := l2Pl l2M2 524290
def w758 : ℕ := l2Key l2M19 134222848
def w759 : ℕ := l2Pl l2M22 285741250
def w760 : ℕ := l2Key l2M5 184555072
def w761 : ℕ := l2Key l2M46 452990656
def w762 : ℕ := l2Key l2M9 419434912
def w763 : ℕ := l2Key l2M46 452990368
def w764 : ℕ := l2Key l2M46 419435488
def w765 : ℕ := l2Key l2M46 184555360
def w766 : ℕ := l2Key l2M35 134224640
def w767 : ℕ := l2Key l2M35 83890272
def w768 : ℕ := l2Pl l2M35 71305228
def w769 : ℕ := l2Key l2M35 98888
def w770 : ℕ := l2Pl l2M35 82212
def w771 : ℕ := l2Key l2M28 4590620
def w772 : ℕ := l2Key l2M20 134352144
def w773 : ℕ := l2Key l2M14 393232
def w774 : ℕ := l2Pl l2M14 376845
def w775 : ℕ := l2Key l2M3 134221824
def w776 : ℕ := l2Key l2M51 134225664
def w777 : ℕ := l2Key l2M51 121641084
def w778 : ℕ := l2Pl l2M51 71387453
def w779 : ℕ := l2Pl l2M51 33948689
def w780 : ℕ := l2Pl l2M51 377709
def w781 : ℕ := l2Key l2M38 205528340
def w782 : ℕ := l2Key l2M38 134225152
def w783 : ℕ := l2Pl l2M38 117576753
def w784 : ℕ := l2Pl l2M38 71321909
def w785 : ℕ := l2Pl l2M38 33686545
def w786 : ℕ := l2Pl l2M38 16677
def w787 : ℕ := l2Key l2M38 117444640
def w788 : ℕ := l2Key l2M51 117444704
def w789 : ℕ := l2Key l2M51 71305244
def w790 : ℕ := l2Pl l2M51 134307621
def w791 : ℕ := l2Pl l2M51 34064253
def w792 : ℕ := l2Key l2M40 134225408
def w793 : ℕ := l2Key l2M40 117838928
def w794 : ℕ := l2Pl l2M40 71305240
def w795 : ℕ := l2Key l2M40 33948688
def w796 : ℕ := l2Pl l2M40 295496
def w797 : ℕ := l2Key l2M40 117444672
def w798 : ℕ := l2Key l2M40 168173072
def w799 : ℕ := l2Key l2M20 134220032
def w800 : ℕ := l2Key l2M28 134220544
def w801 : ℕ := l2Key l2M51 205528860
def w802 : ℕ := l2Key l2M20 134219008
def w803 : ℕ := l2Key l2M28 134219520
def w804 : ℕ := l2Pl l2M27 34062433
def w805 : ℕ := l2Pl l2M27 33947649
def w806 : ℕ := l2Pl l2M51 82213
def w807 : ℕ := l2Pl l2M51 134602605
def w808 : ℕ := l2Pl l2M38 167910673
def w809 : ℕ := l2Key l2M38 121641012
def w810 : ℕ := l2Key l2M38 71305236
def w811 : ℕ := l2Pl l2M38 33703221
def w812 : ℕ := l2Pl l2M40 33352
def w813 : ℕ := l2Key l2M28 134220800
def w814 : ℕ := l2Key l2M6 134219776
def w815 : ℕ := l2Key l2M20 134220800
def w816 : ℕ := l2Pl l2M16 138414096
def w817 : ℕ := l2Pl l2M40 121641048
def w818 : ℕ := l2Pl l2M40 71600728
def w819 : ℕ := l2Pl l2M40 255860312
def w820 : ℕ := l2Key l2M3 134218240
def w821 : ℕ := l2Pl l2M6 138447368
def w822 : ℕ := l2Key l2M15 134218496
def w823 : ℕ := l2Pl l2M15 115468
def w824 : ℕ := l2Key l2M6 134218240
def w825 : ℕ := l2Pl l2M77 50348065
def w826 : ℕ := l2Key l2M77 50331680
def w827 : ℕ := l2Pl l2M77 33701921
def w828 : ℕ := l2Pl l2M77 33685505
def w829 : ℕ := l2Pl l2M51 34030901
def w830 : ℕ := l2Key l2M51 361032
def w831 : ℕ := l2Key l2M37 117571632
def w832 : ℕ := l2Key l2M37 71303188
def w833 : ℕ := l2Pl l2M37 33685521
def w834 : ℕ := l2Pl l2M37 16421
def w835 : ℕ := l2Pl l2M38 134241573
def w836 : ℕ := l2Key l2M38 33686544
def w837 : ℕ := l2Key l2M7 131088
def w838 : ℕ := l2Key l2M38 117576752
def w839 : ℕ := l2Pl l2M38 205544757
def w840 : ℕ := l2Pl l2M51 34047577
def w841 : ℕ := l2Pl l2M51 205610813
def w842 : ℕ := l2Pl l2M34 34046041
def w843 : ℕ := l2Pl l2M34 117833841
def w844 : ℕ := l2Key l2M31 134224128
def w845 : ℕ := l2Key l2M31 134223872
def w846 : ℕ := l2Pl l2M31 88086564
def w847 : ℕ := l2Pl l2M31 16676
def w848 : ℕ := l2Key l2M4 134221824
def w849 : ℕ := l2Pl l2M1 134349825
def w850 : ℕ := l2Key l2M38 134224896
def w851 : ℕ := l2Key l2M51 134225408
def w852 : ℕ := l2Key l2M5 33982016
def w853 : ℕ := l2Pl l2M51 117838961
def w854 : ℕ := l2Key l2M5 134219520
def w855 : ℕ := l2Pl l2M51 168173329
def w856 : ℕ := l2Pl l2M5 33947649
def w857 : ℕ := l2Pl l2M40 205528600
def w858 : ℕ := l2Pl l2M40 105253912
def w859 : ℕ := l2Pl l2M40 33982040
def w860 : ℕ := l2Pl l2M40 134520392
def w861 : ℕ := l2Pl l2M40 122035288
def w862 : ℕ := l2Pl l2M59 122028120
def w863 : ℕ := l2Pl l2M59 71303192
def w864 : ℕ := l2Key l2M59 33947664
def w865 : ℕ := l2Pl l2M59 294984
def w866 : ℕ := l2Pl l2M51 122035325
def w867 : ℕ := l2Pl l2M38 239213845
def w868 : ℕ := l2Pl l2M51 105253917
def w869 : ℕ := l2Pl l2M14 491529
def w870 : ℕ := l2Pl l2M28 493065
def w871 : ℕ := l2Pl l2M20 134352129
def w872 : ℕ := l2Pl l2M28 394241
def w873 : ℕ := l2Pl l2M20 132097
def w874 : ℕ := l2Pl l2M7 131073
def w875 : ℕ := l2Key l2M40 134224896
def w876 : ℕ := l2Key l2M40 33947664
def w877 : ℕ := l2Key l2M40 50730048
def w878 : ℕ := l2Pl l2M51 252059505
def w879 : ℕ := l2Pl l2M28 83205
def w880 : ℕ := l2Key l2M28 361992
def w881 : ℕ := l2Key l2M28 4197404
def w882 : ℕ := l2Key l2M28 1024
def w883 : ℕ := l2Pl l2M17 50729024
def w884 : ℕ := l2Pl l2M17 33980992
def w885 : ℕ := l2Pl l2M51 33947665
def w886 : ℕ := l2Key l2M7 4194320
def w887 : ℕ := l2Key l2M7 4194308
def w888 : ℕ := l2Pl l2M38 121657653
def w889 : ℕ := l2Pl l2M38 33686529
def w890 : ℕ := l2Pl l2M38 121773109
def w891 : ℕ := l2Pl l2M38 33703205
def w892 : ℕ := l2Key l2M37 121634868
def w893 : ℕ := l2Pl l2M37 33685505
def w894 : ℕ := l2Key l2M38 255860020
def w895 : ℕ := l2Key l2M51 255860604
def w896 : ℕ := l2Key l2M38 134224128
def w897 : ℕ := l2Pl l2M1 134234369
def w898 : ℕ := l2Key l2M38 205528080
def w899 : ℕ := l2Key l2M38 88086564
def w900 : ℕ := l2Key l2M38 134219008
def w901 : ℕ := l2Key l2M4 134217984
def w902 : ℕ := l2Key l2M51 134223616
def w903 : ℕ := l2Pl l2M47 412621698
def w904 : ℕ := l2Key l2M47 83890400
def w905 : ℕ := l2Key l2M47 79693836
def w906 : ℕ := l2Pl l2M47 278397058
def w907 : ℕ := l2Pl l2M47 98890
def w908 : ℕ := l2Key l2M47 1130788
def w909 : ℕ := l2Key l2M47 402660096
def w910 : ℕ := l2Key l2M50 402659584
def w911 : ℕ := l2Key l2M50 83890336
def w912 : ℕ := l2Pl l2M50 349702276
def w913 : ℕ := l2Key l2M50 278397056
def w914 : ℕ := l2Pl l2M50 1065252
def w915 : ℕ := l2Pl l2M78 448667539
def w916 : ℕ := l2Pl l2M78 438705937
def w917 : ℕ := l2Key l2M78 117444832
def w918 : ℕ := l2Key l2M78 79693852
def w919 : ℕ := l2Pl l2M78 36144731
def w920 : ℕ := l2Pl l2M78 1130789
def w921 : ℕ := l2Pl l2M78 46006419
def w922 : ℕ := l2Key l2M78 402661120
def w923 : ℕ := l2Key l2M78 280494210
def w924 : ℕ := l2Pl l2M78 438804315
def w925 : ℕ := l2Pl l2M78 36045841
def w926 : ℕ := l2Pl l2M78 448765915
def w927 : ℕ := l2Key l2M78 414719874
def w928 : ℕ := l2Pl l2M78 448782335
def w929 : ℕ := l2Key l2M78 447618706
def w930 : ℕ := l2Key l2M78 361034
def w931 : ℕ := l2Pl l2M78 448749495
def w932 : ℕ := l2Key l2M78 412703654
def w933 : ℕ := l2Key l2M78 403021642
def w934 : ℕ := l2Pl l2M78 1426287
def w935 : ℕ := l2Key l2M78 447651546
def w936 : ℕ := l2Key l2M78 412736494
def w937 : ℕ := l2Pl l2M78 440391651
def w938 : ℕ := l2Pl l2M78 415223583
def w939 : ℕ := l2Key l2M78 412621698
def w940 : ℕ := l2Key l2M78 130029820
def w941 : ℕ := l2Pl l2M78 118575589
def w942 : ℕ := l2Key l2M78 520101856
def w943 : ℕ := l2Pl l2M78 532553715
def w944 : ℕ := l2Pl l2M78 1311491
def w945 : ℕ := l2Key l2M78 447717082
def w946 : ℕ := l2Pl l2M78 81005343
def w947 : ℕ := l2Pl l2M78 118756323
def w948 : ℕ := l2Pl l2M78 36160637
def w949 : ℕ := l2Key l2M78 447356048
def w950 : ℕ := l2Key l2M78 114796
def w951 : ℕ := l2Pl l2M78 448404881
def w952 : ℕ := l2Pl l2M78 46121215
def w953 : ℕ := l2Key l2M78 402775916
def w954 : ℕ := l2Key l2M78 295498
def w955 : ℕ := l2Pl l2M78 1065253
def w956 : ℕ := l2Pl l2M78 536748031
def w957 : ℕ := l2Pl l2M78 406718211
def w958 : ℕ := l2Pl l2M78 415108883
def w959 : ℕ := l2Pl l2M78 134086911
def w960 : ℕ := l2Pl l2M78 524163043
def w961 : ℕ := l2Pl l2M78 440276867
def w962 : ℕ := l2Pl l2M78 457054179
def w963 : ℕ := l2Pl l2M78 519970719
def w964 : ℕ := l2Pl l2M78 314442899
def w965 : ℕ := l2Pl l2M78 119936241
def w966 : ℕ := l2Pl l2M78 522592241
def w967 : ℕ := l2Pl l2M78 412703655
def w968 : ℕ := l2Key l2M78 411572866
def w969 : ℕ := l2Pl l2M78 412994319
def w970 : ℕ := l2Pl l2M78 412998639
def w971 : ℕ := l2Key l2M78 483924894
def w972 : ℕ := l2Key l2M78 404231042
def v0 : List ℕ := [w82,w80,w88]
def v1 : List ℕ := [w82,w85,w88]
def v2 : List ℕ := [w84,w82,w80]
def v3 : List ℕ := [w92,w91,w90]
def v4 : List ℕ := [w108,w107,w105]
def v5 : List ℕ := [w108,w105,w115]
def v6 : List ℕ := [w112,w108,w105]
def v7 : List ℕ := [w108,w128,w105]
def v8 : List ℕ := [w108,w105,w130]
def v9 : List ℕ := [w108,w105,w152]
def v10 : List ℕ := [w181,w147,w145]
def v11 : List ℕ := [w147,w145,w186]
def v12 : List ℕ := [w378,w377,w376]
def v13 : List ℕ := [w393,w392,w391]
def v14 : List ℕ := [w406,w405,w404]
def v15 : List ℕ := [w392,w420,w391]
def v16 : List ℕ := [w425,w424,w391]
def v17 : List ℕ := [w393,w425,w391]
def v18 : List ℕ := [w392,w425,w391]
def v19 : List ℕ := [w433,w432,w431]
def v20 : List ℕ := [w432,w438,w431]
def v21 : List ℕ := [w448,w447,w446]
def v22 : List ℕ := [w452,w392,w391]
def v23 : List ℕ := [w454,w392,w391]
def v24 : List ℕ := [w405,w482,w404]
def v25 : List ℕ := [w392,w391,w506]
def v26 : List ℕ := [w510,w377,w376]
def v27 : List ℕ := [w377,w376,w465]
def v28 : List ℕ := [w392,w391,w532]
def v29 : List ℕ := [w392,w391,w533]
def v30 : List ℕ := [w425,w391,w533]
def v31 : List ℕ := [w392,w533,w506]
def v32 : List ℕ := [w377,w376,w538]
def v33 : List ℕ := [w447,w446,w543]
def v34 : List ℕ := [w45,w43,w41]
def v35 : List ℕ := [w43,w41,w389]
def v36 : List ℕ := [w147,w217,w145]
def v37 : List ℕ := [w393,w392,w533]
def v38 : List ℕ := [w644,w446,w543]
def v39 : List ℕ := [w425,w391,w506]
def v40 : List ℕ := [w425,w707,w391]
def v41 : List ℕ := [w788,w776,w790]
def v42 : List ℕ := [w789,w788,w776]
def v43 : List ℕ := [w91,w800,w90]
def v44 : List ℕ := [w918,w917,w922]
def v45 : List ℕ := [w922,w915,w931]
def v46 : List ℕ := [w932,w922,w915]
def v47 : List ℕ := [w917,w933,w915]
def v48 : List ℕ := [w917,w922,w915]
def v49 : List ℕ := [w940,w922,w915]
def v50 : List ℕ := w411::v13
def v51 : List ℕ := w393::v18
def v52 : List ℕ := w433::v20
def v53 : List ℕ := w378::v27
def v54 : List ℕ := w392::v30
def v55 : List ℕ := w395::v13
def v56 : List ℕ := w393::v25
def v57 : List ℕ := w918::v48
def v58 : List ℕ := w395::w393::v23
def v59 : List ℕ := w397::v55
def v60 : List ℕ := w396::v55
def v61 : List ℕ := w925::w918::v47
def v62 : List ℕ := w925::v57
def l2C (s f b : ℕ) (v : List ℕ) (t : ℕ) : L2Cell := ⟨s,f,b != 0,v,t⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB0 : Array L2Cell := #[l2C 5 0 1 [w2,w1] 0x0,l2C 15 2 1 [w6,w5,w4,w3] 0x0,l2C 19 1 1 [w9,w8,w7] 0x0,l2C 21 3 1 [w12,w11,w10] 0x0,l2C 23 4 1 [w16,w15,w14,w13] 0x8,l2C 27 3 1 [w20,w19,w18,w17] 0x0,l2C 31 5 0 [w25,w24,w23,w22,w21] 0x80080080080000080080f9014014,l2C 31 5 0 [w25,w27,w23,w26,w21] 0x5a05a00005a05a05a05a00000005a0000000f900005a0f9008291,l2C 31 5 0 [w25,w23,w28,w26,w21] 0x7a07a00007a00007a0d000007a0d000827a07a07a07a000000000,l2C 31 5 0 [w25,w24,w23,w29,w21] 0x140140080080080d0008008000008000000,l2C 31 5 0 [w25,w24,w23,w21,w30] 0x14014000000000008008008008008008008008000008008008000008000000,l2C 31 6 0 [w25,w24,w23,w26,w21] 0x140140140140144170140140000d00000d00140140140140140144160140080080080080140140080140140140080080080080084150080080080080080080084140080080000f90000f90140140140140140144130140d00f90000d0,l2C 31 6 1 [w25,w24,w23,w26,w21] 0x418,l2C 51 2 1 [w34,w33,w32,w31] 0x0,l2C 55 5 1 [w39,w38,w37,w36,w35] 0x14,l2C 31 5 0 [w23,w28,w26,w22,w21] 0x7a07a00007a00000000000000827a,l2C 31 5 0 [w40,w24,w23,w22,w21] 0x80080080080000080140140080f9,l2C 31 6 0 [w24,w23,w26,w22,w21] 0x1401401401401401401441d01400000000000000000000000001401401401401401400800800800800800800800800800801401401401400800800800800841c008008,l2C 31 6 1 [w24,w23,w26,w22,w21] 0x41e,l2C 47 5 0 [w45,w44,w43,w42,w41] 0x213b00000006e06e00006e,l2C 47 5 0 [w47,w46,w44,w43,w41] 0x210210020fa002002000002002002,l2C 47 6 0 [w47,w45,w44,w43,w41] 0x21021021021021021000000000000021021021021021021021421021002002002002002002002002002420002002002002002002002002021021021021,l2C 47 6 1 [w47,w45,w44,w43,w41] 0x422,l2C 62 5 0 [w52,w51,w50,w49,w48] 0x10f10f0020020f90f9000000002002002000000000,l2C 62 5 0 [w52,w54,w51,w53,w48] 0x234a0002b30000002b32b3,l2C 62 6 0 [w52,w54,w51,w50,w48] 0x200200200200200200000000000000200200200200200242500210f10f10f10f10f10f10f42410f10f10f10f10f00000000000000200200200200000000000010f10f10f10f10f10f,l2C 62 6 1 [w52,w54,w51,w50,w48] 0x426,l2C 31 5 0 [w25,w27,w26,w29,w21] 0x5a05a00005a000000000000008291,l2C 31 5 0 [w25,w24,w55,w29,w21] 0x140140080080080d0008008000008000000,l2C 31 6 0 [w25,w24,w26,w29,w21] 0x14014014014014014014429014008008008008008008008008008008014014014014008008008008008428008008000000000000000000000000014014014014014014,l2C 31 6 1 [w25,w24,w26,w29,w21] 0x42a,l2C 47 5 0 [w58,w57,w45,w56,w41] 0x5c05c00005c000000000000002183]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB1 : Array L2Cell := #[l2C 47 5 0 [w47,w58,w59,w56,w41] 0x2102100000000200200200000200202d02d,l2C 47 6 0 [w47,w58,w45,w56,w41] 0x2102102102102102102142d02100000000000000000000000002102102102102102100200200200200200242c002002002002002002002002002002002021021021021,l2C 47 6 1 [w47,w58,w45,w56,w41] 0x42e,l2C 63 7 0 [w66,w65,w64,w63,w62,w61,w60] 0x4e04e04e04302704e04e02700c04304300c04e04e04e04e0430430430430430400431320f113204013204004004004004004e04e04e04e04e13204e0430430430430400d110e13110e13110e10e10e10e10e10e10e10e13210e10e10e10e03d10e03d18203d18203d03d03d03d04003d03d03d03d03d03d,l2C 63 7 0 [w66,w65,w64,w67,w61,w60] 0xd10d10d10d10d10d10250d10d10d10d10d102502502502502502504002504004e0400d10d10d10d10d10d11320d10250250250250d10d10d10d102502502502514f14f14f14f14f14f14f14f14f13214f14f14f14f14f14f14f06814f14f0d10d10d10d1025025025025068068068068068040068068068068068068,l2C 63 7 0 [w66,w65,w68,w63,w61,w60] 0xf10f10f10f10f10f105b0f10f10f10f10f105b05b05b05b05b05b04005b04013204e0f10f10f10f10f10f11320f105b05b05b05b0f10f10f10f105b05b05b05b14e14e14e14e14e14e14e14e14e13214e14e14e14e14e14e14e1b314e14e0f10f10f10f105b05b05b05b1b31b31b31b31b30401b31b31b31b31b31b3,l2C 61 5 0 [w73,w72,w71,w70,w69] 0x23100834b000000231231000000,l2C 61 5 0 [w73,w72,w75,w70,w74] 0x80080080fa049049008008008000000000000000,l2C 61 6 0 [w73,w72,w71,w70,w74] 0x8008008008008008049049049049049434049049049049049049049008008008008008008433008000000000000008008008008000000000000049049049049049049000000000000,l2C 61 6 1 [w73,w72,w71,w70,w74] 0x435,l2C 63 8 0 [w66,w65,w64,w63,w61,w60] 0x2702702702702702700c02702702702702700c00c00c00c00c00c43600c13243204043143042f42b04002702702702702702742702700c00c00c00c02702702702700c00c00c00c13113113113113113113113113142313113113113113113113118213113102702702702700c00c00c00c18218218218218241f182182182182182182,l2C 63 8 1 [w66,w65,w64,w63,w61,w60] 0x437,l2C 83 4 1 [w79,w78,w77,w76] 0xd,l2C 85 4 0 [w84,w83,w82,w81,w80] 0x100100d000,l2C 85 4 0 [w84,w83,w82,w80,w85] 0x800800d000,l2C 85 4 0 [w87,w83,w82,w86,w80] 0x1001017000,l2C 85 4 0 (w87::w83::v0) 0x8008017000,l2C 85 5 0 [w87,w84,w83,w82,w80] 0x800000000800100000000100d43d00d43c01700d01743b01743a00d00d00d01700d00d00d,l2C 85 4 0 [w84,w82,w81,w80,w85] 0x8008001000,l2C 85 4 0 [w87,w84,w81,w86,w80] 0xd00d017000,l2C 85 4 0 [w87,w84,w81,w80,w89] 0x8008017000,l2C 85 5 0 [w87,w84,w82,w81,w80] 0x800000000800144101700100000d00000d00144001743f00100100101700100100101743a,l2C 85 4 0 (w87::w84::v1) 0xd00d017000,l2C 85 4 0 [w87,w84,w82,w85,w89] 0x1001017000,l2C 85 5 0 [w87,w84,w82,w80,w85] 0x1700800000100000100844400000d00000d00844300800800801700800800801743f01743b,l2C 85 4 0 [w87,w82,w86,w80,w88] 0x8008001000,l2C 85 4 0 [w87,w84,w86,w80,w89] 0x800800d000,l2C 85 5 0 [w87,w84,w82,w86,w80] 0x800000000800144700d00100d44600100100100d00100100100001700001700144000d43c,l2C 85 4 0 [w87,w84,w82,w88,w89] 0x100100d000,l2C 85 5 0 (w87::w84::v0) 0xd00800000100000100844900800800800d00800800800d44600001700001700844300d43d,l2C 85 5 0 [w87,w84,w82,w80,w89] 0x100800800800800100800800800000d00000d008449001447000017000017008444001441,l2C 85 6 0 (w87::v2) 0x800144b00800800d44a00800100d44800100801744500800101744200100d01743e00d]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB2 : Array L2Cell := #[l2C 85 6 1 (w87::v2) 0x44c,l2C 87 7 1 (w94::w93::v3) 0x1d,l2C 91 5 0 [w99,w98,w97,w96,w95] 0x1601600000000d00d0d000d09009009000d090090,l2C 91 5 0 [w99,w98,w97,w100,w96] 0x1601600d00d03100d09509509500d095095,l2C 91 6 0 [w99,w98,w101,w97,w96] 0xd00310000d001601601601601601645001601601601601601644f0160160d000d00d0d003100d00d03101601600d01601601603c03c03c03c03c03c00d03c03c03c03c03c03c03c03c03c01601601601601601603c016,l2C 91 6 1 [w99,w98,w101,w97,w96] 0x451,l2C 15 4 0 [w6,w4,w102,w3] 0x0,l2C 15 4 1 [w6,w4,w102,w3] 0x453,l2C 85 4 0 [w83,w81,w86,w80] 0xd01700d01700d00000000101700101700100100d00100d001,l2C 85 4 1 [w83,w81,w86,w80] 0x455,l2C 31 5 1 [w24,w23,w104,w26,w21,w103] 0x0,l2C 95 6 0 [w111,w110,w109,w108,w107,w106,w105] 0x2e2013026000095000000,l2C 95 7 0 (w111::w110::w109::w112::v4) 0x45716616616645806f00005935016616616606f16616600016603c00000903600906f00900903c00906f16616616603c1504570a603615003603606f06f06f1504561661661661500593511b51b506f1b51b51661b51b503c1b54541b51b51501b5,l2C 31 5 1 [w25,w24,w104,w26,w21,w113] 0x0,l2C 85 4 0 (w83::v1) 0xd01700d01700d00000000000000801700801700800800d00800d008000000,l2C 85 4 1 (w83::v1) 0x45b,l2C 95 6 0 [w111,w110,w109,w108,w105,w115,w114] 0x2e301406a000090000000,l2C 95 7 0 (w111::w110::w109::w112::v5) 0x593520004570c300016716716700016716745d1671671670c31670270360270c302702703c0270c303c00016716716703c0f90361510360360c30c30c315145c15145a1671671671510593531861860c318618616718618603c186454186186151186,l2C 90 4 0 [w119,w118,w117,w116] 0x6006,l2C 90 4 1 [w119,w118,w117,w116] 0x45f,l2C 15 3 1 [w6,w4,w102,w3] 0x0,l2C 82 3 1 [w123,w122,w121,w120] 0x0,l2C 82 3 1 [w124,w122,w121,w120] 0x0,l2C 95 7 0 (w126::w110::w125::v6) 0x46146146100003303303303303303345403303303303303303345403303300046345446100046245446103303346003303303307d07d07d07d45407d07d07d07d07d45407d03303303303307d03307d01726609c09c09c09c45409c09c09c09c09c45409c03303303303309c03309c00d08c07d07d2e107d,l2C 95 6 0 [w126,w111,w109,w108,w128,w127,w105] 0x2e0013029000000095000,l2C 95 7 0 (w126::w111::w109::w112::v7) 0x45a16416416446506f00003634c16416416406f16416400016403c00000905900906f00900903c00906f16416416403c1b41b406f1b41b41641b41b403c1b44541b41b417c1b417c45a03105917c05905906f06f06f17c45616416416417c03634d,l2C 95 6 0 [w126,w111,w109,w108,w105,w130,w129] 0x27b01404e000000090000,l2C 95 7 0 (w126::w111::w109::w112::v8) 0x3634e00045a0c30001651651650001651654671651651650c31650270590270c302702703c0270c303c00016516516503c1231230c312312316512312303c12345412312317d1230d005917d0590590c30c30c317d45c17d45716516516517d03634f,l2C 91 5 0 [w99,w98,w97,w96,w131] 0x618500000000d00d000000090090000090,l2C 91 5 0 [w99,w98,w97,w132,w96] 0x618400d00d000000095095000095,l2C 91 6 0 [w99,w98,w133,w97,w96] 0x600600600646a00600600600600646900600000d00000d00000d00000d00600d00d00600d00d03c03c03c03c03c03c03c03c03c03c03c03c03c03c016016016,l2C 91 6 1 [w99,w98,w133,w97,w96] 0x46b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB3 : Array L2Cell := #[l2C 21 3 1 [w12,w11,w10,w134] 0x0,l2C 87 6 0 [w94,w93,w92,w91,w135,w90] 0x1400000001400046d00600600600000000600001d00001d000000006006006000006000000006006006000006,l2C 87 6 1 [w94,w93,w92,w91,w135,w90] 0x46e01d,l2C 69 3 1 [w139,w138,w137,w136] 0x0,l2C 87 6 0 [w94,w93,w92,w91,w90,w140] 0x600600001300001300047000000600600000001d00001d000000006006006000000006006000006006000006,l2C 87 6 1 [w94,w93,w92,w91,w90,w140] 0x47101d,l2C 31 5 0 [w25,w24,w23,w141,w21] 0x8008000000000000000000,l2C 31 5 1 [w25,w24,w23,w141,w21] 0x473,l2C 91 4 1 [w99,w98,w97,w96,w142] 0x0,l2C 95 6 0 [w126,w111,w110,w109,w108,w105,w143] 0x33039000475,l2C 95 7 0 [w126,w111,w110,w109,w108,w105,w144] 0x510510004760140900140900000904740140270c30c30270110900000110320320000320c30c30320000792920330330c303303303301d01d09003345401d0330330320330330330790330790790000790c30c3079000032293032079032032032,l2C 79 5 0 [w149,w148,w147,w146,w145] 0x1001000000000000000000,l2C 79 5 1 [w149,w148,w147,w146,w145] 0x478,l2C 95 7 0 [w126,w111,w110,w109,w108,w150,w105] 0x47605105106609500006601309501309500009547901300906f06f00906900006906900006906f06f07829203303306f03303303301d01d09503345401d03303306903303303307803307800007807800007806f06f069293069078069069069,l2C 85 4 1 [w87,w84,w82,w151,w80] 0x8,l2C 95 7 0 (w126::w111::w110::w109::w112::v9) 0xc305147647b03c00003c02700000900004100003645a00000003946105945700000011c,l2C 95 8 0 (w126::w111::w110::w109::v6) 0xc306f47c0c305105105105105105147a0510510510510510514770510510c302703c03c03c4720c302706f00903c03c03c46f06f00905102f05102f05105105105103c46c05102f0c30360360364680c306f03603603646606f0510510510510510510360510360592920c30330330c306f03303306f05105103305105105103303303303301d01d03303c03346403301d0330330330330330360330330330330330330330590330330c305905905945e0c306f05905905945906f051051051051051051059051036036293036036036059036036036036,l2C 91 5 1 [w99,w98,w97,w96,w131] 0x469,l2C 85 5 0 (w87::v2) 0x800800800800800800800800100100100100800800800800100100100100d00d00d00d,l2C 81 3 1 [w156,w155,w154,w153] 0x0,l2C 85 5 0 [w87,w84,w82,w80,w157] 0xd00000000d00d000480000480000000000480,l2C 85 5 1 [w87,w84,w82,w80,w157] 0x48147f,l2C 93 5 1 [w162,w161,w160,w159,w158] 0x48201d,l2C 31 5 0 [w163,w25,w24,w23,w21] 0x8008000000014014000000,l2C 31 5 1 [w163,w25,w24,w23,w21] 0x484,l2C 95 7 0 [w126,w111,w110,w108,w105,w114] 0x6a05421d00048500000048300006a06a06a06a00047e09000047409006a06a06a06a00009000009003b03b01d03b03b01d06a06a06a06a03b06a03b03b03b03b03b03b03b03b03b47e03b03b03b03b03b03b07903b07901409106a06a04606a079079079079079079079079,l2C 95 7 0 [w126,w111,w110,w164,w108,w105,w114] 0x5421d00002600002606a00005400000005406a09106a06a05405406a06a0061b80061b806a00605409000605403b01d03b01d06a03b03b03b03b03b03b03b00603b03b07901409109107906a046046,l2C 91 5 0 [w99,w98,w97,w165,w96] 0x600600d00d000000006006006006006006006006,l2C 91 5 0 [w167,w99,w98,w97,w166,w96] 0xd000006000,l2C 91 5 0 [w167,w99,w98,w97,w96,w168] 0xd00d301000,l2C 91 6 0 [w167,w99,w98,w97,w96] 0x48a00000000048900018500600600600618500600600d00600600d006006185006006185006185006185006016185006006185006469006006006006006488006,l2C 91 6 1 [w167,w99,w98,w97,w96] 0x48b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB4 : Array L2Cell := #[l2C 91 5 1 [w99,w98,w97,w132,w96] 0x46a,l2C 79 5 0 [w169,w149,w148,w147,w145] 0x1001000000013013000000,l2C 79 5 1 [w169,w149,w148,w147,w145] 0x48e,l2C 95 7 0 [w126,w111,w110,w108,w106,w105] 0x48f00048300002602602602602605423200009500009500048d09500047909502602602602603a03a03a03a03a03a01d03a03a01d02602602602603a02603a03a03a03a03a48d03a03a03a03a03a03a07803a07807807807807801321c026026048026078078078078,l2C 95 7 0 [w126,w111,w110,w164,w108,w106,w105] 0x6a00000006a02600005423205402605402602602600005400005402621c0061b80061b802600605409500605403a01d03a01d02603a03a03a03a03a03a03a00603a03a07801321c21c078026048048,l2C 91 5 0 [w99,w98,w170,w97,w166,w96] 0xd30100000000d,l2C 91 5 0 [w99,w98,w170,w97,w96,w168] 0x600000d,l2C 91 5 0 [w99,w98,w97,w96,w171] 0x600600000000000000d00d000000006006006006006006006006,l2C 91 6 0 [w99,w98,w170,w97,w96] 0x600646a00600600600649400600000049300000000049200000600600d00600600d184006006006006184006184006184006006184006006184006016184006006184,l2C 91 6 1 [w99,w98,w170,w97,w96] 0x495,l2C 15 3 1 [w6,w4,w173,w172] 0x0,l2C 15 3 1 [w6,w5,w174,w4] 0x0,l2C 15 3 1 [w6,w5,w4,w172] 0x0,l2C 95 7 0 (w126::w111::w110::w164::v9) 0x261f606a09206a02606a06a06a02602600002600000005405449900048305406a06a06a0000001b80001b806a00002600049800003901d03901d06a03902603903903903903949703903913313305913305906a133026133041041,l2C 95 8 0 [w126,w111,w110,w164,w108,w105] 0x6a02649a06a05449602649149002606a05448c48748606a06a1b846c06a0261b846c02605446c1b800646c1b806a01d01d06a02601d01d02601d01d01d01d01d01d01d01d01d01d01d46c01d01d01d01d01d01d05901d06a05905906a02605905902602f02f02f1b80590591b8,l2C 87 5 0 [w92,w177,w91,w176,w90,w175] 0x7a000000000000000,l2C 85 4 0 [w84,w81,w85,w89] 0x1017001017001008017008017008008001008001008000000000000000000,l2C 85 4 1 [w84,w81,w85,w89] 0x49d,l2C 87 6 0 [w93,w92,w91,w176,w90,w175] 0x542b401401301401301401400001400000001300001300000000000049e0542b50000000000000000000000001d61d61d61d61d61d61d61d61d61d649c1d6,l2C 87 6 1 [w93,w92,w91,w176,w90,w175] 0x49f,l2C 91 5 0 [w179,w101,w97,w178,w96] 0x5d00605d00005d00000003c03c00600600600000600600000600d00d000000000006,l2C 91 5 1 [w179,w101,w97,w178,w96] 0x4a1,l2C 87 5 0 [w180,w92,w91,w176,w90] 0x11d35b05d05d0060060172e70170171b5017,l2C 87 5 1 [w180,w92,w91,w176,w90] 0x4a3,l2C 79 5 0 (w149::w182::v10) 0x3e03e001000000000001001001,l2C 79 5 1 (w149::w182::v10) 0x4a5,l2C 87 5 0 [w184,w92,w91,w176,w90,w183] 0x803e00003e000017,l2C 87 5 1 [w184,w92,w91,w176,w90,w183] 0x4a703a,l2C 79 5 0 [w149,w181,w147,w185,w145] 0x3e03e000000000000000000000000000000000001001,l2C 79 5 1 [w149,w181,w147,w185,w145] 0x4a9,l2C 87 5 1 [w184,w92,w91,w176,w135,w90] 0x3a,l2C 79 5 0 (w149::w181::v11) 0x3e03e000000000000000000000000000000000000000001001]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB5 : Array L2Cell := #[l2C 79 5 1 (w149::w181::v11) 0x4ac,l2C 95 6 0 [w187,w110,w112,w107,w105,w152] 0x1535705919b0a619b1d50001d51d50001d51d51d519b1d500000019b0001d51d51d500001701719b0000001d5000000,l2C 79 5 0 [w149,w181,w147,w188,w145] 0x10000000000a600003e03e0a6000001001,l2C 79 5 1 [w149,w181,w147,w188,w145] 0x4af,l2C 87 5 1 [w184,w92,w91,w90,w189] 0x482,l2C 95 6 0 [w187,w110,w112,w108,w107,w105,w190] 0xa60000002e4063000000267,l2C 85 5 0 (w191::w87::v2) 0x1700801700800000000000000000d00000d000000000000001008001008000000,l2C 85 5 1 (w191::w87::v2) 0x4b347f,l2C 87 5 1 (w192::w184::v3) 0x4b4,l2C 95 7 0 (w187::w110::w112::v4) 0x19b0a64b54b24b119b0630630630634b006319b0150150154ae19b0150592e80630630630630630630150630630630630630634ad06306319b2674a219b0a62674ab2670150150150154a20150630630630630630634aa06319b0174a819b01503a01d0150150150150150170150150150630634a60630630632670174a44a2454267,l2C 95 6 0 (w110::w193::w125::w112::v4) 0x2002000000d0001b50002e7,l2C 94 5 0 [w198,w197,w196,w195,w194] 0x11000611000011000000003c03c006006006000006006000006017017000000000006,l2C 94 5 1 [w198,w197,w196,w195,w194] 0x4b8,l2C 94 5 0 [w198,w197,w196,w194,w199] 0x3c03c000000000000006006006000006110110000110006006000006017017000000000006,l2C 94 5 1 [w198,w197,w196,w194,w199] 0x4ba,l2C 79 5 0 [w149,w147,w201,w200,w145] 0x44044001000000000000000001001001000000,l2C 79 5 1 [w149,w147,w201,w200,w145] 0x4bc,l2C 91 5 1 [w99,w98,w101,w178,w96,w202] 0x0,l2C 79 5 0 [w149,w147,w200,w188,w145] 0x1001044044000000,l2C 79 5 1 [w149,w147,w200,w188,w145] 0x4bf,l2C 95 7 0 (w126::w110::w193::w112::v4) 0x6000000006004d18704d1871874c048d04d0204be09c35818718718702018718700018700000d00000d0200004bd1871504bb1500361500360200200201504b918715003a35909c00002035a02009c02002018718718709c09c09c4b709c454150150,l2C 94 5 0 [w205,w204,w196,w194,w203] 0x6185000000000090017017000000090090,l2C 94 5 0 [w205,w204,w196,w206,w194] 0x6184000095017017000000095095,l2C 94 6 0 [w205,w204,w207,w196,w194] 0x60060060064c30060060060060064c200603c03c03c03c03c03c03c03c05405405400001700001700001700001700600601700600600603c03c03c03c03c03c,l2C 94 6 1 [w205,w204,w207,w196,w194] 0x4c4,l2C 87 5 0 [w184,w92,w176,w208,w90] 0x5d05405d05405d00600003e2e500005d00605d017017006006006000456,l2C 87 5 0 [w94,w177,w176,w208,w90] 0x1611001611001600d00d0060000001100061100442e6006006000006456,l2C 84 3 1 [w212,w211,w210,w209] 0x0,l2C 87 6 0 [w94,w93,w92,w176,w208,w90] 0x4c80004800160540160540160060000132e50000160060161f41f41f41f41f41f40061f44c70060000000540060540132e60060060060064561f41f41f40064c6,l2C 87 6 1 [w94,w93,w92,w176,w208,w90] 0x4c9,l2C 95 7 0 [w126,w111,w110,w112,w108,w107,w213,w105] 0x480001590060003540a61504ab159,l2C 85 5 0 [w87,w84,w82,w214,w80] 0x800000000800000001700101700100000000000000000000000000100d00100d000000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB6 : Array L2Cell := #[l2C 85 5 1 [w87,w84,w82,w214,w80] 0x4cc47f,l2C 31 5 1 [w25,w24,w23,w26,w103,w113] 0x0,l2C 79 5 1 [w149,w148,w147,w217,w216,w215] 0x0,l2C 95 7 0 [w126,w111,w110,w112,w108,w107,w105,w130] 0xd00a60000d00274cf02e0000094ce4be0480000360000004bb4a2059000000457,l2C 95 6 0 [w126,w111,w110,w108,w107,w105,w218] 0x1400000003a000000,l2C 95 7 0 [w126,w111,w110,w108,w107,w105,w144] 0x480480140000140000004d14830140270fb0fb0270110110000110fb0fb07923200000000003200003201100003a03a0fb03a03a01d03a01d01103a03a03a00003a03a03a07903a4ad0790790000790fb0fb01121c011079011011079000,l2C 95 6 0 [w126,w111,w110,w107,w105,w152,w143] 0xd901406606611100000000049e,l2C 95 6 0 [w126,w111,w110,w107,w106,w105,w152] 0x540000780a60000000c4,l2C 95 7 0 [w126,w111,w110,w112,w107,w105,w152] 0x93550270590270fb0270270a60270fb0271681681684d41681684d31681681680fb1680004ce0fb4be0000001681681680001111110fb1111111111111681111114be1111111111331114ae0000591330590fb0fb0fb13349e009356168168168133133000,l2C 95 6 0 [w126,w111,w110,w108,w107,w219,w105] 0x2f048054095000000000000013000,l2C 95 6 0 [w126,w111,w110,w108,w106,w105,w190] 0x2f000000000095000,l2C 78 3 1 [w223,w222,w221,w220] 0x0,l2C 95 7 0 [w126,w111,w110,w108,w107,w106,w105] 0x4d84d10000a64d70a604804802f0264d40540262e20780264d60000a60950000950264ca03a03a03a03a03a03a02603a03a03a4c003a03a03a07803a4b00784a00130c40c4026026026078026026078458,l2C 95 7 0 [w126,w111,w110,w112,w108,w107,w105,w190] 0x270a60fb4804d72e40484d10001504b2233,l2C 95 8 0 (w126::w111::w110::w112::v4) 0xfb0270a64b44da4820fb02704802f04802f0480480480484d949004802f0fb0090090094d50fb0090592320480480480480480480090480480480480480484d20480480fb1504d00fb0a64cd1500364cb46f1500360090090090094ca0090480480480480480484c50480fb03a03a0fb03a03a03a01d03a03a03a01d00900900900903a00904804803a04804804803a03a03a03a03a4c103a03a03a03a03a03a03a05903a4b603a0fb0590590594a00fb00900921c009009009059009009009048048048048048048059048150059059059459150,l2C 91 5 0 [w179,w101,w97,w96,w224] 0x3c03c00000000000000600600600000605d05d00005d00600600000600d00d000000000006,l2C 91 5 1 [w179,w101,w97,w96,w224] 0x4dc,l2C 87 5 0 [w180,w92,w91,w90,w175] 0x11d36400000000000005d05d0060060172f5017017186017,l2C 87 5 1 [w180,w92,w91,w90,w175] 0x4de,l2C 31 5 0 [w25,w225,w27,w23,w21] 0x5a05a008000000000008008008,l2C 31 5 1 [w25,w225,w27,w23,w21] 0x4e0,l2C 87 5 0 [w184,w92,w91,w226,w90,w175] 0x105a00005a000017,l2C 87 5 1 [w184,w92,w91,w226,w90,w175] 0x4e203b,l2C 31 5 0 [w25,w27,w23,w29,w21] 0x5a05a000000000000000000000000000000000008008,l2C 31 5 1 [w25,w27,w23,w29,w21] 0x4e4,l2C 87 5 1 [w184,w92,w91,w90,w175,w140] 0x3b,l2C 31 5 0 [w25,w27,w23,w22,w21] 0x80000000000f900005a05a0f9000008008,l2C 31 5 1 [w25,w27,w23,w22,w21] 0x4e7,l2C 31 5 0 [w25,w27,w23,w21,w30] 0x5a05a000000000000000000000000000000000000000008008,l2C 31 5 1 [w25,w27,w23,w21,w30] 0x4e9,l2C 95 6 0 [w187,w110,w112,w108,w115,w152] 0x5918a0612f10f918a13413413418a13413400013413400000000018a00013413413400001701718a000000134000000,l2C 95 6 0 [w187,w110,w112,w108,w105,w115,w190] 0x2ee0f906200000000000026a]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB7 : Array L2Cell := #[l2C 85 5 0 [w87,w84,w227,w82,w80] 0x1700801700800000000000000000000000000000d00000d000000008001008001000000,l2C 85 5 1 [w87,w84,w227,w82,w80] 0x4ed47f,l2C 87 5 1 [w184,w92,w228,w91,w90] 0x4ee,l2C 95 7 0 (w187::w110::w112::v5) 0x610592bc0f94ef18a4ec4b118a0610610610614eb0610620620620620620624ea0620620620620624e80620620620620620620610620620f926a4e626a0610610610614dd06118a26a4dd18a0620620620620620624e506206103b01d06106106106106101706106106118a0174e318a0620624e106206206226a0174df4dd45426a,l2C 95 6 0 (w110::w193::w125::w112::v5) 0x6006000000d0001860002f5,l2C 31 5 0 [w25,w23,w229,w28,w21] 0x7a07a008000000000000000008008008000000,l2C 31 5 1 [w25,w23,w229,w28,w21] 0x4f2,l2C 31 5 0 [w25,w23,w28,w22,w21] 0x800807a07a000000,l2C 31 5 1 [w25,w23,w28,w22,w21] 0x4f4,l2C 91 5 1 [w99,w98,w101,w97,w224,w202] 0x0,l2C 95 7 0 (w126::w110::w193::w112::v5) 0x9c2f20000200000200604f611211211200011211204d04d4f511247e04d11211206011200000d00000d0600004f31121510361510360600600601514bb1514b911215103b2f30602f406009c06006009c00011211211209c09c09c4f109c454151151,l2C 95 7 0 [w126,w111,w110,w112,w108,w128,w105,w115] 0xf90310000f90274cf0460000094ce4f60450000360000004b94dd05900000045a,l2C 87 5 0 [w184,w92,w91,w175,w230] 0x5d05405d05405d00000000000005a2b900005d00605d00600001701700600600600045c,l2C 87 5 0 [w94,w177,w91,w175,w230] 0x1611001611001600000000000000d00d00011000611007a2ef00600000600600000645c,l2C 87 6 0 [w94,w93,w92,w91,w175,w230] 0x160540160540160004c80004800142b90000160060160060001f51f51f51f51f51f50061f54fa0000540060540142ef00600000600600600645c1f51f51f50064f9,l2C 87 6 1 [w94,w93,w92,w91,w175,w230] 0x4fb,l2C 95 7 0 [w126,w111,w110,w112,w108,w105,w115,w231] 0x2ed3630460000060000f91514e62ed,l2C 85 5 0 [w87,w84,w82,w232,w80] 0x1700801700800000000000100000100000000000000000000800d00800d000000000000,l2C 85 5 1 [w87,w84,w82,w232,w80] 0x4fe47f,l2C 95 6 0 [w126,w111,w110,w108,w233,w105,w115] 0x2f046054090000000000000014000,l2C 95 6 0 [w126,w111,w110,w108,w115,w114,w152] 0x540790000f90002bb000,l2C 95 6 0 [w126,w111,w110,w108,w105,w114,w190] 0x2f000000000090000,l2C 95 6 0 [w126,w111,w110,w108,w105,w115,w218] 0x1300000003b000000,l2C 30 3 1 [w237,w236,w235,w234] 0x0,l2C 95 7 0 [w126,w111,w110,w108,w105,w115,w114] 0x4604602f05406a2e307906a5045030f90005020f906a5015000000f909000009006a4fc03b03b03b03b03b03b06a03b03b03b4f503b03b03b07903b4e80142bb2bb06a06a06a07906a06a0794a007945d,l2C 95 7 0 [w126,w111,w110,w108,w150,w105,w115] 0x7821d0000000130135030004830130660660660000bc0090bc0090660bc04604600006900006906600000000003b01d03b01d06603b03b03b0bc03b03b03b00003b03b03b07803b4ea0660910660780660660780780000780bc0bc078000,l2C 95 6 0 [w126,w111,w110,w108,w115,w152,w143] 0x1301126b01119f00000000049e,l2C 95 7 0 [w126,w111,w110,w112,w108,w115,w152] 0x90590090bc0090272f00f90090bc0090090e20e20e20bc0e20e25070e20e20e25010e20004cf0000000bc4f60e20e20e200019f19f19f19f0bc19f19f0e219f19f4f619f19f19f13319f4eb0000591330590272ba0bc0bc0bc13349e0e20e20e2133133000,l2C 95 7 0 [w126,w111,w110,w112,w108,w105,w115,w190] 0x2b82ee0f90bc0465034805020001514ec2b8,l2C 95 8 0 (w126::w111::w110::w112::v5) 0x2705921d0f94ee0bc0095094820bc00902702702702750802704604604604604604650604604604604604602f02f04650504648604602f0460460460460460270460460f94ff1510364fd4721510360270270270274fc0270bc1514f80bc0460460460460460464c504603b03b03b01d03b03b03b01d02702702702703b0270bc03b03b0bc04604603b04604604603b03b03b03b03b4f703b03b03b03b03b03b03b05903b4f003b0270270910270270270590270270270bc0590590594a00bc04604604604604604605904615105905905945e151,l2C 95 6 0 (w126::w187::w125::w112::v7) 0x150150000170001b40002b6,l2C 95 6 0 (w126::w187::w125::w112::v8) 0x610610000170001230002f9]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB8 : Array L2Cell := #[l2C 95 7 0 (w126::w187::w110::w125::v6) 0xe30e30e30000e30e30000e306100000006101500000001504c0e30004600e304c0e304c07d50c07d50b0e30e30e307d0173060000170000170000170000170330e30174600e30330e303307d30707d07d01701707d07d09c4dd09c4a20e309c00d08c08c09c07d033033,l2C 94 5 0 [w239,w204,w196,w194,w238] 0x11d11d000000090090017017017017090017,l2C 94 5 0 [w239,w204,w196,w240,w194] 0x11d11d095095017017017017095017,l2C 94 5 0 [w239,w204,w197,w196,w194,w241] 0x11d00000003c,l2C 94 6 0 [w239,w204,w197,w196,w194] 0x51000011d00600600600600650f11d00600611d00600650e00611d03c03c03c03c03c03c03c03c11d03c03c03c03c00603c11d01701701701701701701701711d00601700611d00603c03c017,l2C 94 6 1 [w239,w204,w197,w196,w194] 0x511,l2C 94 5 0 [w205,w242,w196,w194] 0x1701701701700001701701701701700001716f110110017460017,l2C 94 5 0 [w205,w204,w196,w243,w194] 0x17017000000000000017000054054017017017017000017,l2C 94 5 0 [w205,w204,w196,w194,w244] 0x17017000000000000000000000000054054017017017000017017000017,l2C 26 3 1 [w247,w246,w245] 0x0,l2C 74 3 1 [w250,w249,w248] 0x0,l2C 78 3 1 [w251,w222,w221,w220] 0x0,l2C 30 3 1 [w252,w236,w235,w234] 0x0,l2C 94 5 0 [w253,w205,w204,w196,w194,w241] 0x16f017000000000017000000000000,l2C 94 6 0 [w253,w205,w204,w196,w194] 0x51951851a51951916f46016f51816f46016f01701701701751701701701701701751601716f01701701701746001716f01701701701751501701701701701751401716f01701701701746001751316f054054054,l2C 94 6 1 [w253,w205,w204,w196,w194] 0x51b,l2C 87 5 0 [w184,w254,w92,w91,w226,w90] 0x5d0000011d900001703a,l2C 87 5 0 [w94,w92,w255,w91,w226,w90] 0x3e03e00005d017,l2C 22 3 1 [w259,w258,w257,w256] 0x0,l2C 84 3 1 [w212,w260,w211,w210] 0x0,l2C 87 5 0 [w94,w184,w92,w226,w90,w261] 0x5a05a0000002fe,l2C 87 6 0 [w94,w184,w92,w91,w226,w90] 0x5a00000005a00052101721e52005d00005d00051f01700003e1f903e01703e01701751e0174e20011f91f901703a51d01703a03a,l2C 87 6 1 [w94,w184,w92,w91,w226,w90] 0x52201d,l2C 87 5 0 [w184,w254,w92,w91,w90,w183] 0x5d00000807200001703b,l2C 87 5 0 [w94,w92,w255,w91,w90,w183] 0x5a05a00005d017,l2C 70 3 1 [w265,w264,w263,w262] 0x0,l2C 84 3 1 [w212,w211,w266,w210] 0x0,l2C 87 5 0 [w94,w184,w92,w91,w183,w261] 0x3e03e000370000,l2C 87 6 0 [w94,w184,w92,w91,w90,w183] 0x1723600003e00003e00052852705d00005d00052605a1a205a01705a0170170000175250081a21a201703b0174a752401703b03b,l2C 87 6 1 [w94,w184,w92,w91,w90,w183] 0x52901d,l2C 94 5 1 [w205,w204,w197,w195,w194,w241] 0x0,l2C 94 5 1 [w205,w204,w196,w206,w194] 0x4c3]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB9 : Array L2Cell := #[l2C 95 7 0 (w126::w187::w110::w112::v7) 0x6100000006104c18804c1881884aa52c04c01552b07d36018818818801518818800018807d00001536101507d01501518818818807d0000170000170150004a618807d07d07d50b45417c4dd17c05917c05901501501517c4a218817c07d17c02b35f,l2C 94 5 1 [w205,w204,w196,w194,w203] 0x4c2,l2C 94 5 1 [w205,w204,w197,w196,w199,w241] 0x0,l2C 95 7 0 (w126::w187::w110::w112::v8) 0x7d36900001500001506152f16c16c16c00016c16c04c04c4e516c52e04c16c16c06116c0612f806107d06106107d00016c16c16c07d0000170000170610004e116c07d07d07d50c45417d05917d05906106106117d4dd17d4a216c17d07d17d01b36a,l2C 94 5 1 [w239,w204,w196,w194,w238] 0x50e,l2C 31 5 0 [w25,w27,w23,w267,w21] 0x5a05a00005a05a00000005a00000000000005a000008291,l2C 31 5 1 [w25,w27,w23,w267,w21] 0x532,l2C 31 5 0 [w268,w25,w27,w23,w21] 0x5a05a05a00000000000005a00000000829105a00000005a,l2C 31 5 1 [w268,w25,w27,w23,w21] 0x534,l2C 95 7 0 [w126,w187,w110,w108,w105,w144] 0x4c04c04c05a5350ab0004ea0ab06106106106105a53325000052e2500610610610610ab2500000ab05a01701700005a0170610610610610ab0170000ab2500175310004542500790790790790790790610610610610610610ab0790790794ad0ab25007907925001d01d27c,l2C 94 5 1 [w239,w204,w196,w240,w194] 0x50f,l2C 79 5 0 [w149,w181,w147,w269,w145] 0x3e03e00003e03e00000003e00000000000003e00000118e,l2C 79 5 1 [w149,w181,w147,w269,w145] 0x538,l2C 79 5 0 (w270::w149::v10) 0x3e03e03e00000000000003e00000000118e03e00000003e,l2C 79 5 1 (w270::w149::v10) 0x53a,l2C 95 7 0 [w126,w187,w110,w108,w150,w105] 0x1fa03e53b0004ea1fa1fa0150151fa04c04c04c1fa24f0001fa03e53924f00052c24f0150150150151fa0170001fa03e01701700003e01701501501501524f01753700045424f1fa0780780784ea1fa07807807807807807801501501501501501524f07807824f01d01d27c,l2C 15 3 1 [w6,w271,w4,w3] 0x0,l2C 15 3 1 [w273,w6,w272,w4] 0x0,l2C 87 5 1 [w94,w184,w92,w226,w90,w261] 0x521,l2C 87 5 1 [w94,w184,w92,w91,w183,w261] 0x528,l2C 15 3 1 [w6,w272,w4,w274] 0x0,l2C 15 3 1 [w6,w272,w4,w3] 0x0,l2C 95 7 0 (w126::w187::w110::w112::v9) 0x152bf0612fd0610150610610610fd0fd0fd0150fd0fd04c04c5420fd4ea04c0fd0fd0610fd54207d00007d06152f01552b0fd0fd0fd54100001700001706154001553f53e0fd53d4611331330590590001334b10590610610611334eb0150150151334ae0fd1330392c0,l2C 95 8 0 (w126::w187::w110::v6) 0x6101554306104c04c04c04c04c04c53c04c04c04c04c04c04c53604c04c06107d53006101507d52d01504c04c04c04c04c04c4c504c06101752a06101501752301504c04c51c04c04c04c07d01751250d46407d0610590590594f00610150590590594b601504c04c04c04c05904c07d05905907d01d01d27c,l2C 95 7 0 (w126::w110::w193::w125::v6) 0xfe0fe0fe0000fe0fe0000fe06000000006002000000002004d0fe0004600fe04d0fe04d00000d00000d00000d00000d0330fe00d4600fe0330fe03309c30807d4bb07d4b90fe07d01726626603303309c4f109c4b70fe0fe0fe09c00d30900d09c00d09c09c09c07d07d,l2C 91 5 0 [w99,w275,w97,w96,w95] 0x18918900000000d00d00d00d09000d090090,l2C 91 5 0 [w99,w275,w97,w100,w96] 0x18918900d00d00d00d09500d095095,l2C 91 5 0 [w99,w275,w101,w97,w96,w202] 0x18900000003c,l2C 91 6 0 [w99,w275,w101,w97,w96] 0x54800018900d00d00d00d00d54718900d00d18900d00d54600d18900d00d00d00d00d00d00d00d18900d00d00d18900d03c03c00d03c03c03c03c03c03c03c03c18903c03c03c03c00d03c189,l2C 91 6 1 [w99,w275,w101,w97,w96] 0x549,l2C 87 5 0 [w94,w276,w91,w208,w90] 0x1892b700d2b600d00d11011000600600d1b4,l2C 87 5 1 [w94,w276,w91,w208,w90] 0x54b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB10 : Array L2Cell := #[l2C 87 5 1 [w94,w177,w91,w208,w135,w90] 0x2b,l2C 87 5 0 [w94,w177,w91,w208,w90,w277] 0x804400004400000d,l2C 87 5 1 [w94,w177,w91,w208,w90,w277] 0x54e02b,l2C 79 5 0 [w149,w147,w200,w145,w186] 0x44044000000000000000000000000000001001000000000000,l2C 79 5 1 [w149,w147,w200,w145,w186] 0x550,l2C 95 6 0 [w126,w193,w112,w128,w105,w152] 0x2035e03619e03119e1d70001d71d70001d71d71d719e1d700d00d19e0000001d700000019e0001d71d71d7000000000,l2C 79 5 0 [w149,w147,w200,w185,w145] 0x1000031000044044001001000000000000031000,l2C 79 5 1 [w149,w147,w200,w185,w145] 0x553,l2C 85 5 0 [w87,w84,w82,w80,w278] 0x170000000170170004c80004c80004c8,l2C 85 5 1 [w87,w84,w82,w80,w278] 0x55547f,l2C 87 5 1 [w94,w177,w91,w90,w279] 0x556,l2C 95 6 0 [w126,w193,w112,w108,w128,w105,w280] 0x310000002e90bb000000269,l2C 85 5 0 (w281::w87::v2) 0xd00800d008000000001008001008000000000000000000000017000017000000,l2C 85 5 1 (w281::w87::v2) 0x55947f,l2C 87 5 1 [w282,w94,w177,w91,w90] 0x55a,l2C 95 7 0 (w126::w193::w112::v7) 0x19e03155b55855719e0bb0bb0bb0bb5540bb19e02002002055219e0200363620bb0bb0bb0bb0bb0bb0200bb0bb0bb0bb0bb0bb5510bb0bb19e00d54f19e02002b01d02002002002002000d0200200200bb0bb4bd0bb0bb0bb19e2694b919e03126954d2690200200200204b90200bb0bb0bb0bb0bb0bb4c00bb00d54c2694b9454269,l2C 85 4 0 (w87::w283::v1) 0xd008017000,l2C 85 5 0 (w87::w283::v0) 0xd00d00000000000000000d00800d00800d00800d00001701700055d00d43d,l2C 85 5 1 (w87::w283::v0) 0x55e,l2C 87 5 1 [w94,w276,w91,w90,w230] 0x55f,l2C 87 5 1 [w94,w177,w91,w90,w230,w140] 0x1b,l2C 87 5 0 [w94,w177,w91,w284,w90,w230] 0x107a00007a00000d,l2C 87 5 1 [w94,w177,w91,w284,w90,w230] 0x56201b,l2C 31 5 0 [w25,w23,w28,w29,w21] 0x80000d000007a07a0080080000000000000d0000,l2C 31 5 1 [w25,w23,w28,w29,w21] 0x564,l2C 31 5 0 [w25,w23,w28,w21,w30] 0x7a07a000000000000000000000000000008008000000000000,l2C 31 5 1 [w25,w23,w28,w21,w30] 0x566,l2C 95 6 0 [w126,w193,w112,w108,w130,w152] 0x361a10603680d01a11d81d81d81a11d81d80001d81d800000d00d1a10000001d80000001a10001d81d81d8000000000,l2C 95 6 0 [w126,w193,w112,w108,w105,w130,w280] 0x2f70d008300000000000026c,l2C 85 5 0 [w87,w84,w285,w82,w80] 0xd00800d008000000000000000000008001008001000000000000000017000017000000,l2C 85 5 1 [w87,w84,w285,w82,w80] 0x56a47f,l2C 87 5 1 [w94,w177,w286,w91,w90] 0x56b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB11 : Array L2Cell := #[l2C 95 7 0 (w126::w193::w112::v8) 0x600362fa0d056c1a15695571a106006006006056806008308308308308308356708308308308308356508308308308308308306008308306001b01d06006006006006000d0600600601a100d5631a10830834f30830830830d026c56126c0600600600604bb0601a126c4bb1a10830830830830830834f508300d56026c4bb45426c,l2C 75 3 1 [w290,w289,w288,w287] 0x0,l2C 27 3 1 [w20,w291,w19,w17] 0x0,l2C 91 5 0 [w98,w292,w97,w96] 0xd00d00d00d00000d00d00d00d00d00000d16f05d05d00d46000d,l2C 91 5 0 [w99,w98,w97,w293,w96] 0xd00d00d00001601600d00d00d00d00000d000000000000,l2C 91 5 0 [w99,w98,w97,w96,w294] 0xd00d00000000000001601600d00d00d00000d00d00000d000000000000,l2C 91 5 0 [w99,w295,w98,w97,w96,w202] 0xd00000000000d00000000000000016f,l2C 91 6 0 [w99,w295,w98,w97,w96] 0x56f56e57356f00d00d00d00d51700d00d00d00d00d51600d16f00d00d00d00d46000d16f00d00d00d00d57200d00d00d00d00d57100d01601601616f00d00d00d00d46000d57016f56f16f46016f56e16f46016f,l2C 91 6 1 [w99,w295,w98,w97,w96] 0x574,l2C 87 5 0 [w296,w94,w177,w91,w284,w90] 0x11000000d00123400002b,l2C 87 5 0 [w94,w92,w255,w91,w284,w90] 0x4404400011000d,l2C 19 3 1 [w9,w8,w298,w297] 0x0,l2C 81 3 1 [w156,w299,w155,w154] 0x0,l2C 87 5 0 [w94,w92,w177,w284,w90,w261] 0x7a07a000000300,l2C 87 6 0 [w94,w92,w177,w91,w284,w90] 0x7a00000007a00057a00d08d00d0000441da04400d04400d00d5620011da1da00d02b02b02b57911000011000057800d57757600d,l2C 87 6 1 [w94,w92,w177,w91,w284,w90] 0x57b01d,l2C 87 5 0 [w296,w94,w177,w91,w90,w277] 0x11000000d0081f800001b,l2C 87 5 0 [w94,w92,w255,w91,w90,w277] 0x7a07a00011000d,l2C 67 3 1 [w303,w302,w301,w300] 0x0,l2C 81 3 1 [w156,w155,w304,w154] 0x0,l2C 87 5 0 [w94,w92,w177,w91,w277,w261] 0x440440002ff000,l2C 87 6 0 [w94,w92,w177,w91,w90,w277] 0xd16e00004400004400058107a08407a00d07a00d00d00000808408400d01b00d54e01b01b58011000011000057f00d57e57d00d,l2C 87 6 1 [w94,w92,w177,w91,w90,w277] 0x58201d,l2C 91 5 1 [w99,w275,w97,w96,w95] 0x546,l2C 31 5 0 [w25,w23,w28,w305,w21] 0x7a07a00007a00007a00000007a00000827a07a000000000,l2C 31 5 1 [w25,w23,w28,w305,w21] 0x585,l2C 31 5 0 [w268,w25,w23,w28,w21] 0x7a00000000827a07a00000000007a07a07a00000007a,l2C 31 5 1 [w268,w25,w23,w28,w21] 0x587,l2C 95 7 0 [w126,w110,w193,w108,w105,w144] 0x4d04d04d07a5881db0005671db06006006006007a00d00d00007a00d0600600600601db00d0001db0320320320320320320600600600600600601db0320320325511db01d01d26d07a58627e00047e27e0600600600601db27e0001db00d58427e00045427e032032032032,l2C 91 5 1 [w99,w275,w97,w100,w96] 0x547,l2C 79 5 0 [w149,w147,w200,w306,w145] 0x4404400004400004400000004400000113c044000000000,l2C 79 5 1 [w149,w147,w200,w306,w145] 0x58b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB12 : Array L2Cell := #[l2C 79 5 0 [w270,w149,w147,w200,w145] 0x4400000000113c044000000000044044044000000044,l2C 79 5 1 [w270,w149,w147,w200,w145] 0x58d,l2C 95 7 0 [w126,w110,w193,w108,w150,w105] 0x1fb04458e0005671fb1fb0200201fb04d04d04d1fb00d0001fb04400d00d00004400d0200200200201fb0690690695671fb06906906906906906902002002002002002001d01d26d1fb27d0001fb04458c27d00048d27d02002002002000d58a27d00045427d069069069069,l2C 15 3 1 [w6,w4,w307,w3] 0x0,l2C 15 3 1 [w6,w4,w173,w3] 0x0,l2C 15 3 1 [w308,w6,w4,w173] 0x0,l2C 87 5 1 [w94,w92,w177,w284,w90,w261] 0x57a,l2C 87 5 1 [w94,w92,w177,w91,w277,w261] 0x581,l2C 95 7 0 (w126::w110::w193::w112::v9) 0x2037106037306002006006006018d18d18d02018d18d04d04d59118d56704d18d18d06018d00000d00000d06059402059359218d11c11c03603600011c55703606006006011c56802002002011c55218d11c03937259109c00009c0604f60204be18d18d18d497590461,l2C 95 8 0 (w126::w110::w193::v6) 0x6002059506004d04d04d04d04d04d58f04d04d04d04d04d04d58904d04d06000d58306002000d57c02004d04d57504d04d04d06003603603656d06002003603603655c02004d04d04d04d03604d01d01d26d06009c4f706002009c4c102004d04d04d04d04d04d46c04d00d54a09c54546409c036036036036,l2C 93 5 1 [w162,w161,w160,w159,w309] 0x55601d,l2C 31 5 0 [w310,w25,w24,w23,w21] 0x14014000000000000000000008008000000000000,l2C 31 5 1 [w310,w25,w24,w23,w21] 0x598,l2C 95 7 0 [w126,w111,w110,w108,w105,w129] 0x4e01609600059900000059700004e04e04e04e03201418b04e04e02e04e03203203203201b01b01d01b01b01d04e04e04e04e01b04e01b01b01b01b01b01b01b01b03201b01b01b01b01b01b52e01b01b00052e09000047409004e04e04e04e000090000090032032032032,l2C 95 7 0 [w126,w111,w110,w311,w108,w105,w129] 0x1609600002900002904e00001600000001604e18b04e04e01601604e04e01418b18b03204e02e02e01b01d01b01d04e01b01b01b01b01b01b03201b01b00601b0061f70061f704e006016090006016,l2C 94 5 0 [w205,w204,w196,w312,w194] 0x6006006006006006006006017017000000006006,l2C 94 5 0 [w314,w205,w204,w196,w313,w194] 0x17000006000,l2C 94 5 0 [w314,w205,w204,w196,w194,w315] 0x17017301000,l2C 94 6 0 [w314,w205,w204,w196,w194] 0x600618500600618500618500618500605418500600618500000059e00000000059d0001850060060060061850060060170060060060064c200600600600600659c006,l2C 94 6 1 [w314,w205,w204,w196,w194] 0x59f,l2C 79 5 0 [w316,w149,w148,w147,w145] 0x13013000000000000000000001001000000000000,l2C 79 5 1 [w316,w149,w148,w147,w145] 0x5a1,l2C 95 7 0 [w126,w111,w110,w108,w127,w105] 0x5a200059700002902902902902901619c06906906906906901319d02902904502902b02b02b02b02b02b01d02b02b01d02902902902902b02902b02b02b02b06902b02b02b02b02b02b52c02b02b00009500009500052c095000479095029029029029069069069069,l2C 95 7 0 [w126,w111,w110,w311,w108,w127,w105] 0x4e00000004e02900001619c01602901602902902900001600001602919d01319d19d06902904504502b01d02b01d02902b02b02b02b02b02b06902b02b00602b0061f70061f7029006016095006016,l2C 94 5 0 [w205,w204,w317,w196,w313,w194] 0x17301000000017,l2C 94 5 0 [w205,w204,w317,w196,w194,w315] 0x6000017,l2C 94 5 0 [w205,w204,w196,w194,w318] 0x6006000000000000006006006006006006017017000000006006,l2C 94 6 0 [w205,w204,w317,w196,w194] 0x60064c30060060060065a70060061840061840060061840060061840060541840060061840000005a60000000005a5000006006017006006006184006006006006184,l2C 94 6 1 [w205,w204,w317,w196,w194] 0x5a8,l2C 15 3 1 [w6,w5,w4,w319] 0x0,l2C 15 3 1 [w6,w5,w4,w274] 0x0,l2C 95 7 0 (w126::w111::w110::w311::v9) 0x291f604e09204e02904e04e04e0290290000290000000160165ab00059701604e04e04e00011c03611c03604e11c02911c04104103901d03901d04e03902903903903903911c0390395410390001f70001f704e0000290005aa000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB13 : Array L2Cell := #[l2C 95 8 0 [w126,w111,w110,w311,w108,w105] 0x4e0295ac04e0165a90295a45a302904e0165a059b59a04e04e03603604e02903603602902f02f02f04e01d01d04e02901d01d02901d01d01d01d01d01d01d01d01d01d03601d01d01d01d01d01d4c501d01d04e1f74c504e0291f74c50290164c51f700646c1f7036036036036,l2C 95 7 0 [w126,w111,w110,w112,w108,w128,w213,w105] 0x4500029400600035c29454d03117c,l2C 85 5 0 [w87,w84,w82,w320,w80] 0x800000000800000000d00100d00100000000100d00100d000000000000000000000000,l2C 85 5 1 [w87,w84,w82,w320,w80] 0x5af47f,l2C 87 5 0 [w94,w184,w91,w208,w90,w230] 0x5a000000000000000,l2C 85 4 0 [w87,w86,w88,w89] 0x100d00100d00100800d00800d008008001008001008000000000000000000,l2C 85 4 1 [w87,w86,w88,w89] 0x5b2,l2C 87 6 0 [w94,w93,w91,w208,w90,w230] 0x162eb0140130140130140140000140000000130000130000000000005b30162ec1b61b61b61b61b61b61b61b60000000000000000000000001b61b61b65b1,l2C 87 6 1 [w94,w93,w91,w208,w90,w230] 0x5b4,l2C 95 6 0 [w126,w111,w110,w108,w128,w105,w321] 0x1400000002b000000,l2C 95 7 0 [w126,w111,w110,w108,w128,w105,w144] 0x450450140000140000005b65970140270fc0fc0270110110000110fc0fc03219c0320320000320fc0fc01119d01103201101102b02b0fc02b02b01d02b01d01102b02b02b03202b55102b02b00002b000000000079000079011000032000,l2C 95 6 0 [w126,w111,w110,w128,w105,w152,w143] 0xd90140660660000005b316a000,l2C 95 6 0 [w126,w111,w110,w128,w127,w105,w152] 0x1600006903100007b000,l2C 95 7 0 [w126,w111,w110,w112,w128,w105,w152] 0x935d0270360270fc0270270310270fc0271691691695b91691695b81691691690fc16900003611c0360fc0fc0fc11c5b30092ea16916916911c16a16a0fc16a16a16a16a16916a16a11c16a55216a16a52b16a0004ce0fc4f600000016916916900011c000,l2C 95 6 0 [w126,w111,w110,w108,w128,w322,w105] 0x2f045016013000000095000000000,l2C 95 6 0 [w126,w111,w110,w108,w127,w105,w280] 0x2f000000000000095,l2C 75 3 1 [w323,w290,w288,w287] 0x0,l2C 95 7 0 [w126,w111,w110,w108,w128,w127,w105] 0x5bd5b60000315bc03104504502f0295b90160292e00690290695b501307b07b02902902906902902902b02b02b02b02b02b02902b02b02b06902b55402b02b4aa02b5bb0000310950000950294ca069465,l2C 95 7 0 [w126,w111,w110,w112,w108,w128,w105,w280] 0x270310fc4c85bc2e90455b626855800017c,l2C 95 8 0 (w126::w111::w110::w112::v7) 0xfc02703155a5bf5560fc02704502f04502f0450450450455be5a304502f0fc0090090095ba0fc00903619c0450450450450450450090450450450450450455b70450450fc0360360365b50fc00900919d0090090090360090090090450450450450450450360450fc02b02b0fc02b02b02b01d02b02b02b01d00900900900902b00904504502b04504504502b02b02b02b02b03602b55c02b02b02b02b02b02b52d02b02b0fc17c4f80fc0315b017c0595ae46f17c0590090090090094ca00904504504504504504546c045036036036036466036,l2C 95 7 0 [w126,w111,w110,w112,w108,w105,w130,w231] 0x2f636502e0000060002f65610d017d,l2C 85 5 0 [w87,w84,w82,w324,w80] 0xd00800d00800000000000100000100800d00800d000000000000000000000000000000,l2C 85 5 1 [w87,w84,w82,w324,w80] 0x5c247f,l2C 95 6 0 [w126,w111,w110,w108,w325,w105,w130] 0x2f02e016014000000090000000000,l2C 95 6 0 [w126,w111,w110,w108,w130,w129,w152] 0x160320000d00d1000000,l2C 95 6 0 [w126,w111,w110,w108,w105,w129,w280] 0x2f000000000000090,l2C 95 6 0 [w126,w111,w110,w108,w105,w130,w321] 0x1300000001b000000,l2C 27 3 1 [w326,w20,w19,w17] 0x0,l2C 95 7 0 [w126,w111,w110,w108,w105,w130,w129] 0x2e02e02f01604e27b03204e5c85c70d00005c60d004e5c50140d10d104e04e04e03204e04e0325b501b01b01b01b01b01b04e01b01b01b03201b56501b01b4e501b5c40000d009000009004e4fc032467,l2C 95 7 0 [w126,w111,w110,w108,w150,w105,w130] 0x690960000000130135c700059701306606606600007c00907c00906607c02e02e06618b06606906606606906900006907c07c01b01d01b01d06601b01b01b07c01b01b01b06901b56701b01b00001b000078000078066000000000069000,l2C 95 6 0 [w126,w111,w110,w108,w130,w152,w143] 0x1301126b0110000005b31a0000,l2C 95 7 0 [w126,w111,w110,w112,w108,w130,w152] 0x903600907c0090273660d000907c00900916b16b16b07c16b16b5cb16b16b16b5c516b00003611c03602736707c07c07c11c5b316b16b16b11c1a01a01a01a007c1a01a016b1a01a011c1a05681a01a052f1a00004cf00000007c4be16b16b16b00011c000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB14 : Array L2Cell := #[l2C 95 7 0 [w126,w111,w110,w112,w108,w105,w130,w280] 0x2bd2f70d007c02e5c74c85c62bd56900017d,l2C 95 8 0 (w126::w111::w110::w112::v8) 0x270360960d056b07c0095cd55607c0090270270270275cc02702e02e02e02e02e02e5ca02e02e02e02e02e02f02f02e5c902e59a02e02f02e02e02e02e02e02702e02e02702718b02702702703602702702707c0360360365b507c02e02e02e02e02e02e03602e01b01b01b01d01b01b01b01d02702702702701b02707c01b01b07c02e02e01b02e02e02e01b01b01b01b01b03601b56d01b01b01b01b01b01b53001b01b0d05c317d0595c147217d0590270270270274fc02707c17d4d007c02e02e02e02e02e02e46c02e036036036036468036,l2C 95 7 0 [w126,w111,w110,w108,w105,w144,w114] 0x7921d05421d21d04604600001100001101400000001400003200003201409000001403b01d03b01d03b03b03b03b06a03b03b03b00003b03b03b07903b01409101407901407907907906a06a079000079000,l2C 93 5 0 [w162,w161,w328,w160,w327,w159] 0x800d000072304000017,l2C 93 5 0 [w162,w161,w160,w329,w327,w159] 0x80010001b9295000017,l2C 93 5 0 [w162,w161,w160,w330,w327,w159] 0x80000000083052eb000000017,l2C 85 5 0 [w87,w84,w82,w331,w80] 0x800800800800800000000100000100800800800800000000800800000d00000d000000,l2C 85 5 1 [w87,w84,w82,w331,w80] 0x5d347f,l2C 85 5 0 [w87,w84,w82,w332,w80] 0x800800800800800800800800800000000d00000d000000008008000001000001000000,l2C 85 5 1 [w87,w84,w82,w332,w80] 0x5d547f,l2C 93 6 0 [w162,w161,w160,w327,w159] 0x1a201d0081f81a201d1a21a200800800800800800800818c0085d60081b900800800800800800800816e0085d40080720000005d20001a200800800800800800800803b0000175d10170000175d0017,l2C 93 6 1 [w162,w161,w160,w327,w159] 0x5d701d,l2C 95 7 0 [w126,w111,w110,w108,w105,w144,w129] 0x3209601609609602e02e00001100001101400000001401418b01403201403203203204e04e03200001b01d01b01d01b01b01b01b04e01b01b01b03201b01b01b00001b000079000079014090000014032000,l2C 93 5 0 [w162,w161,w328,w160,w333,w159] 0x80170001f837600000d,l2C 93 5 0 [w162,w161,w160,w329,w333,w159] 0x800000000829500000d2b4000,l2C 85 5 0 [w87,w84,w82,w334,w80] 0x800800800800800000000100000100800800000d00000d008008008008000000000000,l2C 85 5 1 [w87,w84,w82,w334,w80] 0x5dc47f,l2C 93 5 0 [w162,w161,w160,w330,w333,w159] 0x80010001b930500000d,l2C 85 5 0 [w87,w84,w82,w335,w80] 0x8008008008008008008008008008000001000001000000008000000017000017000000,l2C 85 5 1 [w87,w84,w82,w335,w80] 0x5df47f,l2C 93 6 0 [w162,w161,w160,w333,w159] 0x8401d00807208401d08408400800800800800800800818c0085e00081b908400800800800800800800801b00000d5de00d0080080080080080080082360085dd0081f80000005db00000d0005da00d,l2C 93 6 1 [w162,w161,w160,w333,w159] 0x5e101d,l2C 89 3 1 [w339,w338,w337,w336] 0xd,l2C 93 5 0 [w162,w161,w328,w160,w159,w340] 0xd017000,l2C 92 3 1 [w344,w343,w342,w341] 0x17,l2C 93 5 0 [w162,w161,w160,w329,w159,w340] 0x8017000008000017001,l2C 93 5 0 [w162,w161,w160,w159,w345,w340] 0x1017000001000017008,l2C 85 5 0 [w87,w84,w82,w346,w80] 0x100800100800800100800100000000000d00000d000000000000000000000000000000,l2C 85 5 1 [w87,w84,w82,w346,w80] 0x5e847f,l2C 93 5 0 [w162,w161,w160,w330,w159,w340] 0x800d00000800000d001,l2C 93 5 0 [w162,w161,w160,w159,w347,w340] 0x100d00000100000d008,l2C 85 5 0 [w87,w84,w82,w348,w80] 0x1008001008008001008001000000000000000000000000000017000017000000000000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB15 : Array L2Cell := #[l2C 85 5 1 [w87,w84,w82,w348,w80] 0x5ec47f,l2C 93 6 0 [w162,w161,w160,w159,w340] 0x100118c00800816d0080010390080005ed5e300d0005565e300d0080005eb0080010005ea0010005e95e50170004825e50170080005e70080010005e60015e35e55e45e3,l2C 93 6 1 [w162,w161,w160,w159,w340] 0x5ee01d,l2C 94 4 1 [w205,w204,w196,w194,w349] 0x0,l2C 23 4 0 [w16,w14,w350,w13] 0x8008000000000000000000000000,l2C 23 4 1 [w16,w14,w350,w13] 0x5f1,l2C 95 7 0 [w126,w111,w110,w108,w105,w144,w143] 0x111f60131f61f60410410140920140110140110110110660660000320000320144750000140110000000395f201d03903901d01d0390390390390660390110390390390000390390390000390000790000790145f0000014011000,l2C 93 5 0 [w162,w161,w328,w351,w160,w159] 0x1008000000008304376000,l2C 85 5 0 [w87,w84,w352,w82,w80] 0x800800800800800800000100000100800000000d00000d008008000000008008000000,l2C 85 5 1 [w87,w84,w352,w82,w80] 0x5f547f,l2C 93 5 0 [w162,w161,w351,w160,w329,w159] 0x80170001f80012b4000,l2C 85 5 0 [w87,w84,w353,w82,w80] 0x8008008008008008000001000001008008000000008008008000000017000017000000,l2C 85 5 1 [w87,w84,w353,w82,w80] 0x5f847f,l2C 93 5 0 [w162,w161,w351,w160,w330,w159] 0x800d0000720012eb000,l2C 93 6 0 [w162,w161,w351,w160,w159] 0x16d01d0081b916d01d16d16d16d0080080080080080080080390080080080080010005fa00100800800816e0085f90080720080080080080010005f70010080080082360085f60081f80000005f4000,l2C 93 6 1 [w162,w161,w351,w160,w159] 0x5fb01d,l2C 95 8 0 [w126,w111,w110,w108,w105,w144] 0x2f02f02f0145fc0115f35ef0110270270270270145e20325d959a0320270270270270110325b701101d01d01d01d01d01d02702702702701d02701101d01d01101d01d01d01d01d58901d01d01d01d01d01d01d53601d01d0145d80795cf4860790270270270270110794d2011032079477032,l2C 95 7 0 [w126,w111,w110,w108,w150,w106,w105] 0x6600000006600001300001307823205423223204804800006900006901309500001303a01d03a01d03a03a03a03a02603a03a03a00003a03a03a07803a07800001321c013078013078078078026026078000,l2C 93 5 0 [w162,w161,w328,w160,w354,w159] 0x100d0001d9302000017,l2C 93 5 0 [w162,w161,w160,w354,w159,w345] 0x80010001b9303000017,l2C 93 5 0 [w162,w161,w160,w355,w159] 0x800000000808d23402b1f9001001000266000235001001000000,l2C 93 5 0 [w162,w161,w160,w354,w159,w347] 0x10000013750002ec000017,l2C 93 5 0 [w162,w161,w160,w159,w356] 0x100116d2340391f900000d00000d0002360001f8000000001001,l2C 93 6 0 [w162,w161,w160,w354,w159] 0x116d0010010016030011b90010010010011f901d0012341f901d1f91f900000060200000100100108d0016010011d900100100100100001760001700100103a1f90010010010010010000175ff017,l2C 93 6 1 [w162,w161,w160,w354,w159] 0x60401d,l2C 95 7 0 [w126,w111,w110,w108,w150,w127,w105] 0x6600000006600001300001306919c01619c19c04504506900001319d01306901306906906902902902b01d02b01d02b02b02b02b02902b02b02b06902b02b02b00002b000078000078013095000013069000,l2C 93 5 0 [w162,w161,w328,w160,w357,w159] 0x101700023437400000d,l2C 93 5 0 [w162,w161,w160,w358,w159] 0x800000000821e1d903a1da00008c000235001001001001000000,l2C 93 5 0 [w162,w161,w160,w357,w159,w345] 0x100000130300000d0002b5,l2C 93 5 0 [w162,w161,w160,w357,w159,w347] 0x80010001b937500000d,l2C 93 5 0 [w162,w161,w160,w159,w359] 0x100116d1d90391da00016e000072000000001001000017000017,l2C 93 6 0 [w162,w161,w160,w357,w159] 0x116d00100100160b0011b90010010010011da01d0011d91da01d1da1da00000d60a00d00100102b1da00100100100100100000060900000100100121e00160800123400100100100100d00060700d]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB16 : Array L2Cell := #[l2C 93 6 1 [w162,w161,w160,w357,w159] 0x60c01d,l2C 71 4 0 [w363,w362,w361,w360] 0x1001000000000000000000000000,l2C 71 4 1 [w363,w362,w361,w360] 0x60e,l2C 95 7 0 [w126,w111,w110,w108,w150,w105,w143] 0x131f606609206606601301306606601409209201106604104100006900006906600001347500001300003960f01d03903901d01d0660390390390390390110390390390000390390390000390000780000780660000135f0000013,l2C 93 5 0 [w162,w364,w161,w160,w159] 0x100121e1b903a18c00000d00000d1a20000001f8000000001001,l2C 93 5 0 [w365,w162,w161,w328,w160,w159] 0x8001000000001302000374,l2C 93 5 0 [w365,w162,w161,w160,w159,w345] 0x82b5000017001000234,l2C 93 5 0 [w162,w161,w366,w160,w159] 0x100108d1b902b18c084000000072000000001001000017000017,l2C 93 5 0 [w365,w162,w161,w160,w159,w347] 0x82ec00000d0010001d9,l2C 93 6 0 [w365,w162,w161,w160,w159] 0x800118c00100100818c01d0081b918c01d18c18c00800061500800100100100100100100108d0016140011d900800061300800100100100100000061200000100100121e001611001234001039001,l2C 93 6 1 [w365,w162,w161,w160,w159] 0x61601d,l2C 95 8 0 [w126,w111,w110,w108,w150,w105] 0x660136176105ef06606600900906602f02f02f0660695ca06601360d0696065a306900900900900906601d01d06601d01d01d01d01d01d00900900900901d00901d01d01d01d01d58f01d01d01d01d01d01d01d53c01d01d0660785060660136050785fe49007800900900900906907847a069,l2C 21 3 1 [w12,w367,w10] 0x0,l2C 95 6 0 [w126,w111,w110,w108,w105,w190,w143] 0x2f000000000000000000,l2C 95 7 0 [w126,w111,w110,w112,w108,w105,w152,w190] 0x2fb24e2fb0fb04149900061a61911c000000133,l2C 95 6 0 [w126,w111,w110,w108,w368,w105,w152] 0x2f0410d900026b36c000000000000,l2C 95 7 0 [w126,w111,w110,w112,w108,w369,w105,w152] 0x92ba36d2b802735600000004161c133000000000,l2C 21 3 1 [w11,w370,w10] 0x0,l2C 95 6 0 [w126,w111,w110,w108,w105,w280,w143] 0x2f000000000000000000,l2C 95 7 0 [w126,w111,w110,w112,w108,w105,w152,w280] 0x2fc1b72fc0fc0415ab00061f00011c00061e133,l2C 95 6 0 [w126,w111,w110,w108,w371,w105,w152] 0x2f0410d900026b00000000000036c,l2C 95 7 0 [w126,w111,w110,w112,w108,w372,w105,w152] 0x936736b2bd0272ea00000004162111c000000000,l2C 79 5 0 [w149,w148,w147,w373,w145] 0x13013000000000000000001000001001000000000000000000000000000000000000000000,l2C 79 5 1 [w149,w148,w147,w373,w145] 0x623,l2C 95 6 0 [w126,w110,w108,w374,w105,w152,w143] 0x392be36c36e36f,l2C 79 5 0 [w149,w148,w147,w375,w145] 0x13013000000000000000000000001000001001000000000000000000000000000000000000,l2C 79 5 1 [w149,w148,w147,w375,w145] 0x626,l2C 95 7 0 [w126,w111,w110,w108,w105,w152,w143] 0x4104102f0130660d901106601426b26b0660660660110660660666275ab00047561f4750665cb0115b86250390390390390390390390390660390110390390395910390390395420396244990005f061a5f00665070114d3,l2C 95 8 0 (w126::w111::w110::w112::v9) 0x270091f602702709202702702700902702702702704104104104104104100904104104104104102f02f0416280415ef04102f0410410410410410270410416225ed11c03662055611c0360270270270275cc0270090090090095ba0090410410410410410415ac04103903903901d03903903901d02702702702703902700900900900903900904104103904104104103903903903903959503903903903903903903954303903961d5e913305961b4821330590270270270275080270090090090094d500904104104104104104149a04111c13347c11c,l2C 95 9 0 (w126::w111::w110::v6) 0x2700962902702f02f02f02f02f02f61802f02f02f02f02f02f5fd02f02f0270365ce0270090365c000902f02f02f02f02f02f5ad02f02701d01d02700901d01d00902f02f01d02f02f02f01d01d01d01d01d59601d01d01d01d01d01d01d54401d01d02705950a0270090594db00902f02f02f02f02f02f49b02f03605947d036,l2C 95 9 1 (w126::w111::w110::v6) 0x62a,l2C 103 6 0 (w380::w379::v12) 0x1301301301301201201201201301301301301301301201301a01a01a01a01301301301301201201201201201201a01201801801801801301301301301201201201201a01a01a01a01a01a01801a]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB17 : Array L2Cell := #[l2C 103 6 1 (w380::w379::v12) 0x62c,l2C 101 5 0 [w385,w384,w383,w382,w381] 0x1004001004001001000001000001000000000004000004004000000,l2C 101 5 1 [w385,w384,w383,w382,w381] 0x62e,l2C 71 4 1 [w388,w387,w362,w386,w360] 0x1,l2C 47 5 0 [w58,w57,w390,w43,w389] 0x2002000002000000000000021021000000000000002002002002,l2C 47 5 1 [w58,w57,w390,w43,w389] 0x631,l2C 111 7 0 (w397::w396::w395::w394::v13) 0x200200200401c01f00201c01501f00001500701f00701f00401f00700b00200b00b63000b63200b00b00400b01e00b00200200000000400400e00b01900b00e00b00e00e06700e00b09e00209e63009e00401f09e01f01900b09e01900b00b00b09e00b01e17e,l2C 111 7 0 (w399::w397::w394::w398::v13) 0x200200200402200202200002200401e17201909e09e01901903801f00203802001f00002004f01f04f01f00401f04f09e00209e00009e00400e00e01f09e01f01909e09e01903709e03709e09e03700203700003703700403702201e03701e00e00e,l2C 43 4 0 [w403,w402,w401,w400] 0x2002000000000000000000000000,l2C 43 4 1 [w403,w402,w401,w400] 0x635,l2C 110 5 0 (w408::w407::v14) 0x20020020030020020000000030030020020a7153,l2C 110 5 1 (w408::w407::v14) 0x637,l2C 103 5 1 [w380,w378,w410,w377,w409,w376] 0x3,l2C 111 7 0 (w399::w395::v50) 0x5c00200205c03f00300303f05c00203f00200200200305c05c00200205c00000063900003f00300303f00b00b00b00b00200b00b00b00b00b00b00b00b00b00b00b00b00b00b63800b03703703703700203703703703703763603703703703703703703703702217100b00b00b00b,l2C 111 7 0 (w399::w397::w395::v50) 0x200200200400c00200200c00900000000900500400400500b00200b00b00000b00b00b00400b06700b05c09e00209e00009e00009e03f09e00409e01f17e00b00b00b00b00b09e00b03709e03709e00b00b09e03700203700003703700403702217100b03700b00b,l2C 102 4 1 [w416,w415,w414,w413,w412] 0x3,l2C 42 2 1 [w419,w418,w417] 0x0,l2C 111 7 0 (w399::w397::w395::w394::w393::v15) 0x63d14a00101f00001f0090001a700000e00063c01900000063001e000000,l2C 103 5 0 [w379,w423,w422,w421,w376] 0x52052052003012012000000000000003003,l2C 103 5 1 [w379,w423,w422,w421,w376] 0x63f,l2C 111 6 0 (w399::w397::w394::w393::v16) 0x1df001024020000024000,l2C 111 7 0 (w399::w397::w394::v17) 0x1bd0020021bd1df0030031df1bd0021df0020020020031bd1bd01f01f01f0021bd06f0090240240240091df01f01f01f01f1df1bd21f0021bd00021f64121f1df21f0041df01f21f01f01f01f21f02402421f02402402463221f1bd0240240240021bd0246400240240240241df0240240240240030241df00e00e00e,l2C 42 3 1 [w419,w427,w426,w417] 0x0,l2C 111 7 0 (w399::w397::w394::v51) 0x20020030031bd06f0021bd00e06f1df06f00306f00200200200300f01f00200f00929401e06f00906f00900906f00906f01f01f06f02400906f00a01f00a01f00301f00a64300006f21f63c06f01f01f03003001f00003002402402463002400203101e02401e01e06f02402406f02402400302400e159,l2C 110 6 0 [w430,w429,w428,w405,w404] 0x200200200200300300300300200200200200200201f01f01f01f01f01f01f01f01f01f01801801800200200200200000000000000300300300301f01f01f01f01f01f,l2C 110 6 1 [w430,w429,w428,w405,w404] 0x645,l2C 107 6 0 (w435::w434::v19) 0x2102102102101201201201202102102102102102101202102102102102102202202202201201201201202202202202202201f02202202102102102101f01f01f01f01201201201201201201f012,l2C 43 4 0 [w437,w436,w401,w400] 0x2002000000000000000000000000,l2C 43 4 1 [w437,w436,w401,w400] 0x648,l2C 107 6 0 (w435::w434::v52) 0x2100200202101200300301200200201f01f00300300200200200300002200002200000001f01f01f00063601f00203101f03101f01f01f01f01f00301f649,l2C 107 6 1 (w435::w434::v52) 0x64a647,l2C 111 8 0 (w399::w397::w395::w394::v13) 0x1bc06f0021bc14a06f00306f1bc00214a0020020020031bc1bc00c01f01f01f0021bc00c06f00901f01f01f64b06f00914a00501f00501f01f01f00301f64614a0051bc00e00e00e0021bc06f00e00e00e00e64400e64206f14a00e00e00e00e00300e14a00e01e00e1bc09e0021bc06f09e63e06f14a09e00414a01f01f09e01f01901901f01f63b63a09e01900e00e00e00e00e00e63400e01e01e09e01e01e01e63309e1bc01e01e01e0021bc06f01e01e01e62f06f14a01e01e01e01e00301e14a00e00e00e00e00e00e01e00e00e00e]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB18 : Array L2Cell := #[l2C 99 5 0 [w443,w442,w441,w440,w439] 0x4003004003004000000000000000004000004004000000000003000003003000000,l2C 99 5 1 [w443,w442,w441,w440,w439] 0x64d,l2C 107 5 0 [w434,w445,w444,w438,w431] 0x3003000000000000000000,l2C 107 6 0 (w434::w445::v20) 0x200000000200301200000000300300200064900064900201f01f01f00300300000000300300200364964964900200200064900200000000000000064f00000064e000003000000003,l2C 107 6 1 (w434::w445::v20) 0x650,l2C 79 5 0 [w149,w148,w200,w188,w145] 0x1000000001001001001000001044044,l2C 79 5 1 [w149,w148,w200,w188,w145] 0x652,l2C 47 5 0 [w47,w58,w44,w42,w41] 0x6e06e002000000002000002002002002,l2C 47 5 1 [w47,w58,w44,w42,w41] 0x654,l2C 109 5 0 (w450::w449::v21) 0x1001000000001100100100001001124124,l2C 109 5 1 (w450::w449::v21) 0x656,l2C 110 5 0 [w451,w430,w407,w405,w404] 0x200200000000200215a1a30020a70a70a7,l2C 110 5 1 [w451,w430,w407,w405,w404] 0x658,l2C 15 3 1 [w6,w5,w173,w172] 0x0,l2C 111 7 0 (w399::w397::w398::v22) 0x20922465a2090a72240002242090a76590006552092091000002092241006570006532240a71000000a720902c02c02c65520922402c02c22402c02c02c02c06506506502c02c02c02c20903703720922403703703765322404f04f04f037037037037,l2C 107 6 0 [w435,w434,w445,w432,w431] 0x6e00200206e00300300300306e00200200200206e06e10000206e00010000010000310000310001f10001f01f01f10006e01f01f06e01f01f01f01f64901f012012012,l2C 107 6 1 [w435,w434,w445,w432,w431] 0x65c,l2C 107 5 1 (w434::w445::w453::v20) 0x649,l2C 111 7 0 (w399::w397::w395::w452::v23) 0x2600002601800002a00000002a01800002c02c00300300000300306500306501800302c00002c00001802c01802c02c02c02c02c00302c02c0e40e465e01a0e401a007007007,l2C 107 5 1 [w434,w445,w438,w455,w431] 0x64e,l2C 102 4 1 [w415,w457,w456,w414,w412] 0x3,l2C 35 3 1 [w461,w460,w459,w458] 0x0,l2C 71 4 0 [w363,w463,w360,w462] 0x1001000000000000000000000000,l2C 71 4 1 [w363,w463,w360,w462] 0x663,l2C 103 5 0 [w380,w378,w466,w465,w464] 0x1301a01301a02d01a00101a02d013001013000000000000001001001000000000000000000001000,l2C 103 6 0 [w380,w378,w377,w466,w376,w465] 0x1a01a02d01300101301302d00102d00100001300101300100100000166501a01a00000000000000100100100066400100100100000000000057f001000001662,l2C 103 6 1 [w380,w378,w377,w466,w376,w465] 0x666,l2C 107 5 1 [w435,w434,w445,w432,w455,w431] 0x1f,l2C 77 3 1 [w470,w469,w468,w467] 0x1,l2C 107 5 1 [w435,w434,w445,w455,w431,w471] 0x0,l2C 98 3 1 [w475,w474,w473,w472] 0x0,l2C 111 7 0 (w399::w397::w395::w452::v15) 0x2a00166b02a01800100100100001800101802666a02c02602600000066900100106506500166865306502602602600000000002c66702602602602c02602602c00002c02c66102c02c11511501e11501e0260260261156601a70c4]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB19 : Array L2Cell := #[l2C 47 5 0 [w47,w58,w42,w41,w389] 0x6e06e000000000000002002002002002002000002000000002,l2C 47 5 1 [w47,w58,w42,w41,w389] 0x66d,l2C 99 5 0 [w443,w442,w478,w477,w476] 0x4003004003004000000000000000000000004000004004000000000003000003003000000000000,l2C 99 5 1 [w443,w442,w478,w477,w476] 0x66f,l2C 107 5 1 [w435,w434,w432,w480,w479] 0x670,l2C 107 5 1 [w435,w434,w445,w432,w480,w471] 0x0,l2C 111 7 0 [w399,w397,w395,w452,w392,w391,w481] 0x2c02a00002666b02602a67200001800001802a02a02a00067100206500206502a00200200266e00200200202a02a02a02c02a02a02c66702c00002c02c00202c65502c10710701e10701e02a1071076491c3117,l2C 110 5 0 (w430::w406::w483::v24) 0xa6000,l2C 46 3 1 [w487,w486,w485,w484] 0x2,l2C 110 5 0 [w430,w406,w405,w488,w404] 0x2000002000002000000000000000000000000000000000675000000000000000,l2C 110 5 0 [w430,w406,w405,w489,w404] 0x200200000000000001f01f000000000000000000000000,l2C 110 5 0 [w430,w406,w405,w482,w404,w490] 0x2000000000,l2C 110 5 0 [w430,w406,w405,w482,w491] 0x520000000520520d2237052000002052000000052000,l2C 110 4 0 [w430,w482,w491,w492] 0x20d20020d20d2000000000000,l2C 110 5 0 [w430,w405,w482,w404,w491] 0x5205200000000200000200200200200200200067a0d20d2002000000675,l2C 110 5 0 [w430,w406,w405,w482,w404,w491] 0x2002000000000002052,l2C 110 5 0 (w451::w430::v24) 0x200200200215a237000000002052052052,l2C 110 5 0 [w430,w406,w405,w482,w493] 0x520020020020520520020021bb237000000,l2C 110 5 0 [w430,w406,w405,w482,w494,w404] 0x237052000052000,l2C 110 5 0 [w430,w406,w482,w404,w492] 0xa600200201f00201f01f00200000200200000000200200200067a002000000000,l2C 110 5 0 [w495,w430,w406,w482,w404] 0x20020000000020020020000000000020a6002002,l2C 110 5 0 [w430,w406,w405,w496,w404] 0x2002000000003237052052000052000000,l2C 110 5 0 [w430,w406,w405,w497,w404] 0x2002052000000000237052052000052052000052000000000000052,l2C 110 5 0 (w498::w430::w406::v24) 0x1f002000002,l2C 110 6 0 (w430::w406::v24) 0x20026840000020020520006830006820520020a668100068000201f01f01f0520a667f05200267e05267d67c67b6790520020006780020006770000006760000a60000000a6052000674052,l2C 110 6 1 (w430::w406::v24) 0x685,l2C 107 5 0 [w434,w432,w499,w431,w479] 0x30020d200006e12b000000002000000000000000002000,l2C 107 5 0 [w435,w434,w432,w455,w431,w479] 0x6e000000000000,l2C 107 5 0 [w435,w434,w432,w479,w471] 0x300306e06e0000000000000000000020020d20d2000002002002000002000,l2C 75 3 1 [w290,w288,w287,w500] 0x0,l2C 107 6 0 [w435,w434,w432,w431,w479] 0x200300200000000068a06e00200200268906e00000000000006e00200200267006e0000006880000d20020020020020d200268700206e0d20d200206e0d20020d20020026490d2,l2C 107 6 1 [w435,w434,w432,w431,w479] 0x68b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB20 : Array L2Cell := #[l2C 77 4 0 [w469,w502,w501,w468] 0x1001000001000000000000,l2C 77 4 1 [w469,w502,w501,w468] 0x68d,l2C 109 4 1 [w450,w504,w447,w446,w503] 0x0,l2C 102 4 0 [w416,w456,w505,w412] 0x3003000000000000000000000000,l2C 102 4 1 [w416,w456,w505,w412] 0x690,l2C 111 6 0 [w399,w397,w395,w452,w392,w507,w506] 0x26018000000000000,l2C 111 7 0 [w399,w397,w395,w452,w392,w391,w507] 0x1802a00002600002602a69201868a00001802a02a02a02a01801802a02a00000269106500200206506502a00200200266e00201806e00206e00002c00002c02a00001868f00001800200200200003503500003568e03502a035649050050,l2C 107 5 0 [w508,w435,w434,w432,w455,w431] 0x6e000000003,l2C 107 6 0 [w508,w435,w434,w432,w431] 0x6e00200206e06e00200206e00000069400015a00200200200215a00300300300306e00215a00200206e00215a00200264915a00201206e00200215a002002003003003003003,l2C 107 6 1 [w508,w435,w434,w432,w431] 0x695,l2C 111 7 0 [w399,w397,w395,w452,w392,w509,w391] 0x2a00000002a02600001802601802602602601800002602600306500306502602602600301800300002c00002c02600001800000300300300014b14b01314b0130260261a81a8,l2C 107 5 1 [w435,w434,w432,w479,w471] 0x689,l2C 111 7 0 (w399::w397::w395::w452::v25) 0x2602a02a02a02a02602a02a02600000001800001802a02a02a69269800206500206502a00202602602600266e00200200002c66b02c02a67202666a00200200265a0b40b40b401e0b401e02a0b40260260260b464906b117,l2C 111 8 0 (w399::w397::w395::v22) 0x2a02669902a01802669702602a01869669368c02a02a06500202a02665d06565d65d68665d02601865d06500364606502a02c67302a02602c66c02601802c65f02c06565d02c65d65d65d65b06501e02c01e01e01e02c02a01e01e02a02601e01e01e65102600500500506501e01e065,l2C 103 6 0 (w380::w379::v26) 0x104400104400400400400404400100100100104401a01a01a01a66401a04401a01a0440120120120000a70000a70440a70010440040a70040a701a01a01a01a01a01a,l2C 103 6 1 (w380::w379::v26) 0x69b,l2C 102 4 0 [w457,w456,w412,w511] 0x3003000000000000000000000000,l2C 102 4 1 [w457,w456,w412,w511] 0x69d,l2C 103 6 0 (w380::w378::v26) 0x4400004400400400400404400400404401201201201269e01204401201201201204401201a0120030a70030a70440a70030440040040a70040030a7012012012012,l2C 103 6 1 (w380::w378::v26) 0x69f,l2C 105 4 0 [w515,w514,w513,w512] 0x4004000000000000,l2C 105 4 1 [w515,w514,w513,w512] 0x6a1,l2C 107 6 0 [w434,w433,w445,w432,w431] 0x6e00000006e0030030030030120120120126a201206e00300306e06e01201201201206e01201f01206e10000406e004100004100004004100004004100012012012012,l2C 107 6 1 [w434,w433,w445,w432,w431] 0x6a3,l2C 71 4 0 [w387,w362,w360,w462] 0x1001000000000000000000000000,l2C 71 4 1 [w387,w362,w360,w462] 0x6a5,l2C 109 5 0 (w516::w504::v21) 0x100100000000100100100400400400100101a01a,l2C 109 5 1 (w516::w504::v21) 0x6a7,l2C 107 5 1 [w434,w433,w453,w432,w431,w517] 0x4,l2C 111 7 0 (w397::v58) 0x103e00103e00103e00103e0070070070070010070000006a90000070070070070070070076a800700403f00403f03e00103f00100100100403e00403f00403f00700700700700700702c02c02c02c6a602c02c02c02c02c00102c02c01813500700700700702c02c02c02c02c02c,l2C 111 7 0 (w397::w395::w393::w452::v23) 0x102600102601803e00103e00700102a00000002a00001800001802c13f0070070000076a80e400700100100100400406500406501803f00403f00700702c00002c00101813501802c01802c02c02c00700702c02c00402c,l2C 103 6 0 (w518::w379::v12) 0x11dc0011dc00418f00418f1dc00118f0010010010041dc01a01a01a01a1dc01a01a1dc18f01a01a01a01a00401a18f0180180180181dc0180181dc18f01801818f01a01a018]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB21 : Array L2Cell := #[l2C 103 6 1 (w518::w379::v12) 0x6ac,l2C 103 6 0 (w380::w379::v53) 0x1a01a00101300101300100100401200401200400400100100100402d01a02d01a01a01a01a00101a01a00401a66400001800001800000001a01a01a0006a6,l2C 103 6 1 (w380::w379::v53) 0x6ae62c,l2C 79 5 0 [w147,w200,w217,w188,w145] 0x4404400004400000000000000113c,l2C 79 5 0 [w519,w148,w147,w188,w145] 0x10010010010000010130130010a6,l2C 79 6 0 [w148,w147,w217,w188,w145] 0x130130130130130130136b10130000000000000000000000000130130130130130130010010010010010010010010010010130130130130010010010010016b0001001,l2C 79 6 1 [w148,w147,w217,w188,w145] 0x6b2,l2C 103 6 0 [w380,w379,w520,w377,w376] 0x13013013013012012012012013013012001124001124013013013013012012012012012012001012003237003237013013013013012012012012124001237001001001003124,l2C 103 6 1 [w380,w379,w520,w377,w376] 0x6b4,l2C 103 6 0 [w380,w379,w378,w521,w376] 0x130130130130130120130120120120120011520011520130130130130120120120120120120010120032c10032c10130130130130120120120121520012c1001001001003152,l2C 103 6 1 [w380,w379,w378,w521,w376] 0x6b6,l2C 79 5 1 [w148,w147,w217,w188,w145,w522] 0x13,l2C 69 3 1 [w139,w523,w137] 0x0,l2C 107 5 1 [w434,w433,w445,w432,w479,w471] 0x0,l2C 111 7 0 [w397,w395,w393,w452,w392,w391,w507] 0x1802a00002600002602a6ba0180000506b802a02a02a01802a02a00205000202a0500350500350000036b906500300306506502a0030030036b800301800305005000002c00002c02a57f018000003003003000,l2C 111 8 0 (w397::w395::w393::v22) 0x2a0266b302a0180266b30260050050260056b302602a0186bb02a02a00500500500502a00501e00502a0656a402a0266b70656b56a46b36a402601806500306500500500500500500502a02c6af02a02602c0010260186ad02c6ab6aa02c0050050050050656a402c6a40046a069c065,l2C 103 5 0 [w525,w378,w377,w524,w376] 0x3e00001803e03f03f03e03e03e00300001a03e00003e003003,l2C 103 5 0 [w380,w379,w524,w421,w376] 0x12012001001074074052000000052013013052052001052000,l2C 97 3 1 [w529,w528,w527,w526] 0x0,l2C 103 6 0 [w380,w379,w378,w377,w524,w376] 0x2d0006bf02d0130000180130030120030120130130130036be00101a00101a0130010010010030010180000130130130180130130180030180180010186bd,l2C 103 6 1 [w380,w379,w378,w377,w524,w376] 0x6c062c,l2C 105 4 1 [w531,w515,w514,w512,w530] 0x4,l2C 79 5 1 [w148,w147,w217,w188,w145,w216] 0x13,l2C 111 7 0 (w397::w395::w393::w452::v28) 0x1e02a00202600002602a00001800005000000c02a00502a00c02a00c00c01800c02a00205000200502a05000502a02a02a05002a01e1490020026b906500200206506502a0020020026c300201800205005005000200202c00002c02a57f0180000500000020020026c2,l2C 103 5 1 (w380::w525::v53) 0x6a6018,l2C 111 6 0 (w397::w396::w395::w452::v29) 0x1c01802a00502c000018,l2C 107 5 1 [w434,w534,w433,w432,w431,w479] 0x22,l2C 111 7 0 (w397::w396::w395::w393::v22) 0x1801500101500700101c0186c701c0070076c600701e00700100100100401800b00400b00700700700402a00000002a02600100102600500713f0190070070070050070050050070676a800700500706500400406502c6c502c00101802c01801900702c01900702c00700700702c02c00402c01e135,l2C 103 6 0 (w380::w535::v12) 0x118e00118e00413d00413d18e00113d00100100100418e01a01a01a01a18e01a01a18e13d01a01a01a01a00401a13d01801801801818e01801818e13d01801813d01a01a018,l2C 103 6 1 (w380::w535::v12) 0x6c9,l2C 111 7 0 [w399,w397,w395,w452,w536,w392,w391] 0x1a02600102601800102a01a00002a01800001902c01e02c01902c01900100100100401a01a06506501a00406501800402c00002c00100500501801902c01902c02c00402c02c02c02c0e402c0e40000e400101a0e401a01e02c0e401e0050050e4004,l2C 111 7 0 (w399::w397::v58) 0x100900100900700100c00000000c00700700000706700700100100100400400e00400e00700700700402c00002c00101813500702c00700702c02c00402c02c02c02c02c00700702c0000e40000e403e0e40010e401a13f00700700700700702c00703f0e40040e4]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB22 : Array L2Cell := #[l2C 111 6 0 (w399::w397::w452::v54) 0x2cb00f0520002cb000,l2C 111 6 0 (w399::w397::w395::w452::v31) 0x2601802a000035000000,l2C 111 7 0 (w399::w397::w395::w452::v29) 0x502a00002600002602a6ce01801100001100c02a14901e02a02a02a00c02a00c00c02a01801802a00c02a00206500206502a0020020026cd00201801000201000002c00002c02a6af01802300002300200200269c0350350356c602d03568e01e02a03501e02a03502a02a02a0356c1005117035002,l2C 110 5 0 [w430,w407,w406,w405,w493] 0xa70020020020000000a70a70020021bb1a3,l2C 110 5 0 [w430,w429,w406,w405,w537,w493] 0x181bb000000,l2C 110 6 0 [w430,w429,w406,w405,w493] 0x180180020020020020020180180180180020021bb0021bb0020020021bb00200267e0021bb0180180180180180180020180020020020020000006d10000180180180181bb0020020020020026d01bb,l2C 110 6 1 [w430,w429,w406,w405,w493] 0x6d2,l2C 103 5 1 [w379,w378,w377,w524,w376,w538] 0x0,l2C 103 5 1 (w380::w379::w510::v32) 0x1a,l2C 111 6 0 [w399,w397,w393,w392,w425,w391,w507] 0x310000002cb0000ca,l2C 107 5 1 [w435,w434,w432,w539,w431,w479] 0x2,l2C 107 5 1 [w435,w434,w433,w432,w479,w471] 0x689,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w507] 0x1802a00000900000902a6d805068a6d705000214902a02a02a02a02a05002a0000026b900e00200200e00e02a0020020026d600205005006e00205000205000001900001902a57f05068f0000500020020026d50350350356c702d11702a03502a02a0356d405005003503502a02a050035002,l2C 111 7 0 [w399,w397,w395,w452,w392,w540,w391] 0x2a01300002a0260000050260180090260090186d700902601e02600902600901301306506501300306502602602600301800301302c00102c02600101800100100100300114b14b31300114b00131331514b00031501314b01314b01e01e02602614b01e0260260260260050c431414b003314,l2C 103 5 1 [w380,w379,w378,w524,w376,w464] 0x0,l2C 110 5 1 [w430,w406,w482,w404,w492] 0x680,l2C 111 7 0 (w399::w397::w395::w393::w452::v25) 0x900002600000001800001800c6d800000500000502a6ce6dc00200100001e00001e02a0000266db06b0b4,l2C 111 8 0 (w399::w397::w395::w393::v22) 0x2a0266dd02a0180180260090186c10260090050050260260056da02602602a00c0180180186d902a00c02a02a0056d30050050056cf00502a02a00501e00502a06500202a02600306500300368600302601801806500e01800306500e00500500500506565d00500500300500502a02c6af02a02602c00102601801802c0190186cc02c01900500500502c0056cb00500506500302c00300400369c06501e01e02c01e02c6ca01e01e6c802c02c02a02a01e01e01e6c402a02a02602601e01e01e6c102602600500500500500500500500500501e01e00500500506506501e01e01e003065065,l2C 109 5 0 [w516,w504,w542,w447,w446,w541] 0x1a000000000239067,l2C 109 5 0 (w516::w504::v33) 0x1a01a001001001001004004281281001001001004000000000000,l2C 109 6 0 [w516,w504,w542,w447,w446] 0x100100100101a01a00101a01a01a01a01a01a01a01a6e001a01a00423900423900100123900100100100423901a01a01a01a01a01a00401a0000676df06700100100100101a01a6a7239004004239,l2C 109 6 1 [w516,w504,w542,w447,w446] 0x6e1,l2C 111 7 0 (w544::w397::w395::v17) 0x19000200219000a00a00a00a19000a00a00a00a00200a1901900c50c50c500219010510510500a00a00a00a0c500a19025100219000425100425100a00a00a00a0c50c50c50c50c50c519002402419002402402402400a00a0240c50c50c50c50240c5251024024024024004024251,l2C 111 7 0 (w544::w397::w395::v51) 0x14900200214900500a00a0051901050021900c510500a10500a10500a00a00200a1900c50021901051051051051051050c50c510510500a00a00a00a00a0c500a0010ff0010ff1052510011050c50c52510010c50010c502401e02401e1050240241050260240c50240240c5024024001024,l2C 47 5 0 (w58::w545::v34) 0x2002002000002002000002000000000002000000000000002002002000002002002,l2C 47 5 0 [w58,w45,w43,w42,w41] 0x6e02d00000213b06e02d06e06e00006e00000006e06e06e000,l2C 47 5 0 [w546,w58,w44,w43,w41] 0x13b13b000002002002002000,l2C 47 5 0 [w546,w58,w45,w43,w547,w41] 0x13b00002d002000000,l2C 47 5 0 [w546,w58,w45,w43,w41,w548] 0x2d13b000000,l2C 47 5 0 (w546::w58::v35) 0x13b13b000000000000000002002002002002002000002002002000002,l2C 47 5 0 [w546,w58,w43,w56,w41] 0x13b13b00000000213b02d002002002000002,l2C 47 5 0 [w546,w58,w45,w43,w41,w549] 0x2d13b000000000000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB23 : Array L2Cell := #[l2C 47 6 0 (w546::w58::v34) 0x2d6ec02d13b00202d0020020026eb13b00200213b0020026ea00213b0000006e900002d0006e802d13b0020020020020026e713b0020020020020026e600213b00200200213b0020020020020020026e5002002,l2C 47 6 1 (w546::w58::v34) 0x6ed,l2C 111 8 0 (w544::v59) 0x1491056ee1490051050051051490050050050056ee0051491490c50021491056b70c56b56e46866e31050050050050050050056460051490ff6e21491050ff0011050050050050050c56e20ff6e20046a069c0c514901e01e14910501e01e10500500501e0c501e01e0c50ff01e01e01e01e6e201e0ff,l2C 109 5 0 (w450::w504::v21) 0x100100000010010000110010010000100101a01a,l2C 109 5 0 [w450,w504,w551,w447,w446,w550] 0x1a00000000023a067,l2C 109 5 0 [w450,w504,w447,w446,w552] 0x1a01a001001001001004004004004001001001004000000000000,l2C 109 6 0 [w450,w504,w551,w447,w446] 0x100100100101a01a00101a01a01a01a01a01a01a01a6f201a01a00423a00423a00100123a00100100100423a01a01a01a01a01a01a00401a0000676f106700100100100101a01a6f023a00400423a,l2C 109 6 1 [w450,w504,w551,w447,w446] 0x6f3,l2C 111 7 0 [w399,w397,w395,w553,w425,w391] 0x19100200219100a00a00a00a19100a00a00a00a00200a1911910c90c90c90021910c40c40c400a00a00a00a0c900a19125500219100425500425500a00a00a00a0c90c90c90c90c90c902402425502402402400425519102402419102402402402400a00a0650c90c90c90c90240c9,l2C 111 7 0 (w399::w397::w395::w553::v18) 0x11700200211700500a00a0051910c40021910c90c400a0c400a0c400a00a00200a1910c90021910c40c40c40c40c40c40c90c90c40c400a00a00a00a00a0c900a00123c00123c0c42550010c40c90c92550010c90010c902402402400102401e02401e0c40240240c400a0260c90240240c9,l2C 47 5 0 [w58,w45,w554,w42,w41] 0x202d00006e12b02d02d002002000002000000002002002000,l2C 47 5 0 [w58,w57,w45,w554,w41] 0x20020020000020020000020000000000020000000000002c60020020002c6002002,l2C 47 5 0 [w47,w58,w44,w554,w41] 0x12b12b002000000002002002,l2C 47 5 0 [w47,w58,w45,w554,w555,w41] 0x12b00002d000002000,l2C 47 5 0 [w47,w58,w45,w554,w41,w548] 0x2d12b000000,l2C 47 5 0 [w47,w58,w554,w41,w389] 0x12b12b000000000000002002002000000002002002002002002000002,l2C 47 5 0 [w47,w58,w554,w556,w41] 0x12b12b00000000200200200000212b02d002,l2C 47 5 0 [w47,w58,w45,w554,w41,w557] 0x2d12b000000000000,l2C 47 6 0 [w47,w58,w45,w554,w41] 0x2d6fe02d12b00202d0020020026fd12b00200212b0020026fc00212b0000006fb00002d0006fa02d12b0020020020020026f912b0020020020020020026f80020020020020020026f700212b00200200212b002,l2C 47 6 1 [w47,w58,w45,w554,w41] 0x6ff,l2C 111 8 0 [w399,w397,w395,w553,w392,w391] 0x1170c47001170050c40050c41170050050050057000051171170c90021170c46b70c96b56f66866f50c400500500500500500564600511723c6f41170c423c0010c40050050050050c96f423c6f40046a069c0c901e01e23c01e01e01e6f423c11701e01e1170c401e01e0c400500501e0c901e01e0c9,l2C 107 5 0 [w434,w433,w438,w558,w471] 0x3101f00201f02101f02101f021031021002000000000000002002002000000000000002000000000,l2C 107 6 0 [w434,w433,w432,w438,w431,w558] 0x1f01f02103102100202102100002100200000000203100200200200200200070201f01f00000000200200200064900200200200000200000257f000000000662,l2C 107 6 1 [w434,w433,w432,w438,w431,w558] 0x703,l2C 107 5 0 (w559::w534::v52) 0x3f000000239000000000000000,l2C 43 4 0 [w560,w403,w402,w400] 0x0,l2C 43 4 1 [w560,w403,w402,w400] 0x706,l2C 43 4 0 [w561,w403,w402,w400] 0x2002000000000000,l2C 43 4 1 [w561,w403,w402,w400] 0x708,l2C 107 5 0 (w562::w534::v19) 0x400400000400000000000001f01f03f00403f00003f022022,l2C 107 5 0 (w562::w534::v52) 0x2200000001f00001f000,l2C 41 3 0 [w565,w564,w563] 0x0]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB24 : Array L2Cell := #[l2C 41 3 0 [w568,w567,w566] 0x0,l2C 41 4 0 [w568,w564,w563,w566] 0x70d00000000000070c000000000,l2C 41 4 1 [w568,w564,w563,w566] 0x70e,l2C 107 5 0 [w534,w433,w432,w438,w569] 0x3f00003f00303f0000000d20d200300300300070f00200207f004000000000003,l2C 43 4 1 [w403,w402,w400,w570] 0x70f,l2C 43 4 0 [w403,w571,w402,w400] 0x0,l2C 43 4 1 [w403,w571,w402,w400] 0x712,l2C 107 5 0 [w534,w433,w432,w572,w438,w431] 0x303f01f003000000,l2C 107 6 0 (w534::v52) 0x200063600063600200303f71400000303f00200063663663600201f01f01f00300071300071100300263600363663663671000200263600000200000002200070b70a000000709000000707003705000003,l2C 107 6 1 (w534::v52) 0x715,l2C 107 5 1 (w434::w534::v52) 0x636022,l2C 43 4 0 [w403,w402,w573,w401] 0x2002000000000000000000002002,l2C 43 4 1 [w403,w402,w573,w401] 0x718,l2C 111 6 0 [w397,w396,w395,w392,w574,w391,w533] 0x112c9000000023002,l2C 107 5 1 [w434,w534,w433,w438,w431,w471] 0x636,l2C 111 7 0 [w397,w396,w395,w393,w392,w574,w391] 0x1c00000001c00700100100701571b01e01501500100100171a00100000b00000b0150150157176860010010010000000000090150190150090150090090670090150010010000002c90c70002c90a60c77190c70190190150150c70190150150150153120c70013123110c76360c77170c731101e0c6,l2C 103 5 1 [w380,w379,w524,w575,w376] 0x64e,l2C 79 5 0 [w149,w148,w200,w145,w186] 0x44044000000001001001001000001000000001001001000000,l2C 79 5 1 [w149,w148,w200,w145,w186] 0x71e,l2C 103 5 1 [w380,w379,w510,w524,w376,w464] 0x0,l2C 111 7 0 [w399,w397,w398,w393,w392,w574,w391] 0x380006bf03804f00100104f02072003702002000100100171f00100002200002202002002000071d0010010c76640c70190c70190200c71e31290c70c7037704020020020037020020037037001037653037000,l2C 110 5 0 [w408,w429,w406,w405,w576,w404] 0x15301f000000067,l2C 110 5 0 (w408::w406::v24) 0x200200300300200201f01f30a30a002002002003000000000000,l2C 110 6 0 (w408::w429::v14) 0x200200200215300300315300200215300200200200315301f00201f01f01f01f01f01f01f01f01f72301f01f15301f01f01f01f00301f15300200200200200006772206715300300315301f01f637,l2C 110 6 1 (w408::w429::v14) 0x724,l2C 110 5 0 (w430::w407::v14) 0xa70a70020a70020020000000a70a700200201f1a3,l2C 110 5 0 [w430,w577,w406,w405,w537,w404] 0x1a301f000000067,l2C 110 5 0 [w430,w406,w405,w578,w404] 0x200200300300200201f01f003003002002002003000000000000,l2C 110 6 0 (w430::w577::v14) 0x20020020021a30030031a30020021a30020020020031a301f00201f01f01f01f01f01f01f01f01f72801f01f1a301f01f01f01f00301f1a30020020020020000677270671a30030031a301f01f726,l2C 110 6 1 (w430::w577::v14) 0x729,l2C 107 5 1 [w434,w433,w432,w579,w431,w558] 0x0,l2C 103 5 1 [w380,w379,w378,w580,w376,w464] 0x0]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB25 : Array L2Cell := #[l2C 42 3 1 [w419,w418,w417] 0x0,l2C 111 7 0 [w399,w397,w395,w393,w392,w581,w391] 0xc00000000c00500100072d00100500100501572c06701501500100100100000100000e00000e0150150150000010010010000c70000a60c60150150c70010c70c70000c70c70c701501511572b001106015015115115001115115000,l2C 107 5 1 [w434,w445,w432,w438,w579,w431] 0x649,l2C 111 6 0 [w399,w397,w393,w574,w581,w425,w391] 0x318000317015106015000,l2C 111 7 0 [w399,w397,w395,w393,w392,w574,w581,w391] 0x72d1a81061fc7300a60c701501510601572f,l2C 111 7 0 [w399,w397,w395,w393,w392,w582,w391] 0xc0a600000c0c40010013800c60000c62c30c61e40c60010010010000010a615900029f0c60c60c60000010010010000a60150c60c60c70c70000c70c60c72700c77192700000c60093160090c60bd0bd0c60c6270270001270270000,l2C 47 5 0 [w47,w58,w43,w583,w389] 0x21002021002021000000000000002002002000000000002002002000002002002000002000,l2C 47 5 1 [w47,w58,w43,w583,w389] 0x733,l2C 79 5 0 [w149,w148,w147,w584,w186] 0x13001013001013000000000001001001000001001001000001000001001000001000000000,l2C 79 5 1 [w149,w148,w147,w584,w186] 0x735,l2C 111 7 0 [w399,w397,w395,w393,w392,w574,w391,w481] 0xfa0a60000fa00c57f00966200073673401900066266400001e00057f649,l2C 110 5 0 [w430,w406,w585,w405,w404] 0x20020a70a70000a70000000031a3,l2C 110 6 0 [w430,w406,w428,w405,w404] 0x200000000200300300300368200301801801801800200200300300200201801801801801801801801f018002000000002000000000000003003003003738003018018018018,l2C 110 6 1 [w430,w406,w428,w405,w404] 0x739,l2C 111 6 0 [w397,w395,w392,w574,w391,w533,w507] 0x1801102d000000000,l2C 107 5 0 [w435,w434,w438,w569,w471] 0x210d20210d20210000000000000000000020020020000000000d20020d2002002000002000000002,l2C 107 5 1 [w435,w434,w438,w569,w471] 0x73c,l2C 111 7 0 [w399,w397,w395,w392,w574,w391,w533] 0x1a80dc02d00000002d00c0dc0dc00c0110000dc0dc0dc01173d0352830020020020100020100110110110027340dc73600002300002301166200200200271f03503503571a63603503573b0356490dc0dc0111bf011035011011035002,l2C 110 5 0 [w451,w430,w429,w405,w537,w404] 0x15a000000000018,l2C 110 6 0 [w451,w430,w429,w405,w404] 0x200200200200200215a00215a00200200215a00200267d00215a00200200200200000073f00015a00200200200200265815a018018018018018002018018018018018018018018018018002018018,l2C 110 6 1 [w451,w430,w429,w405,w404] 0x740,l2C 43 4 1 [w587,w437,w402,w401,w586] 0x2,l2C 107 5 0 [w435,w434,w433,w438,w569,w471] 0x21000000000000002000,l2C 107 6 0 [w435,w434,w433,w438,w431,w471] 0x202101f02101f02102100002100200000000000000200200274373c00066200200000074200200200200063600001f00201f002002002002702000002002002000002649,l2C 107 6 1 [w435,w434,w433,w438,w431,w471] 0x744,l2C 97 3 1 [w528,w588,w527] 0x0,l2C 107 6 0 [w435,w434,w433,w432,w431,w589] 0x20020020000000000120000120020020026bf000022000022002000000662002002002000636000002746002002000002,l2C 107 6 1 [w435,w434,w433,w432,w431,w589] 0x747647,l2C 111 7 0 [w399,w397,w395,w393,w392,w574,w391,w590] 0xc0a60dc3810001e3734636233000,l2C 110 5 1 [w495,w430,w406,w482,w404] 0x681,l2C 69 3 1 [w591,w139,w138,w137] 0x0,l2C 111 7 0 (w592::w399::v59) 0xdc24e24e00028300c0dc00c0dc0dc0dc74b24e24e24e00274a00200200000200215900229f24e0000020020020002402402400006360a610600037f0dc2402402400002402400021bf00c0dc00c0dc0a60c40a6000380]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB26 : Array L2Cell := #[l2C 111 8 0 [w399,w397,w395,w393,w392,w574,w391] 0xdc00c0a674c7497480dc00c1a80050a66c16c16c11a80050dc0090090097450dc00901e00900900900900970f0090dc6d31a87416c173e6c10dc0dc1e30020dc0a664b1e300e64b64b1e300e00900900900900900964b6860091a86c11e36c100373a6461a80dc0c77370dc0a67320c701973172e0c701900900900900964e0091a80c70011a81e372a0c772564b64b7211e301e01e0c701e01e01e71c7160c70dc01e01e01e7040dc00900900900900900901e0090090091a801e01e01e01e6c101e6511a81e301e01e01e62f1e3,l2C 47 5 0 (w593::w57::v34) 0x20020020000020020000020000000000020fa0000020fa05c1dd,l2C 47 5 0 [w47,w594,w43,w41] 0x200200200200000200200200200200200200205c002002,l2C 47 5 0 [w47,w594,w57,w43,w41] 0x5c05c00200000200200000205c002,l2C 47 5 0 [w47,w57,w45,w43,w595,w41] 0x5c000000000000,l2C 47 5 0 [w47,w57,w45,w43,w41,w596] 0x5c000000000,l2C 42 3 1 [w597,w419,w427,w417] 0x0,l2C 47 5 0 (w47::w57::v35) 0x5c05c000000000000002002002002000002000002002000002,l2C 47 5 0 [w47,w57,w43,w56,w41] 0x5c05c000000002000000002002002002000002,l2C 47 5 0 [w47,w57,w45,w43,w41,w549] 0x5c000000000000000,l2C 47 6 0 (w47::w57::v34) 0x54200075600005c00200200200200275505c00200205c00200275400205c00075375254200000075100005c00200275074f00200205c00200200200200263600200200200200200200205c00200200205c00200274e002,l2C 47 6 1 (w47::w57::v34) 0x757,l2C 43 4 1 [w587,w403,w402,w598,w401] 0x2,l2C 111 6 0 [w396,w395,w393,w392,w420,w391,w532] 0x20010000f200029900028529a,l2C 42 3 1 [w599,w419,w427,w417] 0x0,l2C 109 5 1 [w450,w542,w600,w447,w446,w550] 0x1a,l2C 105 4 1 [w602,w531,w514,w530,w601] 0x4,l2C 107 5 0 [w534,w433,w432,w558,w471] 0x1f01f05c05c002002000000000000002002000000000000,l2C 107 5 1 [w434,w534,w433,w432,w558,w471] 0x75e,l2C 111 7 0 (w397::w396::w395::w393::v28) 0x1e01c00201500001501c75f0020020070070026c700701c01c01c75d0020026b900b00200200b00b01c00200200268600200200275c00200c01c01901c00c01c00c00c06700c01c00c00072b75b0000020020020db0020db01901901c01c0db01901c01c01c01c18a0db75a18a0f20db7590f229a0db0020db0020db29a01e0bd,l2C 103 5 1 [w380,w510,w377,w538,w465] 0x670,l2C 103 5 1 [w380,w379,w510,w377,w538,w464] 0x0,l2C 111 7 0 (w399::w397::w398::w393::v28) 0x370380020206bf02003876200200204f04f0026d565504f0380380380000020020020220000020220220380000006750000000db0190db0190380380380db7611be0c80db0db0380380380370380380377040370376c2037037000,l2C 69 2 1 [w139,w523,w137] 0x0,l2C 111 7 0 (w399::w397::w395::w393::w536::v28) 0x201a00001a00c00000500075d7642201be00001900000075901e000000,l2C 103 5 1 [w380,w378,w377,w466,w376,w603] 0x0,l2C 103 5 0 [w380,w379,w378,w466,w538,w464] 0x0,l2C 103 5 1 [w380,w379,w378,w466,w538,w464] 0x767,l2C 111 7 0 [w399,w397,w395,w393,w392,w420,w391,w532] 0x200100000200c57f63d0500096627681a76697640751be67501976657f75a01e72b662,l2C 107 5 1 [w435,w434,w433,w432,w604,w471] 0x0,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w605] 0x6701c00000900000901c76a00000500000501c01c01c0000000026b900e00200200e00e01c0020020020000020020020000020020bd01c01c0db7660db0000db0db0020db0db0db01c01c0fa09d01c01c107000107107000107107002,l2C 103 6 0 [w380,w379,w377,w606,w376] 0x2060030000000006b97646b96b90000006b90000006b90000006b97640006b90000006b97640006b90007647647647640002060002060002060002067642066b96b96b92067646b92066b90006b9691206]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB27 : Array L2Cell := #[l2C 103 6 1 [w380,w379,w377,w606,w376] 0x76c,l2C 107 5 0 [w534,w433,w432,w558,w569] 0x3f01f03f01f03f00000000200000300005c05c00203f00203f03f00000007f002000003,l2C 107 5 1 [w534,w433,w432,w558,w569] 0x76e,l2C 111 6 0 [w399,w397,w393,w392,w425,w532,w533] 0xa0020020110000020000000ca,l2C 105 4 1 [w602,w531,w514,w530,w607] 0x0,l2C 111 7 0 [w399,w397,w395,w393,w392,w532,w533] 0x52a201e0500050500050007710020116bf01105000000c00c0020500020050500500050020020020026b901000200201001000200277000205005005000200000000202300002305075d00200200200003503503575d76f02d01e03501e00c00c0356d4050035035050050035002,l2C 111 6 0 [w396,w395,w393,w392,w540,w391,w532] 0x1c00000000000029a000,l2C 46 3 1 [w487,w486,w485,w608] 0x2,l2C 104 3 1 [w612,w611,w610,w609] 0x0,l2C 41 3 1 [w568,w564,w563,w566] 0x0,l2C 111 7 0 [w399,w397,w395,w393,w392,w540,w391,w532] 0x201300001300c7710097767750056d70007640991be77477301e000000000,l2C 107 5 0 [w435,w434,w433,w455,w558,w471] 0x0,l2C 107 6 0 [w435,w434,w433,w432,w558,w471] 0x3101f00201f01f02102100203100200200000000000000200200200068900057f00200000077800200200200075e00001f00201f021021002002000002702002002000002,l2C 107 6 1 [w435,w434,w433,w432,w558,w471] 0x779,l2C 111 8 0 (w399::w397::w395::w393::v28) 0xc01e00c0020020bc0090027480bc00900c00c00c00c77a00c0500bc7770bc0020020500020050050020026d968c05000500c00c00c00c00c00c77200c00200200276d1be00e0020021be00200e00e00c00c00c00c00200c0bc0021be0020026860020bc0500021be00200273a0020500020020db01900276b0db01900c00c00c00c67000c0bc0db7690bc0500db7650501be0020db0020020027631be01e01e0db01e01e01e7607580db00c00c00c00c00c00c01e00c00c00c0bc01e01e01e7040bc05001e01e01e01e6c401e0501be01e01e01e0021be,l2C 79 5 0 (w613::w181::v36) 0x10010000010010010010000000010000000a60000010a603e1dc,l2C 79 5 0 [w148,w181,w147,w614,w217,w145] 0x3e000000000000,l2C 79 5 0 [w148,w182,w147,w145] 0x100100100100000100100100100100100100103e001001,l2C 79 5 0 (w148::w182::v10) 0x3e03e00100000100100000103e001,l2C 15 3 1 [w5,w272,w4,w3] 0x0,l2C 79 5 0 [w148,w181,w147,w217,w145,w615] 0x3e000000000000000,l2C 79 5 0 [w148,w181,w147,w185,w145] 0x3e03e000000001000000001001001001000001,l2C 79 5 0 [w148,w181,w147,w217,w145,w215] 0x3e000000000000000,l2C 79 5 0 (w148::w181::v11) 0x3e03e000000000000001001001001000001000001001000001,l2C 79 6 0 (w148::w181::v36) 0x100103e00100178400103e78000078300003e00100100100100178203e00074b78178003e00100177f77e00100103e00100000077d0000010010010016a600103e00100100103e00100100100100100100100177c001,l2C 79 6 1 (w148::w181::v36) 0x785,l2C 103 5 0 (w616::w525::v53) 0x3f000000153000000000000000,l2C 71 4 0 [w617,w387,w362,w462] 0x0,l2C 71 4 1 [w617,w387,w362,w462] 0x788,l2C 71 4 0 [w618,w387,w362,w462] 0x1001000000000000,l2C 71 4 1 [w618,w387,w362,w462] 0x78a,l2C 103 5 0 (w619::w525::v12) 0x300300000300000001a01a00000003f00303f00003f018018]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB28 : Array L2Cell := #[l2C 103 5 0 (w619::w525::v53) 0x1800000001a00001a000,l2C 70 3 0 [w620,w264,w263] 0x0,l2C 70 3 0 [w265,w621,w262] 0x0,l2C 70 4 0 [w265,w264,w263,w262] 0x78f00000000000078e000000000,l2C 70 4 1 [w265,w264,w263,w262] 0x790,l2C 103 5 0 [w525,w378,w421,w376,w465] 0x7407400000000000000003f00403f03f004004000004791001001052003000000000004,l2C 71 4 1 [w387,w362,w462,w622] 0x791,l2C 71 4 0 [w387,w623,w362,w462] 0x0,l2C 71 4 1 [w387,w623,w362,w462] 0x794,l2C 103 5 0 [w525,w378,w377,w624,w376,w465] 0x1a00403f004000000,l2C 103 6 0 (w525::v53) 0x1a01a01a0006a60010006a60010006a60016a66a600179600403f00000403f0007950040007930040016a60046a66a66a679200100000001800078d78c00000078b0000007890016a6000001004787000004,l2C 103 6 1 (w525::v53) 0x797,l2C 107 5 0 [w534,w433,w432,w431,w480] 0x2205c00000005c00003f03f05c05c05c00400001f05c00005c004004,l2C 107 5 1 [w534,w433,w432,w431,w480] 0x799,l2C 111 7 0 (w397::w396::w395::v50) 0x400400000401c00000001c01500000001500700400400700b00000b00b00000b00b00b00400b06700b00000000000000400400b00b00b06700b00b09e79a09e00001f09e01f00b09e03709e037,l2C 111 7 0 (w397::w625::v60) 0x40040000042a42a400b00b00000b00b00b00400b06700006700000400400b00b06700b01c06700001c01506700001500700400400700b06700b00b17200017200000b17213e17213e17200b00b00b,l2C 15 3 1 [w5,w4,w3,w626] 0x0,l2C 111 6 0 (w397::w396::w395::w454::v29) 0x1c000000000018,l2C 111 6 0 [w397,w396,w395,w393,w392,w391,w627] 0x1500000b000000000,l2C 111 7 0 (w397::w396::v58) 0x101500101500700101c00079f01c00700779e00706700700100100100400400b00400b00700700700400000000079d03e00100103e0070070070070676a800700703f00400403f02c6a602c00101802c01802c00702c02c0e402c,l2C 111 6 0 [w397,w628,w395,w393,w392,w391,w605] 0x700000000003f01c,l2C 111 7 0 (w397::w628::v60) 0x2a32a30070070000070010010010040070070070040000677a106703e00100103e0070070070070676a800703f00400403f01c06700001c01500100101500706700b00400400b0070070ff0000ff0010070ff0ff0ff1de0ff0ff007007007,l2C 111 6 0 [w396,w395,w393,w392,w420,w391,w605] 0x20150000150000002852c7000,l2C 107 5 1 [w434,w433,w432,w579,w431,w604] 0x0,l2C 107 5 1 [w434,w534,w433,w432,w604,w471] 0x0,l2C 111 7 0 [w397,w396,w395,w393,w392,w391,w605] 0x6701c00001500001501c7a500000779f00701c01c01c0000000006b900b00000000b00b01c00000000000000000000075c00001c01c01c06701c01c01c0007a47a10000000000020db00201c01c0db7a30db0db1070db,l2C 111 7 0 (w629::w397::v60) 0x1c01c01c00000000000000000000000000001c01c06701c06700006700006700001c01c01c1a578b1a50001a51a523b1a523b1a501e01c01c01c01c01c01c06701506700001500706700000700b06700000b01c01c,l2C 109 5 0 [w450,w504,w630,w447,w446] 0x100100000010010000010000000000423a,l2C 109 5 0 [w450,w504,w447,w446,w631] 0x427f00100100000000007f07f07f000000,l2C 109 6 0 [w450,w504,w600,w447,w446] 0x10000010040010010040010010040040040047a900402202202202202202202202202202201a01a01a0000000000000010000000010040040040047a8004022022022022,l2C 109 6 1 [w450,w504,w600,w447,w446] 0x7aa,l2C 109 6 0 [w450,w542,w600,w447,w446] 0x100100100100100100100100100101a01a01a01a00400400400401a01a01a01a01a01a01a02201a00000000000000100100100100400400400401a01a01a01a01a01a]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB29 : Array L2Cell := #[l2C 109 6 1 [w450,w542,w600,w447,w446] 0x7ac,l2C 47 5 0 [w58,w57,w632,w43,w41] 0x5c00005c05c00005c00000000005c00000005c000002183,l2C 47 5 1 [w58,w57,w632,w43,w41] 0x7ae,l2C 111 7 0 (w397::w396::w633::v13) 0x1131260011130071260071261130070070070077af00711311300b00b11312600b00b00b00b00100b12600700700b11300000011312600100112600700700700700700700b00b00b00b1131251251256a611312612512512500112600700700700700b00b00b00b12500b12515b135,l2C 47 5 0 [w58,w57,w45,w59,w41] 0x5c00005c05c00005c00000000005c00000005c000002183,l2C 47 5 1 [w58,w57,w45,w59,w41] 0x7b1,l2C 111 7 0 [w397,w396,w395,w634,w392,w391] 0x1141280011140071280071281140070070070077b200711411400b00b11412800b00b00b00b00100b12800700700b11400000011412800100112800700700700700700700b00b00b00b1141271271276a611412812712712700112800700700700700b00b00b00b12700b12715c135,l2C 47 5 0 [w58,w57,w45,w43,w389] 0x5c05c00005c000000000000002183,l2C 47 5 1 [w58,w57,w45,w43,w389] 0x7b4,l2C 111 7 0 (w397::w396::w395::v17) 0xe60000000e60e50040040e50e60040e50040047b50040e60e600b00b00b7b50e60150150150e500b00b00b00b0e50e60000000e60000000000000e50040040040040e500b00b00b00b0e60300300307b50e60300300300300e50300300e500b00b00b00b03002417e,l2C 109 5 0 [w450,w449,w542,w447,w446,w550] 0x124000000022000,l2C 109 5 0 (w450::w449::v33) 0x12412400100100100107f07f00107f000000,l2C 109 6 0 [w450,w449,w542,w447,w446] 0x10010010011240010010011240010010011240010017b80011240220220220220220010221240220220220220010221240000007b7000001001001001124001001001001001656124022022022022,l2C 109 6 1 [w450,w449,w542,w447,w446] 0x7b9,l2C 109 5 0 [w450,w504,w448,w635,w446] 0x1001100001000000100100001001152152,l2C 109 5 0 [w450,w504,w542,w635,w446,w550] 0x152000000022000,l2C 109 5 0 [w450,w504,w635,w446,w543] 0x15215200100100100107f00107f07f000000,l2C 109 6 0 [w450,w504,w542,w635,w446] 0x10010010011520010010011520010220220010010011520010017bd0011520220220220221520220220220220010221520000007bc0000010010010011520010010010010017bb152022022022022,l2C 109 6 1 [w450,w504,w542,w635,w446] 0x7be,l2C 111 6 0 [w396,w395,w393,w392,w420,w391,w636] 0x15000000299000000,l2C 111 6 0 [w397,w396,w393,w392,w425,w391,w636] 0x1c05c0150e5000223000,l2C 47 5 1 [w58,w57,w45,w56,w41] 0x42c,l2C 100 3 1 [w640,w639,w638,w637] 0x0,l2C 111 7 0 [w397,w396,w395,w393,w392,w391,w636] 0xb01c05c01500001501c7c305c05c00700705c0047c200701c01c01c00401c01c01c00b01c01c00b00b7c100b7b500b00b00400b05c06700005c01c00000400400b00013701913701901c01c01c13779a1377c000b1372740bd,l2C 111 7 0 (w397::w396::w395::v37) 0x10ab0010ab0070070ab0070010ab01c01c01c00411e00411e0ab00111e0010010010040ab0070070070070070070000000000000ab0010010ab00700700700700700711e00400411e0230230230230ab0230230230010ab00700700700702300711e02302302302311e023035135,l2C 109 5 0 (w450::w504::w641::v33) 0xfa000,l2C 109 5 0 [w450,w504,w447,w642,w446,w543] 0x1000000000,l2C 109 5 0 [w450,w504,w447,w446,w503] 0x1000001001000000000000000000000000000669000000000000000,l2C 109 5 0 [w450,w504,w447,w643,w446] 0x1a01a000000001001000000000000000000000000000000,l2C 109 5 0 (w450::w504::v38) 0x7407400000000007f00007f07f07f00000107f00000007f000,l2C 109 4 0 [w450,w644,w543,w645] 0x1074001074074000000000000,l2C 109 5 0 (w450::w447::v38) 0x740740000000000010010010010010010000017cb07f07f000669001000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB30 : Array L2Cell := #[l2C 109 5 0 (w450::w504::w447::v38) 0x100100000000000107f,l2C 109 5 0 [w450,w504,w447,w446,w646,w543] 0x1a07f00007f000,l2C 109 5 0 [w450,w504,w447,w647,w446] 0x1a01a00000000100107f00000007f07f07f00007f00000000000007f,l2C 109 5 0 [w450,w504,w447,w543,w645] 0x101a00101a01a0fa0fa0000010010010000000010010010007cb000000001000,l2C 109 5 0 [w450,w504,w648,w447,w543] 0x10010fa0010010fa000000001001001000000000,l2C 109 5 0 (w450::w504::w649::v33) 0x1a0fa000001000,l2C 109 6 0 (w450::w504::v33) 0x1a01a01a7d20010010000010010fa7d10010007d00fa0007cf07f0007a907f0fa07f7ce07f0017bd07f7b87cd7cc7ca07f0007c90000007c80000fa0000000fa0010007c700107f0007c607f,l2C 109 6 1 (w450::w504::v33) 0x7d3,l2C 109 5 1 (w516::w504::v33) 0x6e0,l2C 111 7 0 (w397::w396::w395::w393::v29) 0x701c00101500101501c0ab00101c0070ab0010ab01c01c01c01c01c01c00700701c01c00400b00400b01c11e00401c00100100100400700711e7af00700400700006779f06701c00000001c0070070007d500779e00702301902301901c01c02302301c0236a601c0230010070230230070230230350bd,l2C 111 7 0 [w650,w397,w396,w395,w392,w391] 0x1c01c01c01c01c01c01c01c23800128000100100100423801c01c01c01c23800100123828000400428000700700700700700701c01c01c01c01c01c2381ba1ba1ba0012382801ba1ba1ba1ba2801ba2960bd00700700700701c01c007238007007238007007007007007004007007,l2C 111 7 0 [w397,w396,w395,w393,w392,w651] 0x1c00701c01c01c01c01c00724100724101c01c01c01c24100128800100100100424100700700700700700700400701c01c01c01c24100100124100700700700700700728800400428801c01c01c01c01c01c2411c11c11c10012410070070070072881c11c11c11c12881c12a00bd,l2C 111 8 0 (w397::v60) 0x1c01578601c00701500101501c7d80077d77d67d47c501c01c00b7c401c0157bf00b7ba7867867b60150077b300b7b00047ad7ab00701c7a77a601c0157867860150077a26e27a06aa00700b79c79b00b01c01901901979801c01501901901978601500701901900700b01901901901900b01901e019,l2C 111 6 0 (w399::w396::w411::v51) 0x15000000000022,l2C 111 6 0 [w399,w396,w395,w393,w392,w652,w391] 0x1c000007000000000,l2C 111 7 0 (w399::w396::w395::v50) 0x200200200301c00200201c0150007db01500700300300700b00200b00b7da00b00b00b00300b06700b05c00200205c00000000046103f00300303f00b00b00b00b06763800b00b03700203763603703702203702203700b09e09e,l2C 111 6 0 [w399,w625,w395,w393,w392,w581,w391] 0x3f00b000000015,l2C 111 7 0 (w399::w625::v60) 0x20020020032a42a400b00b00000b00b00b00300b05c00200205c0000677dd06703f00300303f00b00b00b00b06763800b01c00200201c01506700001500700300300700b06700b00b13e00213e00013e13e00b13e17217201900b00b00b,l2C 103 5 1 [w525,w378,w377,w524,w376] 0x6bd,l2C 111 7 0 (w399::w396::v58) 0x1500001500700001c00000001c00700700000706700700300300000300300b00300b0070070070030000000000000070070070670070070030030e40000e47df01a0e401a0070e402c02c02c,l2C 111 7 0 (w399::w628::v60) 0x2a32a300700700000700300300000300700700700306700006700000700706700700300301c06700001c01506700001500706700b00300300b0070070070190070071de0001de0000071de0ff0ff0ff,l2C 111 6 0 [w396,w395,w393,w392,w581,w391,w532] 0x101c00001c0000f200000018a,l2C 103 5 1 [w380,w378,w377,w580,w376,w603] 0x0,l2C 110 5 1 [w430,w429,w428,w405,w537,w404] 0x1f,l2C 103 5 1 [w380,w525,w378,w580,w376,w464] 0x0,l2C 111 7 0 [w399,w396,w395,w393,w392,w581,w391] 0x1c00000001c00700000072d0000070000070157e506701501500000000000000000000b7db00b0150150150000000000007e40007e30150150150670150150150000007dd0001157e20011150010150151151150c70c7,l2C 111 7 0 (w399::w653::v60) 0x1501501500000000000000006700001501506701506700006700001c06700001c01506700706700000700b06700000b0150151fc0000150150151fc7091fc1fc1fd1fd1fd019019015015015015015,l2C 79 5 0 [w149,w181,w654,w217,w145] 0x3e03e00003e03e00000000000003e00000003e00000118e,l2C 79 5 1 [w149,w181,w654,w217,w145] 0x7e8,l2C 111 7 0 (w399::w396::w633::v13) 0x11312600211300712600712611300700700700700200711311300b00b11312600b00b00b00b7e900b12600700700b11300200211312600000012600700700700700b00b00b00b00b00b11315b15b15b00211312615b15b15b63612600700700700715b00700b00b00b00b12512513f,l2C 111 7 0 [w399,w396,w395,w634,w392,w391] 0x11412800211400712800712811400700700700700200711411400b00b11412800b00b00b00b53900b12800700700b11400200211412800000012800700700700700b00b00b00b00b00b11415c15c15c00211412815c15c15c63612800700700700715c00700b00b00b00b12712713f,l2C 111 7 0 (w399::w396::w395::v17) 0xe60020020e60e50030030e50e60020e50020020020030e60e600b00b00b0020e60150150150e500b00b00b00b0e50e60020020e60000000000000e50030030e500b00b00b00b00b00b0e60240240240020e60240240240240e50240240240240e500b00b00b00b02400b030030171]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB31 : Array L2Cell := #[l2C 110 5 1 (w408::w406::v24) 0x723,l2C 111 7 0 (w399::w396::w395::v51) 0x1c00200201c0070030030070e60150020e600b0150e50150030150020020020030e600b0020e601501501501501501500b00b0150150e500b53900b00300b0e50000677db06701500000001500b00b0007ed00b7da00b02400202401e02401e01501502402401502463601502402400b02402400b030106,l2C 111 7 0 (w399::w396::w655::v13) 0x20001501520001501501501520000225300200200200320020000b00b20001501500b25300b00b00b00b00300b25320000200220001501501501525300300325300b00b00b00b00b00b2001ff1ff1ff0022000150150150150150152531ff1ff1ff1ff25300b00b00b00b271271106,l2C 111 7 0 [w399,w396,w395,w393,w656,w391] 0x20201501520201501501501501500b01520200225700200200200320220200b00b20225700b00b00b00b00300b25720200200220201501501501525700300325700b00b00b00b00b00b20220120120100220201501501501501501525720120120120125700b00b00b00b272272106,l2C 79 5 0 [w149,w181,w147,w217,w186] 0x3e03e03e00000000000000118e,l2C 79 5 1 [w149,w181,w147,w217,w186] 0x7f1,l2C 111 7 0 (w399::w396::w395::v37) 0xab0000ab0070070ab0077f20ab01c01c01c00311e00311e0ab00311e0030037f20030ab0070070070070070070000000000000ab0000000ab00700700700711e00300300300311e0350350350350ab0350350357f20ab00700700700711e03503511e02302313f,l2C 79 5 0 [w149,w181,w217,w185,w145] 0x3e03e00003e00000000000000118e,l2C 79 5 1 [w149,w181,w217,w185,w145] 0x7f4,l2C 111 6 0 [w399,w396,w395,w392,w540,w391,w533] 0x1c01c03e11e242000000,l2C 111 7 0 [w399,w396,w395,w393,w392,w540,w391] 0x1c03e00001c0157750070150070150150150070077f60077f201501503e03e00b00b03e0037f500b01501501500300700700700303e06700003e01500000700000300314b77314b01e14b01e01501501514b7df00714b25a106,l2C 111 8 0 (w399::v60) 0x1c01575801c0070157f701501c6d30077417587587f301c01c00b00201c0157f000b7ef7ee6867ec0150077eb00b7ea00373a64600701c75875801c0157e77e60150077e17e000700b7de7257dc63a00b01c01e01e01e75801c01501e01e01e71601500701e01e01e01e00700b01e01e00b019019019,l2C 111 6 0 (w399::w396::w398::v51) 0x1502202000e037000022,l2C 103 5 1 [w380,w525,w378,w377,w575,w376] 0x18,l2C 111 7 0 (w399::w396::w395::w398::v13) 0x200200200401c02200201c0150227fa01500702200400700b00200b00b7f900b00b00b00400b01900b03800200203802000000002004f00400404f00e00b17e01e00b00b00b00e00b00e00e00b06763800b00e00b03700203771703703700403702203702201e00b03701e00b03700b00b00b019171,l2C 79 5 0 [w149,w181,w147,w657,w186] 0x1001001000000013013000000000000001001000000001001,l2C 79 5 1 [w149,w181,w147,w657,w186] 0x7fc,l2C 111 7 0 [w399,w396,w395,w393,w536,w392,w391] 0x1a01500101500700101c01a00001c0070077590077fd01900700100100100401a01a00b00b01a00400b00700700700400000000100100500701e0070050070050050670050070040040e47590e400101a0e401a01e0070e401e0070070070e40070e400401913f,l2C 69 3 1 [w658,w139,w138,w137] 0x0,l2C 103 5 0 [w525,w378,w466,w376,w464] 0x3e03e01a01a001001000000000000001001000000000000,l2C 103 5 1 [w380,w525,w378,w466,w376,w464] 0x800,l2C 111 7 0 (w399::w396::w395::w393::v15) 0x1c00100001c00700100172d0010070010070158010190150150010010017d400100100100b00b0017fa00b01501501563c0010010017e400076600901501e0150090150090090670090150090010017ff0002c711575a2c700111500111501e01e01501511501e015015015015299115001115001115299285115630285019106,l2C 71 4 0 [w387,w362,w659,w360] 0x1001000000000000000000001001,l2C 71 4 1 [w387,w362,w659,w360] 0x803,l2C 111 6 0 [w399,w396,w393,w392,w425,w391,w481] 0xf0000242c8000001,l2C 103 5 1 [w380,w525,w378,w377,w465,w464] 0x6a6,l2C 111 7 0 [w399,w396,w395,w393,w392,w391,w481] 0x1901c00001500001501c80600000700000701c01c01c6c57d400200b00200b01c00200200280500200200200000200c01c01e01c00c01c00c00c06700c01c0000000000000020020fa10780410701e01e01c01c10701e01c01c01c01c2c81070002c83101076a61076c510731030f10700230f01909d,l2C 111 7 0 (w399::w397::w396::w395::v50) 0xe06700b26f00b03703709e00430d03700b,l2C 111 7 0 (w399::w397::w625::v55) 0x200200200400200b00b00b7ff00b00b00b00400b00c00200200c00906700000900500400400500b06705c1720021720001727ff17203f17200417200b00b00b00b00b17263800b13e17e00b30c00b00b00b00b0da0da13e17213e17200b00b17213e00213e00013e13e00413e00b00b13e00b17100b37700b00b00b378,l2C 111 7 0 (w399::w397::w396::v58) 0x506700737902c0070030e402c23c00702c,l2C 111 7 0 (w399::w397::w628::v55) 0x100700700775b00700100100100400700700700400c06700000c00900100100900706700e00400400e2c400713f0ff0070070071490071490ff0000ff0010070070ff0070ff0ff0040ff1350072840070070072c50ff0ff0ff0ff0070070ff0001de75b1de03e1de0011de0070070070070071de6a800703f1de0041de,l2C 79 5 0 [w149,w181,w660,w217,w145] 0x100100000100100100100000000100000000000030e00100100030e000000001001]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB32 : Array L2Cell := #[l2C 79 5 1 [w149,w181,w660,w217,w145] 0x80c,l2C 111 7 0 [w399,w397,w396,w395,w393,w392,w581,w391] 0x700906701527080d1150c737a001,l2C 111 7 0 (w399::w397::w653::v55) 0x100100000101501501500000100100100000c06700000c01506700500100100500e06700000e1fd0000150151fd0151fd0011fd1fd0001fd0c60152c30150150151fe1fd1fd0150151fc0000150151fc0151fc1fc0011fc1fc00010601530b015015015283,l2C 47 5 1 [w58,w57,w45,w554,w41] 0x6f8,l2C 111 7 0 [w399,w397,w396,w395,w393,w392,w391,w605] 0xb00c06701c37b0021070db252810,l2C 111 7 0 (w629::w399::v59) 0x1c01c01c00000200200000200200200000201c01c1a501c1a50001a50001a51a50021a51a51a501c01c0bd01c00c01c01c01c00c01c01c23b01c23b00023b23b00023b23b00209d01c00c01c01c01c00c01c06700906700000900506700000500e00200200e,l2C 111 7 0 (w399::w397::w396::w633::v13) 0x700700200700b00b00100b00700b05b00200205b05600100105600500700700500e00b00b00e11312500211312612500112600700700700700b00b00b00b00b12500b15b13515b12515b12512512512512511315b00211312615b00112600700700700700715b00700b00b00b00b12513f,l2C 111 7 0 [w399,w397,w396,w395,w634,w392,w391] 0x700700200700b00b00100b00700b02500200202507b00100107b00500700700500e00b00b00e11412700211412812700112800700700700700b00b00b00b00b12700b15c13515c12715c12712712712712711415c00211412815c00112800700700700700715c00700b00b00b00b12713f,l2C 111 6 0 (w399::w396::w395::w393::v16) 0xe5001024031000285,l2C 111 7 0 (w399::w397::w396::w395::v17) 0x200200200400b00201501500b00b00f00200200f03100000003100a00400400a00e00b00b00e0e60300020e60000308150300e50300040e500b00b00b00b02417e0240300240300300300300300e60240020e60000240000240e50240040240040240e500b00b00b00b00b02463200b030171,l2C 111 7 0 (w399::w397::w396::w395::v51) 0x1500b00103106700003100900000000900e7ff00000e6430197fa01901503063c01500b0307f900b02403000001e00001e01502471701500100b02463000b,l2C 111 6 0 [w397,w396,w395,w393,w392,w533,w507] 0x200011e02302d0000f2,l2C 111 7 0 (w399::w397::w396::w395::v37) 0x700101c01c00100100100400700702d00000002d0110010010110050070070050100040040100000230000230ab0230010ab0070070070070070237fd00711e02300302300402311e0351350350230350230230230230230000358180350ab0350010ab00700700700711e03500411e02313f,l2C 69 3 1 [w139,w138,w661,w137] 0x0,l2C 111 7 0 (w399::w397::w396::w395::w393::v29) 0x1c00700202d06700002d00c00000000c00575b00000500001900001901c0236c501c00702375900700203502381a01e6c701e01c03575d01c0070356c6007,l2C 109 5 0 [w450,w542,w644,w446,w645] 0x10010220220000000010000000010010000740010740740010010000017cb000000000000001001001000,l2C 109 5 1 [w450,w542,w644,w446,w645] 0x81c,l2C 109 5 1 [w450,w504,w447,w543,w645] 0x7d0,l2C 111 7 0 (w399::w397::w396::w395::v56) 0x81e81d00006700006700c76a00972c00001900001901c8060158010020b40ae00001e00001e01c75f01571b001,l2C 111 8 0 (w399::w397::v60) 0x1c01581f01c00701500101501c6d300774181b7d481901c01c00b00201c0157bf00b7ba81768681601500781400b8130047ad64600701c00c06781281176b01c00c01500906780f80e72e01500900700506780b80a6cc00700500b00e06780980863b00b00e01c01c01901901980701c01c0150150190190198020150150070070190190197fe00700700b00b01972a0190190197fb01900b00b01901e01901901e01901e01901901901901901901901c01c01e01e01e76001c01c01501501e01e01e71c01501500700701e6f401e01e01e6c801e00700700b00b01e01e01e63300b00b019019019,l2C 107 6 0 (w435::w662::v19) 0x1dd0020021dd13d00400413d1dd00213d0020020020041dd1dd0220221dd02202202202213d02202213d02201f0221dd01f01f1dd01f01f01f01f13d01f01f01f01f00401f13d,l2C 107 6 1 (w435::w662::v19) 0x821,l2C 47 5 0 (w47::w593::v35) 0x1dd1dd000000000000002000000002002002002002002002002000002,l2C 47 5 1 (w47::w593::v35) 0x823,l2C 79 5 0 (w149::w663::v11) 0x18e18e000000000001001001001001001001001000001000001000000,l2C 79 5 1 (w149::w663::v11) 0x825,l2C 111 7 0 (w399::w664::w395::v56) 0x10609d09d09d09d10609d09d10600100113f00113f09d09d09d00182600217100217109d0021061061060028240020020010020ae0190ae01909d0ae1060ae0ae0ae0020ae01c0ae0b401e0b401e09d0b41060b40b40b40010b4,l2C 111 8 0 (w399::w664::v55) 0x9d10682709d13f10600110609d6ca13f6ca6ca7d46ca09d09d17100209d10682217182282268682210613f6ca1716ca0047ad64613f09d01901909d10601901910613f01901913f17101901901901982201917101901e01909d01e01e09d10601e01e10613f01e01e01e01e6ca01e13f17101e01e171,l2C 107 6 0 (w665::w434::v19) 0x18300200218318f00400418f18300218f00200200200418318302202218302202202202218f02202218f02201f02218301f01f18301f01f01f01f18f01f01f01f01f00401f18f,l2C 107 6 1 (w665::w434::v19) 0x829,l2C 47 5 0 (w666::w58::v35) 0x183183000000000000002000000002002002002002002002002000002,l2C 47 5 1 (w666::w58::v35) 0x82b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB33 : Array L2Cell := #[l2C 79 5 0 (w613::w148::v11) 0x1dc1dc000000000001001001001001001001001000001000001000000,l2C 79 5 1 (w613::w148::v11) 0x82d,l2C 111 7 0 (w667::w397::w395::v56) 0xc60bd0bd0bd0bd0c60bd0bd0c60010011350011350bd0bd0bd00182e00217e00217e0bd0020c60c60c600282c0020020010020ae0190ae0190bd0ae0c60ae0ae0ae0020ae0b401c0b401e0b401e0bd0b40c60b40b40b40010b4,l2C 111 8 0 (w667::v59) 0xbd0c682f0bd1350c60010c60bd6ad1356ad6ad7d46ad0bd0bd17e0020bd0c682a17e82a82a68682a0c61356ad17e6ad0047ad6461350bd0190190bd0c60190190c613501901913517e01901901901982a01917e01901e0190bd01e01e0bd0c601e01e0c613501e01e01e01e6ad01e13517e01e01e17e,l2C 103 5 1 (w380::w510::w410::v27) 0x664,l2C 111 7 0 (w399::w397::w398::v50) 0x400400000403800000003802000000002004f00400404f02200002200002200403717209e83101f09e01f00b00b00b09e09e03700003700003703700403702230d022037037037,l2C 103 5 0 [w380,w510,w377,w668,w465] 0x4004000000000000000000,l2C 103 6 0 (w380::w510::v27) 0x1a01a01a000001000001000664001000664001000004012000004004000004004000004004001004664664664001000000000000000833000000670000001000664001004000000004,l2C 103 6 1 (w380::w510::v27) 0x834,l2C 103 5 0 [w380,w379,w377,w575,w376,w538] 0x44000000000000,l2C 103 5 0 [w380,w377,w669,w575,w376] 0x4412a001000004001074000000000001000,l2C 103 5 0 [w380,w379,w575,w376,w464] 0x44044004004000000074074001001000001000000001000000000000001001,l2C 39 3 1 [w673,w672,w671,w670] 0x0,l2C 103 6 0 [w380,w379,w377,w575,w376] 0x83900104400100183804400100400100107400100166407400183700104407407400104407400000083600000000000000004400100100164e044074001001001001074,l2C 103 6 1 [w380,w379,w377,w575,w376] 0x83a,l2C 110 4 1 [w430,w406,w405,w488,w404] 0x0,l2C 46 4 0 [w675,w486,w674,w485] 0x2002000002,l2C 46 4 1 [w675,w486,w674,w485] 0x83d,l2C 111 6 0 [w399,w397,w398,w393,w424,w391,w506] 0x38000000022000000,l2C 105 4 0 [w602,w676,w514,w512] 0x4004000000000000,l2C 105 4 1 [w602,w676,w514,w512] 0x840,l2C 111 7 0 [w399,w397,w398,w393,w392,w424,w391] 0x3800000003804f00100084100104f00104f02083f02202002000100100171f00183902200002202002002002002202202002004402200104403066400003083e03002007507503003000003700003702000000100100100002283c000022,l2C 103 5 0 (w380::w379::w677::v32) 0x44000004000,l2C 103 6 0 [w380,w379,w677,w377,w376] 0x1044001044004004004004001001004001124001001664124044001124001001044001012044001001124000000843000044001001044004004004004124001001001001124,l2C 103 6 1 [w380,w379,w677,w377,w376] 0x844,l2C 111 7 0 [w399,w397,w398,w393,w392,w391,w678] 0x2203800002000002003800000404f00404f0380380380040380380380220380380220000220040211370210380381c21c2137137000037000037038000004004004000022000,l2C 103 5 1 [w380,w379,w575,w376,w464] 0x838,l2C 111 7 0 (w399::w397::w398::v56) 0x2003803803803802003803802000100104f00104f03803803800171f00002200002203800002002002083f8470010010ae0190ae0190380380380ae6640200ae0700c80ae0ae0000376bf03703876202072000100100165a,l2C 111 8 0 (w399::w397::w398::v13) 0x3802084803804f02000102003869c04f69c69c7d469c03803802284603802002284584283b02004f02269c0047ad04f03801901901983503802001901902004f01901904f00e00e00e01901901901901901903803776303802003772102004f69c03769c69c69c65b04f022037832037,l2C 111 7 0 (w399::w395::w398::v50) 0x200200200403800200203802000000002004f00400404f05c02200205c00002200002203f02200403f03717e00b00200b00b00b00b00000b63809e00b03700203700003703700403702217102203702203703703700b00b,l2C 47 5 1 [w47,w45,w44,w43,w41,w679] 0x21,l2C 103 5 1 [w380,w378,w510,w575,w376,w464] 0x0]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB34 : Array L2Cell := #[l2C 111 7 0 [w399,w395,w398,w393,w392,w424,w391] 0x3800000003804f00400072d00404f00404f02084c02202002000400400484b00402200002002002002202002002200407584b001075001020075075075030075030000037000037020662004004004000022000,l2C 107 6 0 [w680,w435,w434,w432,w431] 0x2102102102102102102102100427f00427f15a00227f00200200200427f01201201201202102102102100215a00215a012012012012012012002012021021012012012012012,l2C 107 6 1 [w680,w435,w434,w432,w431] 0x84e,l2C 107 6 0 [w435,w434,w433,w432,w681] 0x210120210210210210210120120120120210210210210042980042980120120120121bb0022980020020020042980210210210210021bb0021bb012012012012012012002012,l2C 107 6 1 [w435,w434,w433,w432,w681] 0x850,l2C 111 8 0 (w399::w395::w398::v13) 0x3802042303804f0206a002003885104f84f6a04236a003803802242303802002284d02004f02200404f03800e00e00e42303802000e00e00e00e02004f00e00e00e00e04f00e01900e03803700203802003764b02004f6a00376a00036a065d04f02282203784a63a03700e00e00e00e,l2C 47 5 1 [w47,w45,w44,w43,w41,w548] 0x21,l2C 111 7 0 (w399::w395::w398::w393::v15) 0x3800100003804f00100172d00104f00104f02000001902002000100100185300102200000902000e02000902000900902200902002200107500000107500100e02007500e020020020075020075075001075019170001037000037020662001001001661022000075000,l2C 107 5 0 [w435,w434,w432,w480,w569] 0x1201200000000007f02102107f00007f07f00207f0000020020d20d2,l2C 107 6 0 [w435,w434,w433,w432,w431,w480] 0x2202100003166b03102100000401200401202102102100485502102102102202102102200002200402202200202279900201f00201f021002002002004002,l2C 107 6 1 [w435,w434,w433,w432,w431,w480] 0x856647,l2C 111 6 0 (w399::w397::w398::v54) 0x1db01107f0000001db,l2C 111 6 0 (w399::w397::w398::w393::v39) 0x38000022020030000000,l2C 111 7 0 (w399::w397::w398::v51) 0x3800000003804f00100104f02085900e02002000100100185800100f02200000f00902017001902002002000902000900902002202202000902000a02200100a03085703103083e01902003001902003002002002003000100e1290300307f903000003700003702064b00100100165d022024000024,l2C 103 5 1 [w380,w379,w377,w575,w376,w682] 0x1,l2C 111 7 0 [w399,w397,w398,w393,w392,w391,w636] 0xe03802102000002003800002102104f04f02100404f03803803800400c03801903800c03800c00c02200c03802285b0220040211370211370190190380381370190380380380381a11370001a129c13700429c00e0c837d137002137002137137021037002037038002002002004002022002,l2C 107 5 1 [w435,w433,w432,w455,w431,w480] 0x0,l2C 111 6 0 [w399,w397,w395,w392,w424,w391,w533] 0x2d0000001db0000ac,l2C 103 5 1 [w380,w379,w378,w575,w376,w464] 0x838,l2C 111 7 0 [w399,w397,w395,w393,w392,w424,w391] 0xc00000000c00500100072d00100500100502085f02202002000100100185e00183907585b07500117002002002002002007502004407500107500107507503085d0311290200300200200300010750750300300200200750300307fa03000001e00001e02066200100100166807583c000075,l2C 107 5 1 [w435,w434,w433,w432,w480,w471] 0x0,l2C 111 7 0 (w399::w397::w395::w398::v56) 0x81e00002200002200c00000985f00000e00000e0380000208590010000190000190388610200000700ae002,l2C 111 8 0 (w399::w397::w395::w398::v13) 0x3802086203804f02000102003800404f0040047d400403803800c02202202285703800c02000902202202286002000904f00502202202200404f00503803800e00e00e85c03803802002000e7bf00e00e00e85a00e02002004f04f00e69c00e00e00e00400e04f04f00e01900e03803801901901985703803802002001901901985402002004f04f01901901900404f04f00e00e00e00e00e00e00e00e00e01901900e00e00e01903701982a0190190197fb01901901903803700203802003764b02004f00403700400400465d04f02202203701e02263b03701e00e00e00e03700e63400e00e,l2C 79 5 0 [w149,w684,w147,w683,w217,w145] 0x13c000001000000031,l2C 79 5 0 [w149,w684,w147,w188,w145] 0x100100000100100013c13c,l2C 79 5 0 [w149,w684,w147,w217,w145,w216] 0x13c000000031000,l2C 79 5 0 (w149::w685::v36) 0x1001000001001001001000000001000000000000001001001000001000000001001,l2C 79 5 0 [w149,w147,w200,w217,w145] 0x4404400004400004403100004403100113c044044044000000000,l2C 79 5 0 [w149,w684,w147,w185,w145] 0x13c13c00113c031001001001000001000000,l2C 79 5 0 [w149,w684,w147,w217,w145,w215] 0x13c000031000000000,l2C 79 5 0 (w149::w684::v11) 0x13c13c000000000001001001001001001000001001001000001000000,l2C 79 6 0 (w149::w684::v36) 0x100113c00100186b00113c00003186a03113c00100100100100186913c00100100100113c00100100113c00100186800100100100100100186700100100000086600013c00100100100100186513c031000864031]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB35 : Array L2Cell := #[l2C 79 6 1 (w149::w684::v36) 0x86c,l2C 111 7 0 (w399::w686::w395::v37) 0x11a40011a40930931a40930011a40da0da0da0100100100101a40100100100100010101a40930930930930930930230230230231a40230231a409309309309302309301004f0230230230230230230030230230032820032821a42820011a4093093093093093093010010010010,l2C 111 7 0 (w399::w686::w395::w393::v29) 0x930da0011700011700da1a40010da0931a40011a40da0da0da0da0da0da0930930da0da01000e01000e0da0100100da0100100010100930930100100930100930230190230190da0230230da09302302309303802302302300202300213e00213e0da2820020da093093282002093002093,l2C 111 8 0 (w399::w686::v55) 0xda17086d0da0931700011700da85109384f86f7d486e0da0da00e00e0da17000e00e00e00e86d00e17009300e00e00e00e7ad00e0930da0190190da17001901917009301901909300e00e0190190190190190197250190190da13e0020da17013e7251700936f413e6e20036a465d09300e00e00e00e,l2C 79 5 0 [w149,w148,w660,w687,w217,w145] 0x12a000001000000031,l2C 79 5 0 [w149,w148,w660,w188,w145] 0x100100000100100012a12a,l2C 79 5 0 [w149,w148,w660,w217,w145,w216] 0x12a000000031000,l2C 79 5 0 [w149,w660,w200,w217,w145] 0x100100000100000103100000103104412a001001001000000000,l2C 79 5 0 [w149,w148,w660,w688,w145] 0x12a12a00112a031001001001000001000000,l2C 79 5 0 [w149,w148,w660,w217,w145,w689] 0x12a000031000000000,l2C 79 5 0 [w149,w148,w660,w145,w186] 0x12a12a000000000001001001001001001000001001001000001000000,l2C 79 6 0 [w149,w148,w660,w217,w145] 0x100112a00100187700112a00003187603112a00100100100100187512a00100100100112a00100100112a00100187400100100100100100180c00100100000087300012a00100100100100187212a031000871031,l2C 79 6 1 [w149,w148,w660,w217,w145] 0x878,l2C 111 7 0 (w399::w397::w690::v37) 0x11a60011a60940941a60940011a60c80c80c80100100100101a60100100100100010101a60940940940940940940230230230231a60230231a609409409409402309401001004f0230230230230230030230230032870032871a62870011a6094094094094094094010010010010,l2C 111 7 0 (w399::w397::w690::w393::v29) 0x940c80011290011290c81a60010c80941a60011a60c80c80c80c80c80c80940940c80c801000e01000e0c80100100c80100100010100940940100100940100940230190230190c80230230c809402302309401003802302300202300226f00226f0c82870020c8094094287002094002094,l2C 111 8 0 (w399::w397::w690::v13) 0xc81298790c80941290011290c885109484f87b7d487a0c80c800e00e0c812900e00e00e00e87900e12909400e00e00e00e7ad00e0940c80190190c812901901912909401901909400e00e01901901901901901972a0190190c826f0020c812926f72a1290946f426f6e20036a465d09400e00e00e00e,l2C 106 5 0 [w695,w694,w693,w692,w691] 0x2003002003002002000002000002000003000003003000000,l2C 106 5 1 [w695,w694,w693,w692,w691] 0x87d,l2C 111 6 0 [w399,w397,w395,w536,w392,w533,w507] 0x202302a0001e1000023000,l2C 107 5 0 [w435,w697,w432,w696,w569] 0x7f07f00000000000007f004012012000000000000004004,l2C 107 5 1 [w435,w697,w432,w696,w569] 0x880,l2C 111 7 0 [w399,w397,w395,w536,w392,w533] 0x11e20011e201a01a1e201a0011e20f300c02302302300c0041e10041e11e20011e10010010010041e201a1e101a01a01a1e10238810230230230231e20230230230011e20050050051e10230230230230040231e10230230230230237fd02302300025687f2561e22560011e201a25601a01a01a2561e12560041e1,l2C 111 7 0 (w399::w397::w395::w536::v29) 0x50f30010010f31e20010f301a01100101100c2c50190f300c0f300c00c0f300c0f301a01a0f302300c0f30040040f31e10040f300100100100401a01a01001001a00401002d0190230190190f30230230f302300100517302302300402302302375902381a0000f325675d0f301a01a03503501a000035,l2C 111 8 0 [w399,w397,w395,w393,w536,w392,w391] 0xf31e00010f301a01a1e000901a0011e00090050051e00050011e00f300c01a01a01a6af0f300c0f30050050050058830058820f30050190050f32200040f31e00012200010010010041e001a01a22001a00e00e01a01a0047ad22000e0050050050050050050040050f301901901987e0f31e00190190190011e00050050050050050050190050050052200190190190190040192200190190190190197fe0190190f30e47650f31e00e40011e001a01a0e401a01e01e01a01a6cc6aa0e401e0050050050050050056cb0052200e4004220,l2C 103 5 0 [w525,w378,w466,w421,w376] 0x100003f01a03f01a03f00400003e03e00103f00103f03f000000052001000004,l2C 103 5 1 [w525,w378,w466,w421,w376] 0x885,l2C 103 5 1 [w380,w378,w466,w421,w376,w465] 0x0,l2C 111 6 0 (w399::w397::w395::w420::v30) 0x100100f0000100010000ac000,l2C 102 4 1 [w416,w415,w414,w412,w698] 0x0,l2C 111 7 0 [w399,w397,w395,w393,w420,w425,w391] 0x88900100100f00166b00f00e31901907500e07500e00a00100172d00100a00100a00100188800107500000900900107500100e07507500e07507500107503088703101903001900900903000107503003007507503003063c03088600000000102400002400100100100007563c,l2C 77 3 1 [w470,w469,w468,w699] 0x1,l2C 111 7 0 [w399,w397,w395,w393,w392,w420,w391,w636] 0x2100100002100c52663d1400098897c31a788b00e85b0000190000000007c0]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB36 : Array L2Cell := #[l2C 103 6 0 [w380,w379,w378,w466,w376,w464] 0x1301302d01a00101a01a02d00102d00100000000000000100100100083800001a00101a001001000001665013013001001000001000662000767001000001001001000800,l2C 103 6 1 [w380,w379,w378,w466,w376,w464] 0x88d,l2C 107 6 0 [w435,w434,w432,w700,w431] 0x72d00072d00063d00072d72d72d00020300400000063d20372d72d72d20300020300020300020300020363d72d20372d00072d84120363d63d63d63d00072d63d00072d00000072d63d00072d000,l2C 107 6 1 [w435,w434,w432,w700,w431] 0x88f,l2C 98 3 1 [w474,w701,w473] 0x0,l2C 103 6 0 [w380,w379,w378,w377,w376,w702] 0x100100000100001200001200000000100100166b00000189100100100000100001800001800057f0010000010010010006a6,l2C 103 6 1 [w380,w379,w378,w377,w376,w702] 0x89262c,l2C 111 8 0 (w399::w397::w395::w393::v15) 0x1a900c0010010018931a900c1a70050010010018900010011a70050010051a900900900988e1a90090190090090090090090010091a90011a70010017d40011a91a907588c1a900100107500100e00e00100186083b07500e00900900900900900988a0091a70010750010010017ab1a71a90190190196671a90090090090090090090190090090091a70190190190011a70750190190190198540190750190190190190198020197860191a91157691a900100111501e00172e11501e00900900900964e0091a700111500100100166c1a707511563e075,l2C 103 5 1 [w380,w510,w377,w376,w465,w603] 0x664,l2C 111 6 0 [w399,w397,w395,w392,w481,w605,w533] 0x31e0bd01c00001c00031d,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w481,w605] 0xbd1a58966b91c20bd01c89501c0fa10701c,l2C 111 7 0 [w399,w397,w395,w393,w392,w703,w391] 0x9d00c09d00c09d0000fa1e40002c309d09d09d0000fa17300028409d0020020c800230c00200200000200200200000209d09d09d00c31600c09d09d09d25200025200025225200225225209d10725280409d09d0fa01c107107000107,l2C 111 6 0 [w399,w393,w392,w425,w424,w391,w481] 0xf000031000022000,l2C 103 5 0 [w380,w379,w421,w465,w464] 0x13074013074013000000000074001074000001001001000001000000000000000001001001000000,l2C 103 5 1 [w380,w379,w421,w465,w464] 0x89a,l2C 111 7 0 [w399,w397,w393,w392,w425,w391,w481] 0x3000f00003100003100f00000100114200914200900f00f00f14289b1c209700100a00100a00f00f00f00173600f00f00f03000f00f0300308990306641421420300010300308050306a600002400002400f57f14273400100100166e,l2C 71 4 1 [w363,w388,w362,w360,w704] 0x1,l2C 103 5 0 [w380,w379,w378,w421,w465,w464] 0x13000000000001000000,l2C 103 6 0 [w380,w379,w378,w377,w465,w464] 0x1301a01301a01300000100001300101300000000000000100100189e89a00001a00101a00000100100100100166500100100000166400057f00089d0010000010010010006a6,l2C 103 6 1 [w380,w379,w378,w377,w465,w464] 0x89f,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w481,w705] 0x1e43850fa1420001c37361e40006a6,l2C 109 5 1 [w450,w504,w648,w447,w543] 0x7d1,l2C 111 7 0 [w399,w397,w395,w393,w706,w392,w391] 0x1fe00c1fe00c1fe1fe0fa1a91fe1fe1fe0018a20fa1730012841fe0001421421427530fa0c800030c00100100100014224400c2c300c1fe2440012442440002442442440002446a61fe0000fa0bd000316001001001000,l2C 111 8 0 [w399,w397,w395,w393,w392,w391,w481] 0xc01900c0fa8a31420098a189314200900c00c00c00c8a000c1c31420011420fa6af1c30056af6af1c300500c00c00c00c00c00c6af7d400c0fa8571c200e8578571c200e00c00c00c00c79100c1427bf1c27ba85789c8571421c36af1c26af0047ad7ab1c300c00c00c00c00c00c01900c00c00c1420190190196671421c301901901987e1c31c20190190190198570198351c20190190190190198070197980190fa89810701e89776b10701e00c00c00c00c67000c1421077371421c36f41076e26af6af6731c31c21070021c2,l2C 111 7 0 [w399,w397,w395,w708,w392,w707,w391] 0x4300000004302900001202901202902902901200002902901309901302909900a00a00a0040e70040e7029004012004099099004004003004003108003108029003012003,l2C 111 8 0 [w399,w397,w395,w708,w392,w391] 0x4302942f0430120298a502904301284f42f42f04304300e00e04302900e00e00e00e0290050050050430e77ab0430290e77ab0290120e70040e700e00e00e00e00e00e1086460e76466466467ab0e704310800204302910864602901264610800364610800e00e00e00e,l2C 102 4 0 [w416,w413,w412,w511] 0x3003000000000000000000000000,l2C 102 4 1 [w416,w413,w412,w511] 0x8a7,l2C 103 6 0 [w380,w379,w378,w377,w376,w682] 0x1201200001300001300000002d01202d0120120120120120000128a800401a00401a00400401201201200469e003018003018003003012003004004004003,l2C 103 6 1 [w380,w379,w378,w377,w376,w682] 0x8a962c,l2C 79 5 0 [w149,w148,w654,w185,w145] 0x13013001001001031001001000001000000,l2C 79 6 0 [w149,w148,w217,w185,w145] 0x130130130130130130138ab0130010010010010010010010010010010130130130130010010010010017f4001001000000000000000000000000013013013013013013]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB37 : Array L2Cell := #[l2C 79 6 1 [w149,w148,w217,w185,w145] 0x8ac,l2C 111 8 0 [w399,w397,w393,w708,w392,w391] 0x430298ad0430126b50298ad8ad0290050290050290430128aa04304300500500500504300500e0050430e77ad0430290e70010290127ad0e70047ad0e70050050050051087ad0e77ad7ad73a7ad0e704310873a04302910873a029012108003108005005005005005005,l2C 111 6 0 (w399::w397::w708::v54) 0x4301102900001200f012,l2C 111 6 0 (w399::w397::w393::w708::v39) 0x4302900001200a000,l2C 46 4 0 [w487,w710,w709,w485] 0x2002000002000000000000,l2C 46 4 1 [w487,w710,w709,w485] 0x8b1,l2C 111 7 0 (w399::w397::w393::w708::v18) 0x4300000004300507b02900902902902902900900900500a0318b202900500a0298b000e02901202901200902902900900a02902902902900f01200000f00a00a8af00a00e0560010e70010e702900101203000103000a00100100100300100310800310802900301202400302400a00a00a003,l2C 77 4 0 [w470,w712,w711,w468] 0x1001000001000000000000,l2C 77 4 1 [w470,w712,w711,w468] 0x8b4,l2C 111 6 0 (w399::w397::w395::w708::v31) 0x29012043010000000,l2C 111 7 0 (w399::w397::w395::w708::v29) 0x50430000290000290438b601201100001100c04305b00e04304304300c04300c00c04301201204300c04302d0108b500e04301000e0430100430430430100108af0100050250040e70040e7043004012023004023010010010004002002002004002108002108043002012035002035010002,l2C 111 7 0 [w399,w397,w395,w708,w392,w540,w391] 0x4301300004302900000502901200902900901200000902900e02900902900909900001309901300e02909900e02902902909902900507b0130e70010e7029001012001099099099001001001003001013108003108029003012003099003,l2C 111 7 0 [w399,w397,w395,w393,w392,w707,w391] 0xc00000000c02900001202900a02902902900a00a00000a03105600009900009901307b02902902902902900a02900a00a00a00a02902900a00101900101902900100a00109909907400109900109900100100300100301e00301e02900300a00a00a003099052003099,l2C 111 7 0 (w399::w397::w395::w393::w708::v25) 0x900002900000001200001200c0000000050000050438b600000e00000e0430000298b006b070001002,l2C 111 8 0 [w399,w397,w395,w393,w708,w392,w391] 0x430298ba0430120120290090128b90290090050050290290058b802902904300c0120120128aa04300c0430430058510050050058b700504304300500e00504304300e00e00e8aa04304302902900e6b700e00e00e8b300e02902900500500500500500500500500500e00e0050050050430e70040430290e70010290120120e70190120040e70190050050050e700500400500500e00e00e00e0e77ad00e00e00400e00e1080040e70040040030040e704310800204302910800302901201210801e01200310801e00500500500510864600500500300500500e00e00e10800e00300e00e,l2C 79 5 0 [w149,w148,w654,w188,w145] 0x1001001001000001001000013013,l2C 79 5 1 [w149,w148,w654,w188,w145] 0x8bc,l2C 103 5 1 [w380,w379,w524,w421,w376] 0x6be,l2C 111 6 0 [w399,w397,w392,w713,w391,w533] 0xa37c021000136000136136021136000010136021001001001074136002002002001002002052021136002,l2C 111 6 0 [w399,w397,w393,w713,w391,w506] 0x5605600e00e031021056029098098098098021098000074074021001001001002002002001002002021002098098098002,l2C 111 7 0 [w399,w397,w393,w392,w713,w391] 0x2103100002105605605600a0290560560560560568c005605600e05605605605605600a05600a00a00a00a00a8bf00a00a02107400102100100107400100107405605607405605605600a00a00a00a0520010740010017e90010740210520020210310520000520560560560568be05600a00a00a00a00a00a8bd00a,l2C 47 5 0 [w47,w58,w714,w43,w41] 0x21021002000002002000002002002,l2C 47 5 1 [w47,w58,w714,w43,w41] 0x8c2,l2C 107 5 1 [w435,w434,w432,w480,w569] 0x855,l2C 111 6 0 (w399::w397::w633::v31) 0x513605b05b02d13609b09b05b09b13613613609b00000100113600109b09b09b001002002002001254254002002136002,l2C 111 7 0 (w399::w397::w633::v29) 0x5b00505b02d13600013605b05b05b05b8c505b05b05b05b01001005b05b05b05b05b01005b1360100100100108bf01013602d28600028605b05b05b05b8c405b1362860011360100100100100100108c30102540022860020020027af28602d00225400200225405b05b25405b05b05b136254002136010010010010,l2C 111 7 0 (w399::w397::w633::v56) 0x5605b05b05b05b05605b05b05606b06b00506b00505b05b05b06b8c507000e07000e05b0700560560560708c004307000112500112505b00105600107007007000100200200200100215b00215b05b00205600206b06b06b002,l2C 111 8 0 (w399::w397::w633::v13) 0x5b0568c705b00505600505605b0050050050058c600505b05b00e00e05b05600e00e00e00e8c100e05600500500e05b1256af05b05612500105600500500500500e00e00e00e00e00e69c00e15b6ad1256ca8137ea7b012505b15b00205b05615b6c105600500500500500500565d00500e00e00e00e,l2C 79 5 0 [w149,w148,w147,w715,w145] 0x1001001001000001001000013013000000,l2C 79 5 1 [w149,w148,w147,w715,w145] 0x8c9,l2C 111 6 0 [w399,w397,w392,w425,w391,w716] 0xa11611600001300011611611601300001037e116001001001074013002002002001002002052116013002,l2C 111 6 0 (w399::w397::w634::v39) 0x7b11600e11603111607b09809809811611611609800023e23e116001001001002002002001002002116002098098098002]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB38 : Array L2Cell := #[l2C 111 7 0 (w399::w397::w634::v18) 0x11603100011607b07b07b00a00a07b11607b07b07b8cc11607b00e07b07b07b07b07b00a07b11600a00a00a00a8cb00a11611623e00111600100123e00100123e07b07b23e07b07b07b00a00a00a00a29d00123e00100153900123e11629d00211603129d00029d07b07b07b07b8be07b00a00a00a00a00a00a8ca00a,l2C 47 5 0 [w47,w58,w44,w59,w41] 0x21021002000002002000002002002,l2C 47 5 1 [w47,w58,w44,w59,w41] 0x8ce,l2C 111 6 0 [w399,w397,w395,w392,w716,w506] 0x500502502502d01309b09b02504309b09b01309b00000100101300109b09b09b001002002002001018018002002013002,l2C 111 7 0 [w399,w397,w395,w392,w391,w716] 0x2500502502d0130000130250250250258d00250250250250100430250250250250250100250100100100100108cb01001002d01a00001a0250250250258c402501301a0010130100100100100100108cf01001800201a0020020027b201a02d002018002002018025025018025025025013018002013010010010010,l2C 111 7 0 (w399::w397::w395::w634::v25) 0x7b02502502502507b02502507b06b06b00506b00502502502506b8d007000e07000e02507007b07b07b0708cc06b04300112700112702500107b00107007007000100200200200100215c00215c02500207b00206b06b06b002,l2C 111 8 0 [w399,w397,w395,w634,w392,w391] 0x2507b8d202500507b00507b0250050050050058d100502502500e00e02507b00e00e00e00e8cd00e07b00500500e0251276af02507b12700107b00500500500500e00e00e00e00e00e69c00e15c6ad1276ca8147eb7b312702515c00202507b15c6c107b00500500500500500565d00500e00e00e00e,l2C 111 7 0 [w399,w397,w395,w393,w717,w425,w391] 0x200203100300f00200200f38c02400a03100300a00200200200314100215915915900900900e00914100e00e14114103100003131900038d1411410240240240003243240240240310240311e3024024003024141141141024640,l2C 103 5 1 [w380,w378,w421,w575,w376,w465] 0x0,l2C 111 6 0 [w399,w397,w393,w425,w424,w391,w636] 0x100f00000f0001c0020000,l2C 111 7 0 (w399::w397::w395::w393::v16) 0xf00000000f00a00400072d00400a00400a0000000303190040040040040000040758d60010750010200200200750750308d50312ce031030030030030004075075030030815030000024000024000000004004004000075641,l2C 107 6 0 [w435,w434,w433,w444,w432,w431] 0x3100003100402103100002102202201203100401200400400000402202203102203102202202200002203100003101f00001f004004004000,l2C 107 6 1 [w435,w434,w433,w444,w432,w431] 0x8d8647,l2C 110 5 1 [w430,w406,w482,w490,w718] 0x791,l2C 102 4 0 [w719,w416,w413,w511] 0x3003000000,l2C 102 4 1 [w719,w416,w413,w511] 0x8db,l2C 111 7 0 [w399,w397,w393,w425,w391,w636] 0xf00e00f00f07c00900f00f00f00f00f8dc00f00f00f1c00000001c00211c00210210211c000f00f00f00f00f00f8a800f02122302122300f00f00f00f8da00f0002238d62231c02230041c02590022230020020027b522302102125902100225900f00f00f00f00200f0022590022591c00022590020028a80021c0,l2C 111 7 0 [w399,w397,w395,w393,w425,w533] 0xa00a00a00a00f00f00f01001001001001101101100a00a00a00a0040ac0040ac0040ac0040ac00a00a00a00a00400a0100100100100100100ca0040ac0040040030040ac0030ca0030ca0030ca0030ca00a00a00a00a00a00a010010010010003010,l2C 109 5 1 (w450::w504::v38) 0x7ca,l2C 107 5 1 [w435,w434,w432,w431,w569,w720] 0x21,l2C 111 7 0 (w399::w397::w395::v30) 0xf00a00f00000000000000f00f00f00f01001001001001001000f00f00f00f00f00f0110110760000ac8e00ac00f00f00f00f8df00f0000ac0000ac0100100100100100100ca0020ac0020020027b50ac0020020ca0020020ca00f00f00f00f0020ca0020ca010010010010002010,l2C 111 7 0 (w399::w397::w395::w393::v30) 0xa00f00003100003100f00000000f00a00000000a00f00f00f00f00f00f00a00a00f00f01000e01000e00f00f01001000f0108a800f01107600a01001000a00403000403000f0ac00400f00a0ac00400a01001000200200200400202400202400f0ca00200f00a00a0ca00200a00200a010002,l2C 111 7 0 (w399::w397::w395::w393::v40) 0xf00000000f00000000a00a00a03100a00a00a00a00000a03100a09900001309901302902902900a09900403000403000400400a00409909900400400300400302400302400300300a00a00a003099003,l2C 107 6 0 [w435,w434,w433,w721,w432,w431] 0x3100001201203101202103100002101201201203101201200001203100403102200402220301200400400300403100303101f00301f012012012003,l2C 107 6 1 [w435,w434,w433,w721,w432,w431] 0x8e4647,l2C 110 5 0 [w430,w406,w482,w722,w404] 0x200200200000200200205200201f000000002002002000002000000000,l2C 110 5 1 [w430,w406,w482,w722,w404] 0x8e6,l2C 111 7 0 [w399,w397,w395,w393,w425,w391,w723] 0x3100f00f00f00f03100f00f00000000000a00000a00f00f00f0000000708e700f00f07c07c07007000003000003000f00000000007007000200200200000000274602400200202402400f002002002002002000002070002,l2C 111 7 0 (w724::w399::w397::w395::v17) 0xf00f03100f03100000f00f00f00000f00f00f1748dc1b71b71741741b700900900f00f00f00f00f03100017417400200200200003131900038d00200200200200000217400200238e00238c00f03100f00f00a03100000a,l2C 111 8 0 (w399::w397::w395::v17) 0xf8e98e800f00a8e58e300a00f85100a84f8e28e18de00f00f00e00e00e8dd00f00900900900a00e00e00e00e00a00f03085700f8d90308d703000a03000400a00e00e00e00e00e00e02482a0308228167ec7b603000f02400200f8d402464b02400a6f50246e30036a465d00a00e00e00e00e64200e,l2C 111 6 0 (w399::w397::w393::w574::v16) 0x318022024075000000000024000000,l2C 111 6 0 [w399,w397,w393,w392,w425,w652,w391] 0xf00000a000000000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB39 : Array L2Cell := #[l2C 69 3 1 [w139,w725,w138,w137] 0x0,l2C 111 6 0 (w399::w396::w393::w392::v16) 0xe5022024000000000,l2C 46 4 0 [w486,w674,w485,w484] 0x2000000000000000,l2C 46 4 1 [w486,w674,w485,w484] 0x8ef,l2C 109 5 1 (w450::w447::v38) 0x7cc,l2C 111 6 0 [w399,w397,w393,w392,w424,w391,w723] 0xf00f000000000000,l2C 111 7 0 (w399::w397::w393::w392::v16) 0xf00000000f00a00100089000100a00100a8390008f283903017004400100104402081d0220200220750200010018f10010308990311290310308f00300300300200200300010300308ee0308ed0248ec02400083c00083c0208eb001001001000,l2C 111 6 0 [w399,w397,w393,w574,w726,w425,w391] 0x2ce31700000003103129f000,l2C 111 7 0 [w399,w397,w393,w392,w726,w425,w391] 0x3100003112a00100112a00f03100000f31a03007b00100131b12981d2ce1291290091290090010010000010300300300310308f003003102012912903003000003003100000003103129400029f1298f4001001001000,l2C 110 5 1 [w430,w406,w405,w482,w491] 0x679,l2C 103 5 1 [w380,w379,w377,w421,w727,w376] 0x13,l2C 111 7 0 [w399,w397,w393,w392,w425,w533] 0xa00a00a00a00a00a01101101101101101001101101101101101101100f00f00f0010ac0010ac0010010ac0010010ac01101101101100a00a00a00a00100a0ca0010ac0010017f20010ac0000ca0000ca0000ca8f70ca0110110110118f601100a00a00a00a00a00a,l2C 110 5 1 [w430,w405,w482,w404,w491] 0x67b,l2C 47 5 1 [w47,w58,w554,w41,w389] 0x6fc,l2C 47 5 0 (w58::w57::v35) 0x5c05c000000000000000000000000000000000000000002002,l2C 47 5 1 (w58::w57::v35) 0x8fb,l2C 47 5 1 (w47::w57::v35) 0x754,l2C 79 5 1 [w149,w148,w660,w145,w186] 0x877,l2C 109 4 0 [w450,w644,w643,w645] 0x0,l2C 109 4 1 [w450,w644,w643,w645] 0x8ff,l2C 110 4 0 [w430,w489,w491,w492] 0x0,l2C 110 4 1 [w430,w489,w491,w492] 0x901,l2C 111 6 0 [w399,w397,w425,w533,w506] 0x1109801101100f09b00f00f000000000000000204000204000204000204000902204000000204222000204000000000000204000222000222000900222000000222000222000222,l2C 111 6 0 [w399,w397,w392,w425,w391,w533,w728] 0xac0000ca,l2C 111 7 0 (w399::w397::v54) 0xf00a00f00000090400000f00f00f00f01101101101100f00f00f00f00f00f01190300f0110100970000ac8f10ac00f00f00f00f73600f0008fe0ac8f171f0ac0110110110110ca82c0ac8248f18fd8fc0ac0008fa0ca8f966e0ca00f00f00f00f0000ca8f90ca011011011011734011,l2C 47 5 1 (w546::w58::v35) 0x6ea,l2C 110 4 1 [w430,w482,w491,w492] 0x67a,l2C 111 6 0 [w399,w397,w393,w425,w533,w506] 0x900901000f03103109800000009800009801109800f00f001001001001098204001098001001000001000000000000098098222907098000098,l2C 111 6 0 [w399,w397,w392,w425,w707,w391,w533] 0xf000000000012,l2C 47 5 0 [w47,w58,w729,w43,w41] 0x21021000000000000000000000000000000000000000000000000000000000002000002002,l2C 47 5 1 [w47,w58,w729,w43,w41] 0x90a,l2C 111 7 0 (w399::w397::w393::v54) 0xa00f00003100003100f00000000f00a00a00090b00a90900a01100901100900f00f01101100f01190800f01009701101101101100f00f00f00f00f00f00a00a00f00f00103000103000f0ac00100f00100100a0ac00100a0010018fd00181a0246d602400f0ca77000f01173400a00a0ca90600a6cd00a]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB40 : Array L2Cell := #[l2C 110 5 1 (w451::w430::v24) 0x67d,l2C 111 7 0 (w650::w399::w397::v18) 0xf00f00f00f00f00f00f00f00f00f0d926e09700f00f00f00f0010012970010012970d90d90d90d92c200129700100190d00129700a00a00a00a00f00f00f00f0002c20002c20d90d90d90d990d0d900a00a00a00a00a00a90d00a00f00f00a00a00a00a00a00a00a0d90d90d90d9,l2C 110 5 1 [w430,w406,w405,w482,w493] 0x67e,l2C 111 7 0 [w399,w397,w393,w392,w425,w651] 0xf01100f00f00f00f00f00a00a00a00a00a00a00f00f00f00f00f00f0cb2730970cb0cb0cb0cb00f00f00f00f0010012a10010012a10cb0cb0cb0cb00a00a00a00a2cd0012a100100190f0012a100f00f00f00f0002cd0002cd0cb0cb0cb0cb90f0cb00a00a00a00a00a00a90f00a,l2C 47 5 0 [w58,w43,w42,w41,w389] 0x6e06e000000000000000000000000000002002000000000000,l2C 47 5 1 [w58,w43,w42,w41,w389] 0x911,l2C 47 5 0 [w47,w58,w43,w730,w389] 0x2002000000000000002002002000000002002002002000002002002000002,l2C 47 5 1 [w47,w58,w43,w730,w389] 0x913,l2C 47 5 0 [w47,w58,w43,w731,w41] 0x21021000000000000000000000000000000000000000000000002000002002000000000000,l2C 47 5 1 [w47,w58,w43,w731,w41] 0x915,l2C 111 6 0 [w399,w397,w393,w425,w391,w506,w732] 0xd9011000098011000221,l2C 109 5 0 [w450,w542,w733,w446,w645] 0x1001004004000000074074000001000000000000000001001,l2C 109 5 1 [w450,w542,w733,w446,w645] 0x918,l2C 111 6 0 [w399,w397,w393,w425,w707,w391,w506] 0x1200f00000f099000000000,l2C 110 5 0 [w430,w406,w497,w404,w492] 0x2002000000000000000000000000000000000000,l2C 110 5 1 [w430,w406,w497,w404,w492] 0x91b,l2C 111 6 0 (w399::w397::w393::w734::v39) 0x32203109800003100f000,l2C 110 5 0 [w498,w430,w406,w482,w492] 0x20000000000000000000000020a6002002000000,l2C 110 5 1 [w498,w430,w406,w482,w492] 0x91e,l2C 111 7 0 (w399::w397::w393::v39) 0xf00900f00f07000e00f00f00f00f00f91f00f00f00f09891d91c91a91909800009891709800f00f00f00f00f00f90890300f00022181d22100f00f00f00f89b00f81d91622181d84722109822100109825882c22182481d8fd8fc2210009142586dc73425800f00f00f00f6dc00f6dc2586dc2580988fa2589066dc91266e098,l2C 111 6 0 (w399::w397::w452::w392::v40) 0x12024000052000,l2C 111 6 0 (w399::w396::w393::w392::v40) 0x3f000024000,l2C 46 4 0 [w487,w710,w485,w608] 0x2000000000000000,l2C 46 4 1 [w487,w710,w485,w608] 0x923,l2C 111 7 0 (w399::w397::w393::w392::v40) 0xf00000000f00000000000000a07b00a00a03192400a00a02991a01202901209902902902900a00a90900a03105600103000103000107400107400a0010010019220018ed0240000240000520000520298be00a00a00a921,l2C 42 3 1 [w419,w735,w427,w417] 0x0,l2C 111 7 0 [w399,w397,w393,w392,w734,w391] 0x3100003100a02992405605605605691c05605605605605605605605605605605605605600a00a00a00a00a90b00a00a00107400107400100107400100107405605605605600a00a00100a00a00a0520010740010017e90010740000529260520310520000520560560560568be05600a00a00a00a00a00a8bd00a,l2C 111 7 0 [w399,w397,w393,w392,w734,w425,w391] 0x3100003100a00a00a00a03192400a00f03100000f31b00a02903105691d32205605600905600905605600a00a00000a00107400107400117000131a39000a00100100000103105200005203129400029f0568be00a00a00a000,l2C 69 3 1 [w138,w736,w137] 0x0,l2C 111 7 0 [w399,w397,w393,w392,w425,w391,w723] 0x3100f00f00f00f03100f00f00000002107c02100f00f07007c00000a00000a00f00f00f00000003000003000f0000008f200000000000000000092902400000002402400f00000000007c734000000000000,l2C 69 3 1 [w737,w139,w138,w137] 0x0,l2C 111 7 0 (w724::w399::w397::v51) 0xf00f03100f03100000f00f00f1b791f1741b71741b700e00f00f00f00f00f00f00f00f00003100000000000000003117092b31a0310001b700000000000000003129400029f00f03100f00f07b03100031b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB41 : Array L2Cell := #[l2C 111 8 0 (w399::w397::v51) 0xf92c92a00f00a9289279258ad00a00f00900900992000f00900e00900900900900900f91000a90e90c9058f800f00f03089c00f8f58790308f383b03000900900900900a03000100a02468603068668668678603000f02468600f68602468602400900900900968600900a6860246866866b368600a,l2C 111 7 0 [w399,w397,w395,w393,w392,w717,w391] 0xc00200200c07b03100331b15900215915930b14115900e1bf15900300200200200314100200914137715900900938215915915914114114100314103117000031a15900014114114100002402402400031c02403106f159024159159024024003024141024141141,l2C 111 7 0 (w399::w397::w395::w393::w392::v16) 0xa170319170020020075001031030020020030,l2C 111 7 0 [w399,w397,w393,w392,w425,w391,w636] 0xe00f00c00f00900f00c00f00c00c03100c00f00000002107c02107c00900900f00f07c00900f00f00f00f00e0971c007c00007c02102100a00a02100000a00f00f00f00002103000003000f00000085b07c22300007c0020020027c102102400202400f00200200207c25900207c002002000002,l2C 105 4 0 [w602,w514,w513,w601] 0x4004000000000000,l2C 105 4 1 [w602,w514,w513,w601] 0x931,l2C 111 7 0 [w399,w397,w395,w393,w392,w425,w533] 0x2d00000002d00500a00a00500001100001101001100a01100a01100a01193201100f00f00001000001001101101101101101101001001101100a00a00a00a0010230010230110ac00101100a0010100100ac0010100010100010010030010030350030350110ca00301100a00a0100ca003010,l2C 79 5 1 (w148::w181::v11) 0x784,l2C 79 5 1 (w149::w684::v11) 0x86b,l2C 111 6 0 [w399,w397,w392,w425,w391,w533,w738] 0x12011000000000,l2C 109 4 1 [w450,w644,w543,w645] 0x7cb,l2C 111 6 0 [w399,w397,w395,w425,w533,w506] 0xa01100c00c02d02d00009b00f09b00009b00009b01107600000000000009b09b20493709b00009b00200200200000200200200209b22200209b,l2C 111 7 0 (w399::w397::w395::v54) 0xa00f02d00000002d00c00f00f00c00001100001100f00f00f00f00f01193800f01009700001062701093601001000f00f00f00f01107601101101101101001001101100f73664302385e0230110ac8880110100100ac9350108580100020020029340020020020350020350110ca0020110100ca002010,l2C 69 3 1 [w139,w739,w138,w137] 0x0,l2C 111 6 0 [w399,w397,w395,w393,w425,w533,w506] 0x900c02d00000a00001009809b000098001002,l2C 111 7 0 (w399::w397::w395::w393::v54) 0x2d03100002d00c00000000c00592600000500000900000900f01193b00f00a01100001100f00a93a00e00000e00f01000000f01101000a0108af00a001002,l2C 111 7 0 [w399,w397,w395,w393,w425,w540,w391] 0xf01300000f00000000500a00e00a00500a00500503100500a00a00a00000a93200900909900001309901300e00a09900e00900900a00a00a09900a01303000103000100100a00109909909900100100100300101302400302400300300a00a00a0036a2099003,l2C 106 4 1 [w742,w695,w741,w692,w740] 0x0,l2C 111 7 0 (w399::w397::w395::w393::v39) 0x900f00c00f00e00f00c00f00c00c03100c00f00000000000a00000a00f00f00f93b9380000708e707000e00e00f00f07000e00f00f00f00f0090760980708cc0708b007009800003066b03000f86193e85f07007022181d07085907000200200278600202400202400f002002002002002000002070258002070,l2C 111 7 0 (w399::w397::w395::w393::w392::v40) 0x7b03100a38302902907b02902909900a001,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w723] 0x3100f02109700f00f07c00000000500000500f00f00f00000007600f00f07c07c00f00f07007000007000001900001900f00007c88907007007000000200200200000000292901e00200201e01e00f00207c002002002000002070002,l2C 111 7 0 [w399,w397,w395,w393,w392,w425,w391,w723] 0xc03100f38426807c070000000000024,l2C 111 7 0 (w724::w399::v59) 0xf00f1b700f1b700009700f00c00f00f00f00c00f00f00f00000f00f17400f1b71b700f00f17417400017407600f00c00f00f00f00c1b700017417417400000200200200003117000031a1b700200200200000217400200229400229f00f03107b03100031b,l2C 111 8 0 (w399::w397::w395::v51) 0xf00c03194394294100f00c00a0050318e59408b900a00500f00f00900900993f00f00f00900e00900900a00900900993d00900900f85100a84f93c93993300f00f00f00e00e00e93000f00f00900900900900900900900900900e00e00900900900a00a00e8cd00e00e00e8b300e00a00a00f03085700f0318d903001992f86003001900900900903000988a00900900a03000100a00e00e00e00e03086d00e00e85a00e00e02482a0308228177ee78603000f02400200f03192e02401e64b64b02401e00900900902400964b00900900a6f60246e40036a465d00a00e00e00e02400e64400e00e,l2C 109 5 1 (w450::w449::v33) 0x7b8,l2C 111 7 0 (w399::w397::w655::v29) 0x9723d09701101101101109709709709701109701001001001001001009709709709701100f01000029b00029b0970970970979450970110110110110100100100100100109450102ca00229b00200200294529b0020022ca0020022ca097097097097011011011011010010010010,l2C 111 8 0 (w399::w397::w655::v13) 0x970090090970090090090090976b523d6b56b59466b509709700e00e09700900900e23d00e00e00e00e6b500e23d0972717ba09700900900900923d27100123d00e00e00e00e00e00e7ba00e1ff82a2718227ba7ef7ba2710971ff00209700900900900923d6b51ff6b50036b565d23d00e00e00e00e,l2C 109 5 1 [w450,w504,w635,w446,w543] 0x7bd,l2C 111 7 0 [w399,w397,w395,w656,w391,w533] 0x7623f07601101101101107607607607601107601100f01101001001001001001007607607607600029e00029e0760760760769480760110110110110100100100100100109480102cc00229e00200200294829e0020022cc0020022cc076076076076011011011011010010010010,l2C 111 8 0 [w399,w397,w395,w393,w656,w391] 0x7600900907600900900900900900e0090766b723f6b76b79496b707607600e00e07623f00e00e00e00e6b700e23f0762727bf07600900900900923f27200123f00e00e00e00e00e00e7bf00e20182a2728227bf7f07bf27207620100207600900900900923f6b72016b70036b765d23f00e00e00e00e,l2C 101 5 0 [w745,w385,w383,w744,w743] 0x1004001004001000000000001000001001000004000004004000000000000000000000000000000,l2C 101 5 1 [w745,w385,w383,w744,w743] 0x94b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB42 : Array L2Cell := #[l2C 111 8 0 [w399,w397,w395,w393,w392,w391,w636] 0xc00e00c02102107c00902194107c00900c00c00c00c94c00c14007c8aa07c0210211400210050050210218aa42f14000500c00c00c00c00c00c8aa00c00c00c00c00c00c00c00e00c00c00c07c00e00e00e00e93000e8dd07c14000e00e00e00e8aa00e14002102113701902185713701900c00c00c00c79100c07c13788c07c14013700414000e00e00e00e00e00e85c42300e2740021370020020027c413702102127401e02100227401e00c00c00c00c00200c07c27400207c1400022740020026a400214000e00e00e00e00200e,l2C 111 6 0 [w399,w397,w395,w392,w540,w533,w507] 0x201102a000011000000205,l2C 111 7 0 [w399,w397,w395,w393,w392,w533,w507] 0x352a200001100001100000005094e00205000202a02a02a0000036b901000300301001000300300300300000305005000002300002300000005087f00300300300003503503581802d20802d0350350350356d4050050035003,l2C 103 6 0 [w380,w379,w378,w377,w668,w376] 0x1801802d00002d01300001302d00302d01200301200300300000302d00002d01a00001a00300300300001801802d01802d018018018000018,l2C 103 6 1 [w380,w379,w378,w377,w668,w376] 0x95062c,l2C 111 7 0 [w399,w397,w395,w393,w392,w746,w533] 0x38a02302d00102d01100101114300117317317300c00c00500c14300500502d00402d25c00438b00100100100414314302302302d02302d1c332332314314314302388102302300402302302300002302d00002d2a2000389143143,l2C 103 6 0 [w380,w379,w378,w377,w747,w376] 0x1201202d00002d01300001301201202d01202d01201201200001202d00402d01a00401a01201201200402d00302d018003018206012004004004003,l2C 103 6 1 [w380,w379,w378,w377,w747,w376] 0x95362c,l2C 109 5 1 [w450,w504,w642,w748,w543] 0x70f,l2C 105 4 0 [w602,w749,w513,w601] 0x4004000000000000000000000000,l2C 105 4 1 [w602,w749,w513,w601] 0x956,l2C 111 7 0 [w399,w397,w395,w392,w540,w533] 0xa300c01101101100c0119570110110110110110050110002050002050132050130130132050110110110110110119320110012430012430130132430130012430110110110110010112050012430010019320012052420012430010017f200124300024294e242013242013242011011011011955011205242003205,l2C 109 5 0 [w450,w504,w447,w750,w543] 0x1a00101a0010000010010010fa001000000001001001000000000001000,l2C 109 5 1 [w450,w504,w447,w750,w543] 0x959,l2C 111 7 0 [w399,w397,w395,w393,w392,w533,w732] 0x1101102d01102d01101101101101100006b95a0a30a300001000001000000001101101100006b06b00000189102300100102302300100101100106b00100100100000100100100000100003500003500000001100006b06b,l2C 111 7 0 [w399,w397,w395,w393,w751,w392,w533] 0x1101102d01102d01101101117501195701101111f11f11f00c00c01100c01101101102d00001101101100002d25c00038b17517502d00102d38800138a17500100100100000100100100000102d00002d2a2000389175175,l2C 111 8 0 (w399::w397::w395::v37) 0x95c01195b01100500501100595801100c00c00c9540108aa0100116b70106b59338f88de0110050050050050050059520236af02301102300101100500500500588200501087a02386e0046a069c0100356ad0236ca8197f37c502395103594f0350110356c1011005005005005005005010035003010,l2C 77 4 0 [w469,w501,w468,w467] 0x1000000000000000,l2C 77 4 1 [w469,w501,w468,w467] 0x95e,l2C 111 6 0 [w397,w396,w395,w392,w391,w533,w507] 0x1800011e023000000000,l2C 111 6 0 [w399,w397,w395,w392,w481,w533,w507] 0x1802305000031e000023000000000000,l2C 111 6 0 [w399,w397,w395,w392,w391,w533,w627] 0x11000010000000,l2C 42 3 1 [w419,w752,w427,w417] 0x0,l2C 111 6 0 [w399,w397,w395,w392,w533,w507,w506] 0x1801105000001100000000009b000000000,l2C 111 6 0 [w399,w397,w395,w392,w391,w507,w732] 0x11011000000000000,l2C 111 7 0 [w399,w397,w395,w392,w391,w533,w507] 0x3514901802a01805002a00001100001100068a96568a02a96400000276d01000200201001000206e00206e0020028f900296302396202300068f00068f02a96100200200200003503503596002d11702d03595f03503503502a02a03573b035002,l2C 111 6 0 [w399,w397,w395,w392,w753,w481,w533] 0x20802d02d28400000031d000,l2C 111 6 0 [w399,w397,w395,w392,w753,w533,w506] 0x20802d02d02d289000207000,l2C 111 7 0 [w399,w397,w395,w392,w753,w391,w533] 0x20811711700c11700c2c403502d00000002d11796802d1aa00028902d12b00212b02d05b00231f00200200000202d00000002d11796702d2c500028400200200200003503503500003503503502d03595f03511711702d02a,l2C 111 6 0 [w397,w396,w395,w392,w391,w533,w738] 0x3f000000023000,l2C 111 6 0 [w399,w397,w398,w392,w391,w533,w738] 0x1202300007f000,l2C 77 4 0 [w470,w712,w468,w699] 0x1000000000000000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB43 : Array L2Cell := #[l2C 77 4 1 [w470,w712,w468,w699] 0x96c,l2C 111 6 0 [w399,w397,w395,w392,w533,w738,w506] 0x12011140000011000000000,l2C 111 7 0 [w399,w397,w395,w392,w391,w533,w738] 0x1005b01204301214004300001100001100000000000004396e02d02502d01096d01001001004304301001093601096302300002300007f00007f0438c401001001096b00200200296a0020350020350020d20020d2010002,l2C 109 5 0 [w450,w504,w447,w647,w645] 0x1001000000000000000000000000000000000000,l2C 109 5 1 [w450,w504,w447,w647,w645] 0x970,l2C 111 7 0 [w399,w397,w395,w392,w754,w391] 0x2502502502502502502502502502597102502d00000002d02502502502502502501096d0430100100100100106270100100250250250258c402502d07f00007f00007f93a07f0100100100100100108cf0100d200207f0020020027b207f02502502502502d0020d20020020d20020d20020d2010010002010010010,l2C 111 6 0 [w399,w397,w395,w392,w754,w533,w506] 0x32102d02d28909b000000,l2C 111 7 0 [w399,w397,w395,w392,w754,w391,w533] 0x32102502500c02500c31f01002d00000002d02597302d1aa00028901001001002d01096d01002502502d04301001000001002d07f00007f0258c402d2c500028401001001000000200200200002d0d20020d202d1490022c438f010,l2C 111 6 0 [w399,w397,w395,w392,w533,w506,w590] 0x28300009b000000207,l2C 79 5 0 [w149,w148,w147,w755,w186] 0x1001000000000001001001001000001001001000001001001000001000000,l2C 79 5 1 [w149,w148,w147,w755,w186] 0x976,l2C 109 5 1 [w450,w504,w447,w631,w645] 0x94c,l2C 111 6 0 [w399,w397,w395,w392,w533,w506,w723] 0x9700f09b00000f000207,l2C 109 5 0 [w450,w504,w649,w543,w645] 0x10000010fa001001000000000000000000000000,l2C 109 5 1 [w450,w504,w649,w543,w645] 0x97a,l2C 111 7 0 (w399::w397::w395::v31) 0x1106b00501101101100c00c00c01197b01101101101100009b97909b97397109b96e97809b01101101101101101193890301100097724581e73624581e24581e24501101101101181e01109b8fe24593581e55171f09b20782e24582681e4ad93424500020797520796862420796469820701101101101173d01109b20700209b,l2C 42 3 1 [w427,w756,w417] 0x0,l2C 111 7 0 [w399,w397,w395,w392,w391,w533,w732] 0x111aa0130a301306b0a302d11f02d0110110110a301100001000001000000001101101100000000097d0230000000230230000000a3736011000000000000000000000000000000035000035000965011000,l2C 42 3 1 [w757,w419,w427,w417] 0x0,l2C 111 7 0 (w399::w397::w395::w751::v29) 0x17511f17511f00500c11f11f00c00c01101102d01111f11f11f01197b02d0a328901102d00001101101100002d05b00031f02d00011f00002d2c500028400000000000000000000000002d00002d14997f2c4,l2C 111 8 0 (w399::w397::w395::v29) 0xc00500c98001197e01100c00c00c00c97c00c97497201096f42f01000c00c00c00c0119490109469399058e10117d40237d402300c00c00c00c7d400c0110237d40110107d40237d47d44237d40100357d40237d47d47587d402396970003596668c03500c00c00c00c01103573e011010035002010,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w533,w507] 0x1492a214902a02a05000001000202d03502a02a035,l2C 111 7 0 [w399,w397,w395,w393,w392,w746,w391] 0x17317300c14317300500c17300102d1aa00128914300117317317314300c14328417300c00c17317300402d05b00431f00100100100414314314300417302317317302d0f32be02314302314314302302300402302302300002317300002d1490002c4143143143000,l2C 111 7 0 [w399,w397,w395,w392,w540,w391,w533] 0x50a300c1aa0090a300c0a300c00c0a300c0a30130130a301100c0a302d0090110090a30110110a300511f0000000a32050000a30130130100100130000100110110110000010010a32430010a30130230010230110010010010000010010017f60010006d70a32420000a3013035000035011000,l2C 109 4 0 [w516,w644,w543,w645] 0x1074001074074281004000000000000000000,l2C 109 5 0 [w516,w504,w447,w543,w645] 0x101a00101a01a000001000001001001281281000000001001001000985000000000000001000,l2C 109 5 1 [w516,w504,w447,w543,w645] 0x986,l2C 101 4 1 [w745,w385,w383,w758,w743] 0x0,l2C 111 7 0 (w399::w397::w395::w393::v31) 0x901100501100901100900c00c02d00901100901101101101100006b95a06b00500501101106b00500c00c00001000001000000001101101193b90806b06b09b8c506b8b606b00102300102300100101100106b24500106b0010010000010010017580010000356bf0359886d80116db06b06b20798706b6ce06b,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w732] 0x130a302d11f0110a30110110001aa0a30a30a301100000e00000e0a300001101101100006b06b06b00000000197d0190010010190190a300101100106b00100100100000100100100000100001e00001e0a377101100006b06b06b000,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w533,w732] 0x1aa38602d0111aa0a306b000000023000,l2C 111 7 0 [w399,w397,w395,w393,w751,w392,w391] 0x11f11f00c01111f01100c11f01111f11f02d0a301101117501111f11f11f01100c01128911f00c00c11f11f00001101101100002d05b00031f17517517500011f00102d2c500128417500100100100000100100100000111f00002d1490002c4175175175000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB44 : Array L2Cell := #[l2C 111 8 0 (w399::w397::w395::w393::v29) 0xc00500c02d98c01100998b98a01100900c00c00c01100c98900c00c00500501101100598401101100c00c00c00c00c00c00c00c00c00500500c00c00c02d95401000e8aa8aa01000e00c00c00c01000c8aa00c00c0116b70106b593c90c8e20110050050050050108c60050058b700500502d9830230196af6af02301900c00c00c02300c6af00c00c01102300101100500500502300588300500501087b02386f0046a069c0100356ad0236ca81b7587d602302d95103501e9826d903501e00c00c00c03500c77200c00c0110356c10110050050050050356ee0050056cf005005010035002010,l2C 111 8 0 [w650,w399,w397,w395,w392,w391] 0xc00c00c00c00c00c00c00c0d96b726e6b584f90e84f0d900c00c00c00c0d91ba0010d926e84f1ba84f00484f69c26e2966ad1ba6ca7417417d71ba00500500500500c00c00c00c0d92967410d926e29600226e00500500500500500574100500c00c0050d90050050d900500500500500584f005005,l2C 111 8 0 [w399,w397,w395,w393,w392,w651] 0xc00500c00c00c00c00c0050cb0050cb00c00c00c00c0cb6b72736b58519108510cb00500500500500500585100500c00c00c00c0cb1c10010cb0050050050052738511c185100485169c2732a06ad1c16ca6d36d37d81c100c00c00c00c0cb2a06d30cb0050050050050050056d30052732a0002273,l2C 106 5 0 [w742,w695,w759,w692,w740] 0x2003002003002002000002000002000003000003003000000000000000000000000000000,l2C 106 5 1 [w742,w695,w759,w692,w740] 0x990,l2C 111 8 0 [w399,w397,w395,w393,w392,w540,w391] 0xa300c01301301398a0a300c0a30090090099910a30090050090090050090090090090090a30050050050059840059580a30090090090a30998aa0a301301309901300e00e0130138b98ad09900e00900900900900900993d0090050050050050050058b80050a325a0010a301301325a01901300125a01900900900900900100900500500500500100509900125a0010016a000109914b00125a0010017f700125a0a314b7770a301301314b01e0136c114b01e00900900900970f0090050050050050050056da6b300509914b003099,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w506,w590] 0x28324e2839750000706dc0000000b4,l2C 103 5 1 [w380,w379,w378,w466,w760,w376] 0x0,l2C 111 7 0 [w399,w397,w395,w393,w392,w761,w391] 0x1bf00c1bf00c00c30b00c1bf2330001bf1bf1bf00000011f0002891bf0020020970023202332332330029140020020000021bf0000001fe0002c32339940020020020000b40b40b40001bf1bf0000dc2332330b40b40000b431c0b4,l2C 111 7 0 [w399,w397,w395,w393,w392,w761,w391,w506] 0x900c30b00c1bf0000000b4000000000,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w506,w705] 0x1fe3871fe00006b81e81d0000ae000,l2C 107 5 1 [w435,w434,w433,w432,w762,w558] 0x0,l2C 111 7 0 [w399,w397,w395,w393,w392,w763,w391] 0x1e400c1e400c00c2c300c1e425b0011e41e41e400197700111f0012891e400000009700032025b25b25b0000010010010001e41e40001a925b25b2be0ae0ae0ae0000ae0ae0ae0000ae1e499800028300030b25b000001001001000,l2C 111 7 0 [w399,w397,w395,w393,w392,w763,w391,w506] 0x900c2c300c1e40000000ae000000000,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w506,w723] 0x971b709700f97900007000f00f0000b4,l2C 111 7 0 [w399,w397,w395,w393,w392,w764,w391] 0x7600c07600c07607607600c32000c07607607626800007607607600000011f00028907607600000f0762682680708e70700700000700760000001fe0002c326800007007007000000200200200007600200228300230b268002002002000002002070,l2C 111 7 0 [w399,w397,w395,w393,w392,w764,w391,w506] 0x900c32007600c076000070000000000,l2C 111 7 0 [w399,w397,w395,w393,w392,w391,w506,w732] 0x11f0d901111f01100006b0119170000ae,l2C 111 7 0 [w399,w397,w395,w393,w392,w765,w391] 0xc1aa0cb1aa00c1aa00c0a30000cb1aa00c28900c1aa0cb0cb1aa1aa1aa06b95a1aa0000000970003200cb0cb0cb00006b06b06b0001aa0010011fe0012c30cb00100106b0010010000010010010000011aa00000028300030b0cb00006b06b06b000,l2C 111 7 0 [w399,w397,w395,w393,w392,w765,w391,w506] 0xcb28900900c00c1aa00006b000000000,l2C 111 8 0 (w399::w397::w395::v56) 0xc00900c00c00c00c00c00c00c00900c00c00c0090090090099910099a099f06b00599e98a06b00500c00c00c00c00c00c98997c00c99d99c07000e99b94107000e00c00c00c00c94c00c00900900900900900993f92000906b8d20708c78ba8ad42f06b99a9990ae0199978930ae01900c00c00c00c8a000c00900900900988e00906b0ae00106b0708790ae86d8624238480700b482f0ae82781f7587860ae9969950b401e9937480b401e00c00c00c00c77a00c00900900900974500906b7000b46ee6dd6b369906b0700b4002070,l2C 111 9 0 (w399::v59) 0xc0099a100c00500999200900c98f00598e98d98195d00c00c00e94d00c00994a00e94794492d8ea0090058d300e8c88bb8ae8a600500c0198a400c00901989400900501988400500e87c01987086385284900e01e8300198288207f87d901900c01e77b00c00901e74d00900570101e6ef6de6bc69a00500e01e64c00e,l2C 111 9 1 (w399::v59) 0x9a2,l2C 115 5 1 [w770,w769,w768,w767,w766] 0x16,l2C 87 5 0 [w184,w92,w91,w771,w90] 0x5d05d05d00023508c05d05d21e23400000005d05d,l2C 85 5 0 [w87,w84,w82,w80,w772] 0xd00d00000100000100000000800d00800d00d00d00d00000000800000800000000d00d,l2C 85 5 1 [w87,w84,w82,w80,w772] 0x9a647f,l2C 87 5 0 [w184,w254,w91,w208,w90] 0x5d2b705d00000005d05d05d0170170000002b605d,l2C 23 3 1 [w774,w773,w14,w13] 0x0,l2C 87 5 0 [w184,w254,w92,w91,w90,w261] 0x5d00000000005d000000000000017039,l2C 87 6 0 (w184::w254::v3) 0x9aa9a905d05d05d05d55f05d05d05d05d05d9a805d05d05d05d05d9a705d05d05d05d05d9a505d05d23505d00001752401700001751d01708c05d05d01705d05d05d05d08c08c08c01d01d05d05d08c01d,l2C 87 6 1 (w184::w254::v3) 0x9ab]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB45 : Array L2Cell := #[l2C 103 5 1 [w380,w525,w378,w377,w376,w603] 0x18,l2C 98 3 1 [w475,w474,w775,w473] 0x0,l2C 119 6 0 [w780,w779,w778,w777,w776] 0x3e00003e01801801801848201806308606306300303f00303f03e00303f00300303e01803f27501803f27500010100010103e10103a03e0070cc0cc0cc03f10100300300303f,l2C 117 5 0 [w786,w785,w784,w783,w782,w781] 0x231000000000000000,l2C 117 6 0 [w786,w785,w784,w787,w782,w781] 0x1a29511111111111104906c04906c0490490000490001111110000000000001111111119b000000000006c00006c00000000000049e11111101a2fe000000,l2C 117 6 1 [w786,w785,w784,w787,w782,w781] 0x9b1,l2C 119 7 0 [w780,w779,w789,w778,w788,w776] 0x630630630630180180180184b10180630630630630630630070070070079b20070630630630630630630079af0630070532e800303f00303f06306306306306306300306301803f13801803f1380070070070070030079ae06c9ad06c0630630630630070b50850b50b508500700706c0b500700703f06c00300300303f,l2C 103 5 0 (w378::w410::v32) 0xa70a700000000000000400400000003f03f003003000003000003003000003,l2C 103 5 1 (w378::w410::v32) 0x9b4,l2C 119 6 0 (w780::w779::w791::w789::v41) 0x3415f00015f1380000b006c06c06c,l2C 118 6 0 [w796,w795,w794,w793,w792] 0x60060060060030520030520060060520060030520280280280288a8028054054054052028028052000176000176006176006176052176003052028028028028028028,l2C 118 6 1 [w796,w795,w794,w793,w792] 0x9b7,l2C 103 5 0 [w525,w378,w377,w538,w682] 0x3f01803f01803f00000000000000000300003f00303f003003000003000000000003003003000000,l2C 103 5 1 [w525,w378,w377,w538,w682] 0x9b9,l2C 118 6 0 [w796,w795,w794,w797,w792] 0x5405405405401801801801805405405405405405401805402802802802805405405405405405402805401801801801806c06c06c06c05405405405401801801801802802802802802802806c028,l2C 118 6 0 [w796,w795,w794,w797,w792,w798] 0x280280060540060540060060030180030180030030060060060031ab0281ab0280280280280280060288a802800300006c00006c00000002802802800069e,l2C 118 6 1 [w796,w795,w794,w797,w792,w798] 0x9bc9bb,l2C 85 4 0 [w84,w83,w82,w799,w85] 0x800800d000,l2C 85 5 0 [w87,w84,w82,w799,w85] 0x800000000800000d00d0084430080080080170080080080000000009be,l2C 85 5 1 [w87,w84,w82,w799,w85] 0x9bf,l2C 87 5 1 [w184,w92,w91,w800,w175] 0x9c0,l2C 119 6 0 [w780,w779,w789,w777,w776,w790] 0x862bc0000000000000f20f20000f24820f20f20000f200006206227527500300300300320a0f20a80a81011010f2000003003,l2C 119 6 0 [w780,w779,w789,w788,w790,w801] 0x530f213413413413415f2f11ab0f21341341340f20000030031341341340030f200306c06c0f2000003003,l2C 119 6 0 [w780,w779,w789,w788,w776,w790,w801] 0x39b0f21ab15f0f2000,l2C 85 4 0 [w84,w802,w82,w81,w85] 0x8008001000,l2C 85 5 0 [w87,w84,w802,w82,w85] 0x10010084440000080000000080000080080009c5008017008008008000000,l2C 85 5 1 [w87,w84,w802,w82,w85] 0x9c6,l2C 87 5 1 [w184,w92,w803,w91,w175] 0x9c7,l2C 119 7 0 (w780::w779::w789::v41) 0x530532bc0620620620620620620620620620620620621ab4ef0f20004b10f215f9c80f29c49c30f20620620620620620629c20621ab0281384e602813815f9c10289bd9ba15f0620620620620620629b80620f20280030f215f0b10850b10b108515f06c06c0b115f06c0620620620620f206c4e30f202806c4df9b69b5028,l2C 39 3 1 [w673,w805,w804,w671] 0x0,l2C 119 7 0 (w806::w779::w791::v42) 0x3303303303300303f00303f0330330330330330330030330000000009ca03303303303303f00300303f02813802802869e13803303303303302803303f13802803f00313802806c2cf0890890890899b50890330330330330330330890890890890030890890342d00891380892e1089089,l2C 119 6 0 [w806,w779,w791,w789,w788,w776,w807] 0x3315f15f0003a3]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB46 : Array L2Cell := #[l2C 117 5 0 [w786,w811,w810,w809,w782,w808] 0x9f000000000,l2C 117 6 0 [w786,w811,w810,w787,w782,w808] 0x343041231231231230000000000001231231239cd04906c04906c04904900004900012312300000000006c00006c00000000000045c1231230000000342f9,l2C 117 6 1 [w786,w811,w810,w787,w782,w808] 0x9ce,l2C 119 7 0 (w806::w780::w779::w791::v42) 0xe30e30e300315f00000015f04c0e30e304c0070030030070289cf0e30e30e302802800306c30600006c9cc06c0330e30e303303f06c00303f13830713802806c06c1380280899b60e30e30890030342d02d01380890890890890b00b0,l2C 118 6 0 [w812,w795,w794,w797,w792] 0x611d00611d00315300315311d00615300600600600311d02802802802811d02802802802800602811d15302802815306c06c06c06c11d06c06c11d15306c06c15302802806c,l2C 118 6 1 [w812,w795,w794,w797,w792] 0x9d1,l2C 87 5 0 [w184,w92,w91,w176,w813,w90] 0x3e0000002950001a2017,l2C 82 3 1 [w122,w121,w814,w120] 0x0,l2C 85 4 0 [w87,w84,w81,w815,w89] 0x8008017000,l2C 85 5 0 [w87,w84,w82,w815,w89] 0x80080080080010080080080000000080000000000170170084440009d5,l2C 85 5 1 [w87,w84,w82,w815,w89] 0x9d6,l2C 87 6 0 [w94,w184,w92,w91,w813,w90] 0x1f805a05a9d705a18c0001b905a00005a16e9d407205a01705a05a05a03b0000170179d405a05a05a03b03b0179d30000171a21a2,l2C 87 6 1 [w94,w184,w92,w91,w813,w90] 0x9d801d,l2C 87 5 0 [w184,w92,w91,w176,w800,w90] 0x29500005d,l2C 84 3 1 [w212,w211,w816,w210] 0x0,l2C 87 6 0 (w94::w184::w92::v43) 0x7205a05a00005a18c9db1b905a05d05a05a05a01b05a00005a2360001f800600605a05a05a0069c005a05a23623605a0065dd1f80069da05d05d084084,l2C 87 6 1 (w94::w184::w92::v43) 0x9dc01d,l2C 118 5 0 [w796,w795,w818,w817,w792] 0x5405400300320a20a101000000101018018101101003101000,l2C 118 5 1 [w796,w795,w818,w817,w792] 0x9de,l2C 103 5 1 [w380,w525,w378,w377,w580,w376] 0x18,l2C 119 6 0 [w806,w780,w779,w777,w776,w801] 0x72bf04c04c03e03e27527500300300300300000000000000300314414400014448214414400014400014400003f1440cd2c0,l2C 118 5 1 [w796,w795,w794,w817,w792,w819] 0x18,l2C 98 3 1 [w475,w820,w474,w473] 0x0,l2C 119 7 0 [w806,w780,w779,w789,w777,w776] 0x9e303e9e203e0070070070079e100704c04c04c00303f00303f03e00303f00300303e00700720a0070070079ae1019ad10103e1019e003e0070070070079df00703f10100300300303f0860860860869c20860860860860867df0860070070070070070070869af00708603f0860860860860a80a827c,l2C 82 3 1 [w122,w121,w120,w821] 0x0,l2C 119 7 0 [w806,w780,w779,w789,w788,w776,w801] 0x72bf0fd04c0fd04c0fd0fd15f2fd15f0070070070fd0fd0fd0079e10031380031380030030fd0fd0fd00300700300006c9e506c0009ad00700000300314c14c05305300014c4b105314c14c9c414c9c30fd0fd00700700714c9b203f14c0b62c0,l2C 83 3 1 [w823,w822,w77,w76] 0xd,l2C 82 3 1 [w122,w824,w121,w120] 0x0,l2C 87 6 0 [w94,w184,w92,w803,w91,w90] 0x5a03e05a05a05a0391b905a05a00005a16e9e807205a00005a2360001f80009e805a05a05a0009c700000005a05a23623605a0005f61f80009e716d16d,l2C 87 6 1 [w94,w184,w92,w803,w91,w90] 0x9e901d,l2C 119 8 0 (w806::w780::w779::v42) 0x4c04c04c04c9ea0079e600704c04c04c04c04c04c9e404c9dd0289bd02804c04c04c04c04c04c9b804c0070280030079d906c52a06c04c04c04c04c00706c52300702806c9d29d09cb0280530530530539c905304c04c04c04c04c04c0070530530539b30070539ac05305305305308508527c,l2C 103 5 0 [w379,w423,w421,w376,w538] 0x52052000000000000012012003003000000000000003003]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB47 : Array L2Cell := #[l2C 103 5 0 [w379,w423,w377,w538,w682] 0x1201801201800000000000002d01800301802d012003012003000000000000000003003003000000,l2C 103 5 0 [w379,w378,w423,w377,w538,w464] 0x0,l2C 37 3 1 [w828,w827,w826,w825] 0x0,l2C 103 6 0 (w379::w378::w423::v32) 0x180180009ef0009ee02d01200301201202d00302d0030030000000120030120030030000039ed0030030000039ec0180180000000000000030030030009b4003003003000,l2C 103 6 1 (w379::w378::w423::v32) 0x9f0,l2C 119 8 0 (w806::w830::w779::w829::v42) 0x5105105105100314a00314a05105105105105105100305102804002802802847202804005102f05105105105105102f14a00502802802800314a0050280420280289cf0420510510510510510510289b805114a04202801200314a0530532920b00b00b00b00510510510510b00b00b00b00b00b00b00b00850850b00280b09cb0b00850b00b00b00b00b00280b00b00530530530539f105305105105105105105114a05305305300314a0530422930530420530530530530530b00b00b00b00b00b00530b0,l2C 53 4 0 [w834,w833,w832,w831] 0x8008008008000000,l2C 53 4 1 [w834,w833,w832,w831] 0x9f3,l2C 117 5 0 [w786,w836,w810,w783,w782,w835] 0xd034000000176186,l2C 85 4 1 (w87::w283::v1) 0x55d,l2C 117 6 0 [w786,w836,w785,w810,w787,w782,w835] 0x8c0000349f69f50490340000722b900003b9f406c06c186,l2C 21 3 1 [w12,w837,w11,w10] 0x0,l2C 117 6 0 [w786,w785,w810,w838,w782] 0xd00d00d00d00400400400400d00d00d00d00400d0340340340349f403408c01d03408c01d08c0340340340340001769f417608c08c00d08c00417600417608c034034034034034,l2C 117 6 0 [w786,w836,w810,w783,w782] 0xd00d00d00d00400400400400d00d00d00d00400d0340340340349a70340342350340341da0340340341d90001769f517608c17600d176004176004176034034033,l2C 117 7 0 [w786,w836,w785,w810,w787,w782] 0x8c08c08c08c00400400400408c08c08c08c08c08c00408c03403403403455f03408c08c08c08c08c08c0349fa08c0340340340340040340340840340340349a703407208c01d08c01d08c08c08c08c0349f908c01d0341da0340340340040341d90342350349f806c9f706c08c08c08c08c00406c00406c03403406c034034034034034034033,l2C 117 7 1 [w786,w836,w785,w810,w787,w782] 0x9fb01d,l2C 117 5 1 [w786,w785,w809,w782,w839] 0x482,l2C 119 7 0 [w806,w830,w779,w778,w777,w776] 0x9e30139e20130180180180189fd01804802f08604804802f00301200301201300301200300301301801215d01801215d0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0cc0030cc0cc0860860860864a008608601308604808608600500521c0860860860860030860cc0cc0cc0cc0cc0cc0869af0cc,l2C 119 8 0 [w806,w830,w779,w789,w778,w788,w776] 0x4804804804801804001801801848201804004802f04804804804804802f0050050050059b20050480480480480480480059fe0480050532320030120030120480480480480480480030480180180120420180030120420050050050050030050b50b50b50b50480480480480b50b50b50850b50b50b50850b50b50b50b50b50b50b50b50b50b50b50030b50b50530530530534a005304804804804804804800500521c0050050050530050050050530530530530030530b50b50b50b50b50b50539b30b5,l2C 119 6 0 (w779::w840::w791::w789::v41) 0x24624603403400039d,l2C 119 7 0 (w806::w779::w840::w789::v41) 0x892f211204d11204d11211200304f00304f00300311211211200300003400003400000002804202804202802800002869e1120280280030b12f32462f4246089089089112112089003089089a000899b5089028,l2C 119 6 0 [w806,w830,w779,w777,w790,w801] 0x500501301300300300300320b20b20b20b20b20b00320b02d14415e2ba14400014400320b20b20b144000,l2C 119 6 0 [w806,w830,w779,w777,w776,w790,w801] 0x505002d15e144000,l2C 119 7 0 [w806,w830,w779,w789,w777,w776,w790] 0x8621d0000136bf0130009e20500500050050000509fd005050050a03050a0204604600315d00315d00300300300320a0501c50a81c50a81c51c51c51c51c51c50031c515e09115e0860860860860000500500500864a00860031c51c51c50869c2,l2C 119 7 0 [w806,w830,w779,w789,w788,w790,w801] 0x50530050500050e20e20e20e20402f01ab0050500050e20e20e2050a020030030030030e20e20e20030500031c41c41c41c41c41c41c41c40031c402d05314c0530402ba0e20e205005005014c49e14c0031c41c41c414c9c3,l2C 119 7 0 [w806,w830,w779,w789,w788,w776,w790,w801] 0x52a20500051ab005040050a0302d05304014c0009c4,l2C 119 7 0 [w806,w830,w779,w789,w788,w776,w790,w841] 0x539c1ab05000000002802d000,l2C 119 8 0 (w806::w830::w779::w789::v41) 0x5305321d04604604602f04604604602f0460460460460460461ab4ee050005a074820500050409c7050a06a05050046046046046046046a040461ab4ff0280429bd4720280420409c00289bd9bd0400460460460460460469b80460500280030500b10b10b10850b10b10b10850b10b10b10b10b10b10460460460460b10b10b10b10b10b10b10b10b1a010b10b10530400910530400530530530530530460460460460460460500530530534a00500530530530539f10530b10b10b10b10b10b10539c90b1,l2C 55 5 0 [w39,w37,w842,w36,w35] 0x7a07a07a00007a00000000004927a000000,l2C 55 5 1 [w39,w37,w842,w36,w35] 0xa09,l2C 55 5 0 [w39,w38,w37,w36,w843] 0x14014231000000000231231231000,l2C 55 5 1 [w39,w38,w37,w36,w843] 0xa0b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB48 : Array L2Cell := #[l2C 85 4 0 [w87,w83,w82,w815,w88] 0x8008017000,l2C 85 5 0 [w87,w84,w82,w815,w88] 0x800000000800000800800800d008008008000000017017008443000a0d,l2C 85 5 1 [w87,w84,w82,w815,w88] 0xa0e,l2C 113 3 1 [w847,w846,w845,w844] 0xd,l2C 97 3 1 [w529,w528,w848,w527] 0x0,l2C 69 3 1 [w139,w138,w849,w137] 0x0,l2C 117 6 0 [w786,w785,w810,w809,w850,w782] 0x1f809f09f00009f18c0001b909f09f09f0009d709f09f18c18c09f0005d61b91a21a209f00009f16ea12072000a11000a1009f10109f09f09f03b000000,l2C 117 6 1 [w786,w785,w810,w809,w850,w782] 0xa1301d,l2C 119 8 0 [w806,w830,w779,w789,w788,w851,w776] 0x5339805309109109109109109109109109102f09109109102f0400402080409d72080400402081f60405d620839a091091091091091091a14091040040040040a0f0400400400400960405d4040394091091091091091091a0c0912080280032080e90e90e90e90e90e90e90e90e93970e90e90e93990910910910910e90e90e90e90e90e90e90e90e9a0a0e90e90530530530530400530530530400460910910910912080530532080530530530530e90e90e90e90e90e90530e9,l2C 119 7 0 (w806::w779::w840::w791::v42) 0xfe0fe0fe00424600000024604d0fe0fe04d04f00400404f0000340000340330fe0fe03303f03400403f08930803469e0fe03403400406c2cf2cf0b00b0089a000fe0fe089004034309034089034089089089089138089,l2C 103 5 0 [w380,w378,w852,w377,w376,w464] 0x40000000a7,l2C 103 6 0 [w380,w378,w852,w377,w376] 0xa1700000400400400400400400400400413d00400469e13d00400413d00400413d00401a13d00400413d0030a70030a70030a70030a700400400313d0a700400400413d,l2C 103 6 1 [w380,w378,w852,w377,w376] 0xa18,l2C 102 4 0 [w457,w413,w412,w511] 0x3003000000000000000000000000,l2C 102 4 1 [w457,w413,w412,w511] 0xa1a,l2C 119 7 0 [w806,w779,w840,w789,w853,w776] 0x1601601601601221001221001601621001601221003403403403404d0ad04d04d210012012210042042042042a1b04204d04d04d2100420420420122100ad0ad26d028225028225016225016225210225012210034034225034028225042042225042028225,l2C 103 5 0 [w380,w510,w854,w377,w682] 0x4004000000000000,l2C 103 6 0 [w380,w510,w377,w376,w682] 0x12012012000000000000000a1d00000094c00000000401a00000400400000400400000400400000400000400000300000300069e00300069e00300000369e00300469e00369e69e004,l2C 103 6 1 [w380,w510,w377,w376,w682] 0xa1e,l2C 119 7 0 [w806,w779,w840,w789,w788,w776,w855] 0x422fa08304d08304d08308301204f01204f01201208308308301239f0853a10850340342463a0246042042042246042083083083083083042a1b08329c04201229c04a39e028089028089028028034028042326028326,l2C 103 5 0 [w856,w380,w510,w377,w376,w464] 0x4000,l2C 103 6 0 (w856::w380::v26) 0xa2100000400400400400400400400400300300300300300300300300400400400400300401201201201201269e012012012012012012012012004012,l2C 103 6 1 (w856::w380::v26) 0xa22,l2C 119 8 0 (w806::w779::w840::v42) 0x4d04d04d04da0a04f6a004f04d04d04d04d04d04d6a004da0a03458303404d04d04d04d04f03400404fa0a042a23a20a1f04204d04d04d04da1c04d04f0426a00126a004f08508526da0a089a0108904d04d04d04d04f08900304f034a19089a169cb089042089028089,l2C 118 5 0 [w859,w858,w797,w792,w857] 0xa70a7000000000000028028003003003003000000000000,l2C 118 5 0 [w796,w795,w858,w797,w860,w857] 0x0,l2C 118 5 0 [w796,w858,w797,w798,w857] 0x180280180280000000000001ab0280030281ab018003018003003000003000000000000000003000,l2C 118 5 0 [w796,w795,w861,w792,w857] 0x5205200600600000020a20a003003000003000000003000000000000003003,l2C 118 6 0 [w796,w795,w858,w797,w792,w857] 0x180180000000000001ab0280030280281ab0031ab003003003000003a28000028003028003003000003a2700300300000301801800051f000a26003000003003003000a25,l2C 118 6 1 [w796,w795,w858,w797,w792,w857] 0xa29,l2C 118 5 1 [w796,w795,w861,w792,w857] 0xa28,l2C 54 3 1 [w865,w864,w863,w862] 0x0]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB49 : Array L2Cell := #[l2C 119 7 0 [w806,w830,w779,w789,w866,w776] 0xa2c00a00a00a00aa2b00a00a01619c01215d0120128a815d01301319d00a00a15d04500a00a02b02b02b02b02b02b02b02b02b02b02b02b02b02b02b02b02b02b01202b00305200305200305200305200a00a00a00a00300a15d01201201200315d02b02b02b02b02b02b00302b,l2C 117 6 1 [w786,w785,w810,w787,w782,w867] 0x55601d,l2C 119 8 0 [w806,w830,w779,w789,w868,w788,w776] 0x45045045045012040012012012a2e01204004502f04502f045045045045012a2d04502f005005005005a2a00504504504504504504500504500504219c0120420120125b504204504504504504504501204500500519d0050050050420050050050d30d30d30d30450450450450d30d30d30850d30d30d30850d30d30d30d30d30d30d30d30d30d30d30120d36a00d30032760032760450450450450120122760530120032760530050050050050030050420122760120032760d30d30d30d30d30d30030d3,l2C 23 4 0 [w16,w869,w14,w13] 0x8008008008000000,l2C 23 4 1 [w16,w869,w14,w13] 0xa30,l2C 87 6 0 [w94,w92,w870,w91,w90] 0x44a3104400d00d00d00d08d08d00d08d016016016016a3101604401608d01601604408d01d04408d01d08d00600600600604400600604400d00d00d00d00600d016016016016,l2C 85 5 0 [w87,w84,w82,w80,w871] 0xd00d00000800000800000000800100800100d00d00d00d00001700001700000000d000,l2C 85 5 1 [w87,w84,w82,w80,w871] 0xa3347f,l2C 87 5 0 [w94,w872,w177,w91,w90,w261] 0x4400000d01600000016a,l2C 87 6 0 [w94,w872,w177,w91,w90] 0x44a3504400d00d00d00d04408d00d044016016016016a3401601602b0160161d901600600600600604400600604400d00d00d00d00600d016016266016016235,l2C 85 4 0 [w87,w873,w82,w88,w89] 0x1001008000,l2C 85 5 0 (w87::w873::v0) 0xd00d001001000a3700000d00800d00800d00844600d00000000000000d000,l2C 85 5 1 (w87::w873::v0) 0xa38,l2C 85 4 1 [w87,w873,w82,w88,w89] 0xa37,l2C 87 6 0 [w94,w93,w872,w92,w91,w90,w261] 0x13000016a3a0130140160000722ff00016a00008da35039a31,l2C 21 3 1 [w874,w12,w11,w10] 0x0,l2C 87 7 0 (w94::w93::w872::v3) 0xa3c013a3b013016016016016a39016013013016016016013013016084016016016a3401607201602b0160131d901308d08d08d08d08d08d08d08d08d08d08d08d08d01608da3608d08d08d08d08d01d01d08d01608da3208d01d00600600600601300600601301601601601600601601601601626601600601623508d08d08d08d08d08d00608d,l2C 87 7 1 (w94::w93::w872::v3) 0xa3d01d,l2C 118 5 0 [w796,w794,w793,w875,w798] 0x6006000000000000000000000000,l2C 118 6 0 [w796,w794,w793,w792,w798] 0x280280280000060540000060060000060060000060060000030000030008a80030008a80030068a80038a88a8006000000000000000a3f0000007910000060000000060030008a8003,l2C 118 6 1 [w796,w794,w793,w792,w798] 0xa40,l2C 119 7 0 [w806,w830,w779,w789,w853,w776,w855] 0x4209618b02f02e02f01601601200a01200a01201201601220c18b20c04204204220c04202e02e1c00420121c01ac0ad1ac0ad1ac1ac1ac1ac1ac1ac0421aca1b1ac02817f02817f0280280423250283251ac1ac1ac028,l2C 118 5 0 [w876,w796,w794,w793,w792,w860] 0x6000000,l2C 118 6 0 [w876,w796,w794,w793,w792] 0x6006006006003003003003006006006006003006000000a430000060060060060030030030030280280280280280280288a8028028006028028028028028,l2C 118 6 1 [w876,w796,w794,w793,w792] 0xa44,l2C 119 6 0 [w806,w830,w779,w853,w866,w776,w801] 0x20c20c0160160002ea,l2C 119 7 0 [w806,w830,w779,w789,w853,w866,w776] 0x20c00000020c00001600001600a19d00aa4601619c01600a01600a00a00a00a0168a801319d19d04504515d00a20e0ad20e0ad20e02b20e02b20e20e20e01600617f00617f01605200601600a00601600620e20e20e006,l2C 118 5 0 [w796,w795,w794,w877,w792,w860] 0x6000052000,l2C 118 6 0 [w796,w795,w794,w877,w792] 0x600600600600600300600305200305200628b0060068a828b00605405200600628b05200628b006006052000000a4800000600600600605200300305228b00600600600628b,l2C 118 6 1 [w796,w795,w794,w877,w792] 0xa49,l2C 119 7 0 [w806,w830,w779,w789,w853,w776,w801] 0xa1f600001600001600000020c09220c00a00a00a00a00aa4600aa2b0120420120420120120000128a804104100a01220d0ad20d0ad20d20d20d20d20d01200317f00317f00300300a00301200320d20d20d003,l2C 119 7 0 [w806,w830,w779,w789,w853,w776,w878] 0x1609620c18b20c01620c01600000a00000a00000001600001418b18b01602e02e02e20f0ad20f0ad20f20f20f20f20f01600617f00617f00600601600601600620f20f20f006]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB50 : Array L2Cell := #[l2C 119 8 0 [w806,w830,w779,w789,w853,w776] 0xa0c016a4c016a0c00aa4b00a016a4a00aa47a2d00aa0c042a45a42a4104202f02f02f00a04201200a0ad0ad0ad0ad0ad0ad0ad0ad0ad0ad0ad0ad0ad0ad0ad0ada1c0ada0c17f9b817f01617f00617f00a17f00300a0429b817f0289b817f0ad0ad0ad0ad0ad0ad9b80ad,l2C 87 6 0 [w93,w92,w879,w91,w90] 0x14014014014014014014014006006006006016016016016008008008008008008006008014014014014014014016396016016016016014014014014008008008008016016016016016016008016,l2C 87 6 0 [w94,w92,w880,w91,w90] 0x1401401401401407207207207207200807201601607201d07201d072072014014014014014072016016016016014014014014006006006006072072072072008008006072016016016016,l2C 87 6 0 [w94,w93,w92,w881,w90] 0x14014014014014014014014014014016395016016016016014014014014008008008008016016016016016016008016014014014014006006006006016016016016008008008008008008006008,l2C 87 6 0 [w94,w93,w92,w91,w881,w90] 0x1418c0390140140140140143950720140140140161da01602b01601601601601600801d00801d00800800800801601601600800621e006234006006006006008008008006,l2C 87 7 0 (w94::w93::w882::v3) 0x14014014014014014014014014014016016016016016014084014014a51014a5001416e014072072014a4f014006014a4e072072072072072072072072072072072072072016072072014014014014006006006006016016016016072072072072072072006072,l2C 87 7 1 (w94::w93::w882::v3) 0xa5201d,l2C 85 4 0 [w87,w802,w82,w86,w88] 0x8008001000,l2C 85 5 0 [w87,w84,w802,w82,w88] 0x1001008449000008008008000a5400800d008008008000000008000000000,l2C 85 5 1 [w87,w84,w802,w82,w88] 0xa55,l2C 119 8 0 [w806,w830,w779,w789,w788,w776,w855] 0x4204209602e02e02e02f02e02e02e02f02e02e02e02e02e02e8aa56b1400058aaa2e140005040a561408aa8aa14002e02e02e02e02e02e8aa02e04004018b04004004204204004004202e02e02e02e02e02ea42a4102e140042a390125b514004a04a04a08504a04a04a08504a04a04a04a04a04a02e02e02e02e04a04a04a04a04a04a04a04a04aa2004aa1f04a9bd5c325d0539bd47225d053040a0f25d9bd9bd25d02e02e02e02e14025d00314004255f25d0289cf25d04a04a04a04a04a04a9bd04a,l2C 102 5 0 [w416,w415,w883,w412] 0x3003003003003003003003003003003003000000000000000000000000003003003003003003,l2C 102 5 1 [w416,w415,w883,w412] 0xa58,l2C 102 5 0 [w884,w415,w456,w412] 0x3003003003003003003003003003003003003003003003003003000000000000000000000000,l2C 102 5 1 [w884,w415,w456,w412] 0xa5a,l2C 119 8 0 (w885::w806::w830::w779::v42) 0x9609609609604025c01225c096096096096096096012096040040042042042040040096096096096096096042a4509625c04204204201225c0af0af0af0af0960960960960af0af0af0af0af0af0af0af0af0420afa230af0af0af0af0af26d26d0af0420afa5b0af39204028a02828a09609609609625c28a01225c04204228a04202828a0af0af0af0af0af0af0280af04204228a29204202828a39104202e04209602f09602f096096096096042a5909602f25c19d04204204201225c393040394040,l2C 21 2 1 [w12,w367,w10] 0x0,l2C 85 4 1 [w87,w84,w81,w335,w80] 0x0,l2C 85 4 1 [w87,w84,w81,w799,w89] 0x0,l2C 87 6 0 [w94,w93,w92,w91,w176,w800,w90] 0x14000014000000014a5f295a5ea5d0160002b40009da,l2C 21 3 1 [w12,w11,w886,w10] 0x0,l2C 85 4 0 [w87,w84,w799,w86,w89] 0x800800d000,l2C 85 5 0 [w87,w84,w82,w799,w89] 0x800800800800100800800800d00d008449000a62000000008000000000,l2C 85 5 1 [w87,w84,w82,w799,w89] 0xa63,l2C 87 6 0 (w94::w92::w177::v43) 0x7207a07aa6407a18c5e01b900d07a08401d01b01d07a01607a07a07a01b01b01600008408407a00607a2360061f800d006006016,l2C 85 4 1 [w87,w84,w799,w86,w89] 0xa62,l2C 87 6 0 [w94,w93,w92,w91,w800,w208,w90] 0x140140130001b9a663050000161b6000,l2C 21 3 1 [w12,w887,w11,w10] 0x0,l2C 87 7 0 (w94::w93::w92::v43) 0x14072014014014014014a6401401401401418c0145e00141b901401401601401401401401401401ba68016a6701608408408408408408408408408401d08408408401d084084084084084084084084084a650840840140140140149c00140140140142360145dd0141f8a61006a600060160060060160840840840840840849dc084,l2C 87 7 1 (w94::w93::w92::v43) 0xa6901d,l2C 117 5 0 [w785,w810,w809,w888,w782,w835] 0x9f09f0000002b5,l2C 117 5 0 [w786,w889,w785,w809,w888,w782] 0x7700101723503a000000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB51 : Array L2Cell := #[l2C 117 5 0 [w786,w785,w810,w888,w890,w782] 0x77000077001101,l2C 117 5 0 [w786,w785,w809,w888,w782,w781] 0x1709f00009f001000,l2C 117 6 0 [w786,w785,w810,w809,w888,w782] 0x9f00000009f00100010121e001a6e01721e21e03a03a7ff077000077001a6da6c001000a6b0011f900110100110100103a0009ef,l2C 117 6 1 [w786,w785,w810,w809,w888,w782] 0xa6f01d,l2C 117 5 0 [w786,w785,w891,w809,w782] 0x1f92340770000770771d908d000000000000077077077077,l2C 117 5 0 [w786,w889,w811,w809,w782] 0x10010770003020770000770000000000000772b7077077,l2C 53 3 1 [w834,w893,w833,w892] 0x0,l2C 117 5 0 [w786,w889,w785,w809,w782,w835] 0x107700000007700000003b000000000,l2C 117 5 0 [w786,w889,w785,w809,w782,w894] 0x77000001008072000039,l2C 117 6 0 [w786,w889,w785,w809,w782] 0x1a75001077077077077a3907707700107708d077077077077077077077077a3407708d01d08d01d08d07707708d01d01a1d901a000000a74a73001000a6c001077077077077a72077077077077077a71077,l2C 117 6 1 [w786,w889,w785,w809,w782] 0xa76,l2C 119 6 0 [w806,w830,w779,w777,w866,w776,w801] 0x1615e00015e04501301315d000013,l2C 119 6 0 [w806,w830,w779,w789,w866,w776,w895] 0x15e15e00009800002b,l2C 119 7 0 [w806,w830,w779,w789,w777,w866,w776] 0x15e00000015e000013a7901315d19c00aa7801619c19c0450450125b501319d01301301315d01315d00a15d00a00a00a1c60a81c60a81c602b1c602b1c61c61c61c60121c600308600308601305200301300a0030120031c61c61c6003,l2C 117 5 0 [w786,w785,w784,w809,w896,w782] 0x770002b4000,l2C 69 3 1 [w139,w897,w138,w137] 0x0,l2C 117 6 0 [w786,w785,w810,w809,w896,w782] 0x7209f09f00009f18c0001b909f09f09f004a6409f09f18c18c09f0045e01b908408409f07709f09f09f01b00400407707709f00009f236a7c1f8004a7b,l2C 117 6 1 [w786,w785,w810,w809,w896,w782] 0xa7d01d,l2C 117 5 1 [w786,w785,w809,w850,w781] 0x9d7,l2C 117 5 1 [w786,w785,w809,w898,w782] 0x5e9,l2C 117 5 0 [w786,w785,w899,w782,w781] 0x1523a200130000100107707700400400116a000000000000,l2C 117 5 1 [w786,w785,w899,w782,w781] 0xa81,l2C 118 5 0 [w796,w795,w817,w798,w857] 0x1820a01820a01800000000020a00320a000003003003000003000000000000000003003003000000,l2C 118 5 1 [w796,w795,w817,w798,w857] 0xa83,l2C 117 5 1 [w786,w785,w809,w896,w781] 0xa64,l2C 117 5 1 [w786,w785,w809,w782,w781,w867] 0x39,l2C 119 7 0 [w806,w830,w779,w777,w776,w801] 0x50051f615e04102f04104102f15e01301304115e01302d01215da8601215d15ea850128aaa8415e013a82012a78a2b0130cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd0cd6a00cd0cd02da801440009fd14415ea7f144a03a021440131446c11440121440031440cd0cd0cd0cd0cd0cd9e10cd,l2C 117 5 0 [w786,w785,w784,w809,w782,w894] 0x8101000101000001,l2C 117 5 0 [w786,w785,w810,w809,w835,w894] 0x101303101000000,l2C 117 5 0 [w786,w785,w810,w890,w782,w894] 0x9f09f000077001,l2C 117 6 0 [w786,w785,w810,w809,w782,w894] 0x118c09f16d09f00109f00100816d16d00103903903993a0770000770007c3001a8aa75001000101000101000a89001000001a88,l2C 117 6 1 [w786,w785,w810,w809,w782,w894] 0xa8b01d]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB52 : Array L2Cell := #[l2C 117 5 0 [w786,w785,w900,w784,w809,w782] 0x16d1010000000012b4000,l2C 97 3 1 [w529,w901,w528,w527] 0x0,l2C 117 6 0 [w786,w785,w900,w810,w809,w782] 0x9f00109f09f09f03909f09f16d16d09f0390391b909f09f000001a8e00000109f16ea8e07209f9c7000001001a8d09f2360001f8,l2C 117 6 1 [w786,w785,w900,w810,w809,w782] 0xa8f01d,l2C 119 8 0 [w806,w830,w779,w789,w777,w776] 0xa90013a8c013005005005005a8700502f02f02fa7e0128aa0120136b7012a7aa2d013005005a770050050050a80a80a80a80a80a80a80a80a80a80a80a80a80a80a80a80a80a80a86a00a80a8a14086a04086013086a700860050050050059fe0050120860030860a80a80a80a80a80a89e40a8,l2C 119 7 0 [w806,w830,w779,w789,w788,w776,w801,w841] 0x2a22a21ab00000001202d14c000,l2C 119 8 0 [w806,w830,w779,w789,w788,w776,w801] 0x50051f604104104102f04104104102f041041041041041041005040092005040005005005005005041041041041041041005a8704102d5ed0120428aaa2e012042040a640128aa8aa040041041041041041041a4b041005005005005a2a0050b60b60b60850b60b60b60850b60b60b60b60b60b60410410410410b60b60b60b60b60b60b60b60b60b60b66a00b60b602d5e914c053a9248214c0530409d714ca06a0514c0410410410410050050050059b200501214c00314c0b60b60b60b60b60b69e60b6,l2C 119 8 0 [w806,w830,w779,w789,w788,w902,w776] 0x539a00509209209209209209209209209202f09209209202f005005005005040005005005040041092092092092092092005092040040040040a560400400400400960405f9040394092092092092092092a0c0920050050050050e80e80e80e80e80e80e80e80e83970e80e80e83990920920920920e80e80e80e80e80e80e80e80e8a0a0e80e80400402a50409c72a50400402a521d0405f62a53980920920920920050050050050122a50032a50e80e80e80e80e80e89ea0e8,l2C 119 9 0 (w806::w830::w779::v42) 0x2f02f02f02fa94005a9300502f02f02f02f02f02fa9102fa6aa5ca57a5302f02f02f02f02f02fa4d02f005a3ea2f00508508508508502f02f02f02f085085085085085085085085085a24085085a15053a0805302f02f02f02f0050539ff0059fc0539f20530850850850850850859eb085,l2C 119 9 1 (w806::w830::w779::v42) 0xa95,l2C 91 6 0 [w98,w101,w133,w97,w96] 0x600600600601601601601601601600600600600601601601601601601601603c01600d00d00d00d00d00d00d00d00d00d00d00d00d00d016016016016,l2C 91 6 1 [w98,w101,w133,w97,w96] 0xa97,l2C 123 7 0 [w908,w907,w906,w905,w904,w903] 0x32032032032032032032032032032010010010010032032032032032032010032010010010010042010132132327073073073073032032032032010010010010073073073073073073073073073073073055073073055055055055032032032032010010010010055055055055042055,l2C 123 7 0 [w908,w907,w905,w904,w909,w903] 0x13204227b032032032032032032032032032032010010010010010010010010010010032032032032032032010032073073073073073073073073073073032032032032010010010010073073073073073055073073055055055055055055055055055055032032032032010010010010,l2C 123 7 0 [w908,w907,w906,w905,w904,w909,w903] 0x4227b03203603203603203203203203203203203201000e01000e010010010010032032032010010010010010042010010132327132132132132042042132132073145073145073073073073073073073073073073055073055192055192055055055055055055055055042055055,l2C 121 6 0 [w914,w913,w912,w911,w910] 0xd00d00d00d00d00d00d00d00d00d03403403403400400400400403403403403403403402202202200000000000000d00d00d00d004004004004034034034034034034,l2C 121 6 1 [w914,w913,w912,w911,w910] 0xa9c,l2C 123 8 0 [w908,w907,w906,w905,w904,w909] 0x3603603603603603603603600e00e00e00e03603603603603603600e03600e00e00e00e00ea9d00e00e13285104284fa9ba9aa9913214514514514503603603603600e00e00e00e14514514514514514514514514519214514519219219219203603603603600e00e00e00e192192192192192a98192192,l2C 123 8 1 [w908,w907,w906,w905,w904,w909] 0xa9e,l2C 127 7 0 [w921,w920,w919,w918,w917,w916,w915] 0x28c28c22733022733022722725f32f25f32f25f25f22722722725f03432e0f43a532e2123a628c24932d24932d2492492492492492490be28c0be28c3a428c22722725f25f,l2C 127 8 0 [w920,w919,w918,w917,w922,w916,w915] 0x1031033a8212aa02121542120642120be0be0be0be0be0be0be0be0be0be0be0be0be0be0be0be0f70f70f70f70f70f70f70f70f70f70f70f70f70f70f70f70f70f70be0be0be0be0be0be0f70bea0a04b04b04b21204b04a04b04b21221221207304b2122120be0be0be0be0f70f70f70f711b11b11b11b11b11b11b11b11b11b11b11b11b11b11b11b11b11b0be0be0be0be0f70f70f70f711b11b11b11b11b11b,l2C 127 9 0 [w920,w919,w923,w918,w917,w922,w916] 0xe11803dd0e00e00e00e00e00e00e00e00e00e00e00e00e00e00eb0eb0eb0eb0eb0eb0eb0eb0eb0eb0eb0eb0e00e00e00e00e00e00eb0e00eb0eb0eb0eb0eb1030eb0eb103103103103aa11031031031031031030e11031030e10b71180b70b71180e10e11450b70e10e10e00e00e00e00eb0eb0eb0eb1031031031031601601601601601601601601601600e00e00e00e00eb0eb0eb0eb103103103103103103160103160160160160160160,l2C 127 9 0 [w920,w925,w919,w923,w918,w917,w922,w924] 0xe114540b0a20a20a20d80a20a20a20d80a20a20a20a20a20a20a20a20a20a20aa0aa0aa0f00aa0aa0aa0f00aa0aa0aa0aa0aa0aa0a20a20a20a20a20a20aa0a20aa0aa0aa0aa0aa0b30aa0aa0b30b30b30ef0b30b30b30ef0b30b30b30b30b30e10b30b30e10e140c0e10e10e11450e10e10e10a20a20a20a20a20a20aa0aa0aa0aa0aa0aa0b30b30b30b30b30b32df1313493490e10e10e10b70b70e10a20a20a20a22df0a20aa0aa0aa0aa0aa0aa0b30b30b30b32df0b30b70b70b71221221221631221221221631221221221221221220a20a20a20a20aa0aa0aa0aa0b30b30b30b30b30b31220b3122122122122122122122122122122,l2C 127 8 0 [w920,w925,w919,w918,w917,w922,w927,w926] 0x734080343483480b30b31d40c21d40c21d41d41d41d42300f82300f82302301d41d41d42302464092460730730731d41d423023004908f08f24a24a3473471d424a2302300a90a9279130279130279279279279,l2C 127 9 0 [w920,w925,w919,w918,w917,w922,w927] 0xef0ef4060c20c20c20c20c20c20c20c20c20c20f80f80f80f80f80f80f80f80f80f80c20c20c20c20c20c20f80c2a0a073aa40730e10e10e10e10c20c20c20c20f80f80f80f80640640640640640640e10e10e10e10e10e10c20c20c20c20640c20f80f80f80f80f80f80ee0ee4071301301301301301301301301301300c20c20c20c20f80f80f80f8130130130130130130130130130130,l2C 127 10 0 (w920::w925::w919::w923::v44) 0xd80d80d80d80d80d80d80d80f00f00f00f00d80d80d80d80d80d80f00d80f00f00f00f00f00ef0f00f00ef0ef0ef0ef0efaa50ef0ef0e1145aa30e10d80d80d80d80f00f00f00f00ef0ef0ef0ef0e1180180180aa20e10d80d80d80d81800d80f00f00f00f00f00f00ef0ef0ef0ef1800ef11811840a1631631631630d80d80d80d80f00f00f00f00ef0ef0ef0ef0ef0ef1630ef163163163163163163163163163163,l2C 127 6 0 [w930,w925,w918,w917,w929,w922,w928] 0x0,l2C 127 6 0 [w930,w918,w917,w932,w929,w922,w931] 0x28,l2C 127 7 0 [w930,w925,w918,w917,w929,w922,w931] 0x2803d03d03d03d52e52e52e00200252e002aa8055055055963aa703d791055055,l2C 127 6 0 [w930,w918,w917,w932,w929,w922,w915] 0x0,l2C 127 7 0 (w930::w925::w918::w917::w929::v45) 0x3d028080aaa,l2C 127 5 0 [w934,w918,w917,w932,w933,w915] 0x0]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB53 : Array L2Cell := #[l2C 127 6 0 (w930::w934::w918::w917::v46) 0xaac,l2C 127 7 0 (w930::w934::w925::w918::w917::v45) 0x28aad04a96304a470791,l2C 127 6 0 [w930,w925,w918,w917,w935,w922,w931] 0x0,l2C 127 6 0 [w920,w930,w918,w917,w932,w922,w926] 0x0,l2C 127 7 0 [w920,w930,w925,w918,w917,w922,w931,w926] 0x4aab0aaf,l2C 127 6 0 [w920,w930,w918,w917,w936,w922,w915] 0x0,l2C 127 6 0 [w920,w930,w925,w917,w937,w922,w915] 0x0,l2C 127 6 0 [w920,w930,w925,w918,w938,w922,w915] 0x0,l2C 127 7 0 [w920,w930,w925,w918,w917,w922,w915,w928] 0x463ab402eab3043ab2aa7,l2C 127 7 0 (w920::w930::w918::w917::w939::v45) 0x280283cb03d,l2C 127 5 0 (w930::w941::w940::v46) 0x0,l2C 127 5 0 [w930,w918,w941,w932,w915,w942] 0x0,l2C 127 6 0 (w930::w918::w917::w941::v46) 0xab8ab7,l2C 127 6 0 [w920,w930,w918,w917,w932,w933,w915] 0x963aac,l2C 127 5 0 [w920,w930,w940,w932,w915,w942] 0x0,l2C 127 6 0 (w920::w930::w917::w940::v46) 0x97fabbab7,l2C 127 6 0 [w920,w930,w918,w917,w932,w915,w942] 0x97fabbab8,l2C 127 6 0 [w920,w930,w918,w917,w932,w922,w943] 0x0,l2C 127 7 0 (w920::w930::w918::w917::v46) 0x281950800681951ca97fabe195abd335335002002abc002963ab0195aba195195195aadaaa195195195195ab9195002,l2C 127 7 0 (w920::w930::w918::w917::w932::v45) 0x2808003daaaaa8,l2C 127 8 0 (w920::w930::w925::w918::w917::v45) 0x583b10282a90280282a952e2ab52e2ab52e2ab52e2ab2a952e0022aa0022aa0022aa0022aa00200252e002ac0178abfab61781781789632a8ab52a89632a8ab12a82a979117817803d03d03daaeaab334aab03daa905803d05803d52e03d002,l2C 127 5 0 [w934,w918,w917,w936,w929,w922] 0x0,l2C 127 5 0 [w934,w925,w917,w937,w929,w922] 0x0,l2C 127 5 0 [w934,w925,w918,w938,w929,w922] 0x0,l2C 127 6 0 [w934,w925,w918,w917,w929,w922,w928] 0x463ac4090ac32c6ac2,l2C 127 7 0 [w934,w925,w918,w917,w929,w922] 0x3d03d03d03d03d03d03d03d21403d5c32145c32145c321403d22803d2280020022280020022282140022280020025c300221403d03d3c503d05503d03d03d21405505505505521422805505522803d03d03d03d5c35c3ac55c32145c35c3214228002002228055055055055055055,l2C 127 8 0 [w920,w930,w925,w918,w917,w929,w922] 0x3d03d05803d03d03d03d03d1cd03d5c31cd5c31cd5c31cd03d1e703d1e70020021e70020021e71cd0021e70020025c30021cd03d03d33403d05506805803d03d03d1cd0550550550551cd1e70550551e703d03d21303d5c32135c32135c32131cd2135c31cd1e72130021e705521305505505521305803d21303d03d03d5c3ac621303d05803d03d03d05803daa903d1cd05803d1cd1e705803d1e703d05803d03d055058,l2C 127 6 0 [w944,w934,w925,w918,w917,w929,w922] 0x0,l2C 127 7 0 [w934,w925,w918,w917,w929,w922,w915] 0x2828d28d28d3c403d52e21452e21428d52e52e52e00222800222800200200200252e0029f82902902905c375bac5ac804a3b0290290,l2C 127 6 0 [w934,w925,w918,w917,w945,w922,w915] 0x3d,l2C 127 6 0 [w934,w925,w918,w917,w929,w922,w926] 0x0,l2C 127 7 0 [w930,w934,w925,w918,w917,w929,w922,w915] 0x75baa704a9635c3acb5c328d791aca3b0]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB54 : Array L2Cell := #[l2C 127 7 0 [w920,w930,w925,w918,w917,w945,w922,w915] 0x3daca2d6,l2C 127 7 0 [w920,w930,w925,w918,w917,w929,w922,w926] 0xacb03daa7,l2C 127 8 0 [w920,w930,w925,w918,w917,w929,w922,w915] 0x282652653c72653c93b305852e1cd52e1cd26552e52e3bd52e0470021e70021e700233100233100200252e0029f82292293c62293c8229229963213ace2132657919633b2acd3b422922903d03d03daccac903d05803daab03daa9058265265aab3ca229229,l2C 127 5 0 (w934::w925::w946::v47) 0x0,l2C 127 5 0 [w934,w925,w918,w947,w933,w915] 0x0,l2C 127 6 0 (w944::w934::v61) 0xad1ad0,l2C 127 5 0 [w934,w918,w917,w936,w933,w915] 0x0,l2C 127 5 0 [w934,w925,w917,w937,w933,w915] 0x470,l2C 127 5 0 [w934,w925,w918,w938,w933,w915] 0x0,l2C 127 6 0 [w934,w925,w918,w917,w933,w915,w928] 0x28470ad53d2ad42dcad3,l2C 127 5 0 (w934::w948::w918::v47) 0x0,l2C 127 5 0 [w950,w925,w918,w917,w949,w933] 0x0,l2C 127 6 0 (w950::w934::v61) 0xad83d003dad7,l2C 127 6 0 [w934,w925,w918,w917,w949,w933,w915] 0x5c3ad8,l2C 127 7 0 (w934::v61) 0x10e13804a04a04a04a01b21501b21501b01b21501b01b21579356b22b793a2e22b10e22b10e22b21501b22b01b01b01b7932151970493d119719704b19721519719719719721522b19719722badaad9ad6ad205f10e05f05f21501b01b21522b79379322b197197197197,l2C 127 5 0 [w934,w925,w946,w917,w951,w922] 0x0,l2C 127 5 0 [w934,w925,w918,w947,w951,w922] 0x0,l2C 127 6 0 [w944,w934,w925,w918,w917,w951,w922] 0xaddadc,l2C 127 5 0 [w934,w948,w918,w917,w951,w922] 0x0,l2C 127 6 0 [w950,w934,w925,w918,w917,w951,w922] 0x470adf,l2C 127 7 0 [w934,w925,w918,w917,w951,w922,w915] 0x3428f03428f13828f28f3b004a01b01b28f01b01b01b96396396396301b01b01b9630492db0492db2dbae0ade03d3c4,l2C 127 6 0 (w930::w934::w925::w946::v48) 0xadcad0,l2C 127 6 0 [w930,w934,w925,w918,w947,w922,w915] 0xaddad1,l2C 127 7 0 (w930::w944::w934::v62) 0xae3ae2adead23c43b0,l2C 127 6 0 [w930,w934,w918,w917,w936,w922,w915] 0xad3,l2C 127 6 0 [w930,w934,w925,w917,w937,w922,w915] 0x470ad4,l2C 127 6 0 [w930,w934,w925,w918,w938,w922,w915] 0xad5,l2C 127 6 0 [w952,w930,w934,w925,w918,w917,w915] 0x28,l2C 127 7 0 [w930,w934,w925,w918,w917,w922,w915,w928] 0xae8ae716cae62dcae5963470ad6,l2C 127 6 0 (w930::w934::w948::v57) 0xadfad7,l2C 127 6 0 [w930,w934,w925,w918,w917,w953,w915] 0x3d,l2C 127 6 0 [w950,w930,w925,w918,w917,w949,w922] 0xad8]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB55 : Array L2Cell := #[l2C 127 7 0 (w950::w930::w934::v62) 0xaecae0ad9aebaea3b003d,l2C 127 7 0 [w930,w934,w925,w918,w917,w949,w922,w915] 0xaec5c3adaaca,l2C 127 8 0 (w930::w934::v62) 0x5f03427701b0d501b0d505f05f0d505f01b0d57c256b0ea7c2a2e0ea05f0ea05f0ea0d501b0ea01b01b01b7c20d506d04926005f05f33d05f0d506d06d06d06d0d50ea06d06d0eaaeeaedae9ae405f05f05f05f0d501b01b0d50ea7c27c20ea06d06d06d06d04aae104b04a04b04a05f05f04b05f05f05f04aadb04b0d504b04a04a01b0d50ea04b04a04a7c20ea06d04b06d04b04a03d2d6,l2C 127 6 0 (w920::w934::w925::w946::v48) 0x0,l2C 127 6 0 [w920,w934,w925,w918,w947,w922,w915] 0x0,l2C 127 7 0 (w920::w944::w934::v62) 0xaf1af0ac83b03c4,l2C 127 6 0 [w934,w925,w918,w917,w935,w922,w915] 0x3d,l2C 127 6 0 [w920,w934,w918,w917,w936,w922,w915] 0xac2,l2C 127 6 0 [w920,w934,w925,w917,w937,w922,w915] 0xac3,l2C 127 6 0 [w920,w934,w925,w918,w938,w922,w915] 0xac4,l2C 127 7 0 [w920,w934,w925,w918,w917,w922,w915,w928] 0x463af616caf52dcaf4af3ac5,l2C 127 7 0 [w920,w934,w918,w917,w939,w922,w915] 0x283da2d526005a05a2dd05a05a05a05a0029f81952dd2dd19505a1950023dc3db,l2C 127 8 0 (w920::w934::v62) 0x5f0282774e50d54e50d505f05f0d505f4e50d50020020ea0020020ea05f0ea05f0ea0d50020ea0020024e50020d506daf826005f05f33d05f0d506d06d06d06d0d50ea06d06d0ea96375baf7af205f05f05f05f0d54e54e50d50ea0020020ea06d06d06d06d06d06d03dac903dac605803d03d05803d05f05805f05f05f0580d505803d03d4e50d50ea05803d03d0020ea06d05806d05804a04a2d7,l2C 127 5 0 (w920::w925::w946::v47) 0x0,l2C 127 5 0 [w920,w925,w918,w947,w933,w915] 0x0,l2C 127 6 0 (w920::w944::v61) 0xafbafa04a,l2C 127 6 0 (w920::w930::w925::w946::v48) 0xafa,l2C 127 6 0 [w920,w930,w925,w918,w947,w922,w915] 0xafb,l2C 127 7 0 (w920::w930::w944::v62) 0xafeafdafc03d04a,l2C 127 8 0 (w920::w930::w934::v62) 0x3427705f01b00200201b01b01b00204926006d06d96375bab5aff05705f05f0570d501b01b0d50ea0020020ea06406d06d06496304a75904a05f05f05f05f05f04a79105f0d504a01b0d50ea04a0020ea06d06d06d06d0582d605804a03d04a04b04a05804bacc03d5c303daae03d03d05f05f05f05f0d501b01b0d50ea03d0020ea06d06d06d06d04b2d7,l2C 127 8 0 (w920::w954::v62) 0x1940343ad01b1cc01b1cc1941941cc19401b1cc0020021e60020021e61941e61941e61cc01b1e601b01b01b0021cc1ae0493ae1941943af1941cc1ae1ae1ae1ae1cc1e61ae1ae1e604a04b04a04b19419404b19404a04b1cc04b04a1cc1e604b04a1e61ae04b1ae1ae1ae04b04a2d504a03d03d05803d03d0581940581940581cc05801b1cc1e605803d1e61ae0581ae058,l2C 127 8 0 (w955::w930::v62) 0x1930343aa01b1cb01b1cb1931931cb19301b1cb0020021e50020021e51931e51931e51cb01b1e501b01b01b0021cb1ad0493ab1931933ac1931cb1ad1ad1ad1ad1cb1e51ad1ad1e504a04b04a04b19319304b19304a04b1cb04b04a1cb1e504b04a1e51ad04b1ad1ad1ad04b04a03d2d503d03d05803d03d0581930581930581cb05801b1cb1e505803d1e51ad0581ad058,l2C 127 7 0 [w920,w925,w918,w917,w951,w933,w915] 0x4a04a3c23c33c104a01b01b01b01b96396396396301b01b01b9630492da0492da2da963963963963,l2C 127 8 0 (w920::w930::v61) 0x10e04204b04a04a04a01b1ce01b1ce01b01b1ce01b01b1ce8c48c41e88c48c41e810e1e810e1e81ce01b1e801b01b01b8c41ce1960493cf19619604b1961ce1961961961961ce1e81961961e804ab0304b04a04b04a0570573331ce04b04a04a01b1ce1e804b04a04a8c41e819604b19604b22a04a04b04a04a79104aadb04b7915c322a79167122a10e22a10e22a1ce22a01b1ce1e822a0021e819622a19622a,l2C 127 7 0 [w920,w930,w925,w918,w917,w935,w922,w915] 0x3d2d7af3aaf,l2C 127 7 0 [w920,w925,w918,w917,w951,w922,w915,w926] 0x34080049049,l2C 127 8 0 [w920,w930,w925,w918,w917,w922,w915,w926] 0x4b3b20342ac0340342ac01b33801b33801b01b2ac01b8e03378e03378e08e001b01b01b8e004924a04904924a04924a24ab063ccb0604b04a04b2ac04a04a01b04a8e024a24a04a04a75904ab05336ab5336aceab1,l2C 127 8 0 [w920,w930,w925,w918,w917,w951,w922,w915] 0x342630342630423be2632633333333b404b01b01b26301b01b3bd01b04796396396333196333101b01b01b9630492640492643bc2643bf26426404a04bb0604b26326326304ab03b063c026426404a04a96304aae19639639633b19633b3,l2C 127 7 0 [w921,w920,w930,w918,w917,w939,w915] 0x1c92470140140120120140140140120490490490490280490420490280281ca247042014,l2C 127 8 0 [w920,w930,w918,w917,w939,w922,w915] 0x14db092471ca14d1ca1ca1ca0801770140140f50140140f514d14d0f514d0140f50400f50400f596d11a96d11a14d11a14d11a04011a04011a0f501411a01401401496d0f504904910904904910914d14d10914d0491090401090401090f51093d90f511a10904911a12d049109049049af80491099f812dab612d14d12d14d12d04012d04012d0f512d0140f511a12d00211a,l2C 127 6 0 [w920,w930,w925,w940,w915,w942,w956] 0x124c896d97d3d561e33c,l2C 127 6 0 [w920,w930,w925,w957,w940,w915,w942] 0x56b88b]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB56 : Array L2Cell := #[l2C 127 7 0 [w920,w930,w925,w940,w915,w942] 0x2e04e15d02e02e02e13904e139139b0c88bb0b88b1991990471991990143d419919919919901b01b21701b01b21701b21701b21701b21701b21719921719919919921722d01b21701b01b4e501b21704e22d04e22d52e5c322d52e6d822d88b22d52e22d19922d19922d,l2C 127 7 0 (w920::w930::w925::w958::v49) 0x1628e01628e15d28e28e88b88b0433ba3bb02e0142d901401b01b28e01b01b01b2d92d901b01b4e501b52e52e52e52e,l2C 127 6 0 [w959,w920,w930,w925,w917,w940,w915] 0x12,l2C 127 7 0 [w920,w930,w925,w917,w940,w922,w915,w956] 0xb0f97f4c8b0b96d97d3d861e33c,l2C 127 6 0 (w920::w930::w925::w960::v49) 0x43,l2C 127 7 0 (w920::w930::w925::w957::w917::v49) 0x88b56bb0cb11,l2C 127 8 0 (w920::w930::w925::w917::v49) 0x1390163d6b1288bb1088b13913913913902eb0e04702e04702e13913904713913913902eb0d04702e0433d70de0142ae1391390471390de0de0de0de0470de0de04701b1ea01b1ea1391391ea13901b1ea01b1ea01b1ea04702e1ea02e01b0470de1ea0de0de0de1ea21801b1ea01b01b4e501b1ea52e5c321852e68c21813921813921888b21852e21804702e21802e52e0470de2180de218,l2C 127 7 0 [w920,w930,w925,w918,w958,w915,w942] 0x2e02e3b83b63b702e97f97f97f97f0142d801401b01b01b01b2d82d801b01b4e501b52e52e52e52e,l2C 127 8 0 [w920,w930,w925,w918,w917,w915,w942] 0x4704e04202e02e02e05705733202eb1404702e04702e04e1e904e1e997856b1e99785561e904702e1e902e02e02e978b0d0471981980471981980143d30471981980471e91981981e901b01b21601b01b21601b21601b21604702e21602e01b0471e921601b1e919821619819819821622c01b21601b01b4e501b21604e22c04e22c52e5c322c52e6d822c04702e22c02e73d0471e922c0021e919822c19822c,l2C 127 6 0 [w920,w930,w925,w961,w940,w922,w943] 0x0,l2C 127 6 0 (w920::w930::w925::w962::v49) 0x43,l2C 127 7 0 [w920,w930,w925,w918,w940,w922,w915,w943] 0x16043b17043b16014,l2C 127 6 0 [w920,w930,w925,w917,w962,w922,w963] 0x0,l2C 127 7 0 [w920,w930,w925,w918,w917,w922,w963,w943] 0x2eb1996d,l2C 127 6 0 [w920,w930,w925,w917,w961,w922,w956] 0x0,l2C 127 7 0 [w920,w930,w925,w918,w917,w961,w922,w943] 0x43b1bb16,l2C 127 6 0 [w959,w920,w930,w925,w918,w917,w915] 0x0,l2C 127 7 0 [w920,w930,w925,w918,w917,w922,w915,w956] 0xb1db1b96d97d04a61e03d,l2C 127 7 0 [w920,w930,w925,w918,w917,w962,w922,w915] 0x433ceb19b17,l2C 127 7 0 [w920,w930,w925,w918,w958,w922,w915,w943] 0x16080014014,l2C 127 8 0 [w920,w930,w925,w918,w917,w922,w915,w943] 0x473bd0162ad0160162adb203cdb2004702e0472ad02eb1f33bb1e33bb1cb1a02e02e02eb1801424b01401424b01424b24b01b33a01b33a01b01b2ad01b02e01b24b24b01b01b4e501b52e33952e33952e52e02e52e,l2C 127 8 0 (w920::w930::w925::w918::w958::v48) 0x1626101626104204726126133233202e047b2004726126126102eb14b203b904704797f97f02e02e02e97fb0e97f33197f3310142620142622622620472623b501b01b26101b01b3b201b3b426226201b01b4e501b52e52e52e3b152e3b3,l2C 127 8 0 [w921,w920,w930,w925,w918,w917,w915] 0x160dd0160dd0121190121190dd0161190160160160120dd147b092470dd1471471471470dd1191471471191c90571c91c90340f40340f40dd0f43a90dd1190f40121191470f41471471470f412c0340f40340340280340f40420420f40420340f402812c02812c0dd12c0160dd11912c01211914712c14712c04212c04212c1c90801810dd0420420420160dd119042042119,l2C 127 9 0 (w920::w930::v62) 0x57b23181b22047b21047057057047057b1504742f42f08142f42f08105708105708104742f08142f42fb1342f047064b0a177057057047057047064064064064047081064064081b0804bb0704b05705704b057b0404b04704b01b04708104b42f08106404b06406406404b058b0204bb01b00af9aef04bacfac7058ac168c05805705805705804705852e047081058002081064058064058,l2C 127 8 0 [w920,w930,w964,w918,w917,w939,w922,w915] 0x4224724714d1ca08e1770b81b11b11b11b11b11b11b11b11b11b11ed1ed1ed1ed1ed1ed1b11b11b11ed1ed1ed1ed1ed1ca1771ca14d042b0914d14d1ca1ca08e0801ca3e91b01b01b01b01b01b01b01b01b01b01b01b01ec1b01ec1ec1ec1ec1ec1ec1ec1ec1ec1ec,l2C 127 9 0 (w920::w930::w925::w964::v57) 0x5704207e08e08e08e0b808e08e08e0b808e08e08e08e08e08e08e08e08e08e08e08e08e08e0b90b90b910a0b90b90b910a0b90b90b90b90b90b908e08e08e08e08e08e0b908e0b90b90b90b90b90b90b90b90570573e8057057057057042b23057057057064b2517717705705706408005705708e08e08e08e06408e0b90b90b90b90800800800c10c10c112f0c10c10c112f0c10c10c10c10c10c108e08e08e08e0b90b90b90b90c10c10c10c10c10c10c10c10c10c10c10c10640c10c10c10c10c10c110b0c10c110b10b10b16110b10b10b16110b10b10b10b10b10b08e08e08e08e0b90b90b90b910b10b10b10b10b10b10b10b10b10b10b10b,l2C 127 8 0 (w921::w930::w934::w925::v44) 0x5f1d005f1d005f1eb05f1eb1d016e1eb16e16e16e0041d005f05f27705f1af05f1d01af1af1af1af1d01eb1af1af1eb2772af05f2772af27705f05f05f05f1d016e16e1d01eb0040041eb1af1af1af1af13803403413805f08b05f05f05f08b1d008b0af0af16e1d01eb08b0af0af0041eb1af08b1af08b0af03d3aa0af13808b0af08b0af05f2d50341d016e16e1d01eb13803403f0041eb,l2C 127 9 0 (w921::w920::w930::w925::v44) 0x5707e05707e0570a10570a107e84f0a184f84f5a084f07e05705718105715405707e15415415415407e0a11541540a118108a05718108a18105708b05708b07e08b16e07e0a108b0040a115408b15415415408b0ed5a008b5a05a05a0b2708b04208b03408b0570ed0570ed07e0ed00607e0a10ed0020a11540ed1540ed0425a00ed0285a00ed057080b2307e04201607e0a104284f01284f0a1,l2C 127 9 0 (w921::w920::w930::w925::w964::v44) 0x7e07e07e07e07e07e07e07e07e07e07e07e0a10a10a10a107e07e07e07e07e07e0a107e0a10a10a10a10a10a10a10a1057057057057057057042b2305705705705718105715405707e07e07e07e15407e0a10a10a10a118118118118108a0573e418108a1813e108b08b08b08b07e07e07e07e0a10a10a10a108b08b08b08b08b08b08b08b08b08b08b08b15408b08b08b08b08b08b0ed08b08b08b08b08b3e308b08b08b3df0ed0ed0ed0ed07e07e07e07e0a10a10a10a10ed0ed0ed0ed0ed0ed0ed0ed0ed0ed0ed0ed0ed0ed0ed3e20ed0ed0ed3de05708e04207e0b807e07e07e07e07e0b80a13e60a10a10a10a10a13e00573e5057,l2C 127 10 0 (w920::w930::w925::w964::v44) 0xb80b80b80b80b80b80b80b810a10a10a10a0b80b80b80b80b80b810a0b810a10a10a10a10a10a057b29b28b26b240570571801800570b80b80b80b81800b810a10a10a10a08a08a3e712f12f12f12f0b80b80b80b810a10a10a10a12f12f12f12f12f12f12f12f18012f12f12f12f12f12f16112f12f1611611611610b80b80b80b810a10a10a10a161161161161161161161161161161,l2C 127 7 0 [w921,w920,w930,w918,w965,w916,w915] 0x2a72a701632c0dd27b32c21124832b24832b24824824824822632a22632a22622622622625e22622622625e32925e32925e25e25e25e0472a70472a72d22a72d42d2248248,l2C 127 8 0 [w920,w930,w918,w965,w922,w916,w915] 0xd40d4328211b2b211154211064211a0c04704704721104702e0470472112112110320472112110bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0bf0f60f60f60f60f60f60f60f60f60f60f60f60f60f60f60f60f60f60f60f60bf0bf0bf0bf0f60f60f60f60f61200f60f61201201201201201201201201201201201201201201201201201201201201201200bf0bf0bf0bf]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2DataB57 : Array L2Cell := #[l2C 127 9 0 [w920,w930,w923,w918,w965,w922,w916] 0xdf1802d10df0870a40870870a40df0df0360870df0df0d40d40d40d40ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0d40ce0ce0d40d40d40d4b2c0d40d40d40d40d40d40df0d40d413a13a13a13a13a13a13a13a13a13a13a13a13a13a0ce0ce0ce0ce0d40d40d40d413a13a13a13a13a15513a13a1551551551551551551551551551551551551551551551550ce0ce0ce0ce0d40d40d40d40d40d41550d4,l2C 127 8 0 [w920,w930,w925,w918,w965,w922,w927,w943] 0x323400163413410a00a020c07120c0320320322780d72780d727827827827801407107124b24b33f33f0820821cf0ec1cf0ec1cf1cf1cf1cf1cf1cf1cf24b1cf1cf22e1cf22e12122e12122e22e22e22e22e22e,l2C 127 9 0 [w920,w930,w925,w918,w965,w922,w927] 0xc00c033ea0c032b2e0320df0df0df0df0d70d70d70d70d70d70d70d70d70d70d70d70d70d70d70d70640640640640640640df0df0df0df0df0df09a09a09a0d70d70d70d70ec0ec0ec0ec0ec0ec0ec0ec0ec0ec0ec0ec0ec0ec0d70d70d70d70ec0ec0ec0ec0640ec0ec0ec0ec0ec0ec1210ec0ec1211211211211211211211211211211211211211210d70d70d70d7121121121121121121,l2C 127 9 0 [w920,w930,w925,w923,w918,w965,w922,w966] 0xdf0362d10df0df2a60df0df0df0360df0df0df0a00a00a00a00a00a00a50a50a50cf0a50a50a50cf0a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a50a00a50a50a00a00a00c00a00a00a00c00a00a00a00a00a00df0a00a02de0272a62a60df0df0df0870870df0870870870a50a50a50a50a00a00a00a02de0a00d60d60d612e0d60d60d612e0d60d60d60d60d60d60d60d60d60d60d60d60a50a50a50a50a00a00a00a00d60d60d60d62de0d60d60d60d60d60d61040d60d61041041041561041041041561041041041041041041041041041041041040a50a50a50a50a00a00a00a00a00a01040a0104104104104104104,l2C 127 10 0 [w920,w930,w925,w923,w918,w965,w922] 0xdf036b300df0c00c00c00c00cf0cf0cf0cf0cf0cf0cf0cf0cf0cf0cf0cf0cf0cf0cf0c00cf0cf0c00c00c00c00c0b2f0c00c00df180180180b2d0df0a40a40a40cf0cf0cf0cf0c00c00c00c01800c012e12e12e12e12e12e12e12e0cf0cf0cf0cf0c00c00c00c012e12e12e12e18012e12e12e12e12e12e15612e12e1561561561561561561561560cf0cf0cf0cf0c00c00c00c00c00c01560c0156156156156156156,l2C 127 7 0 [w921,w920,w930,w918,w917,w939,w916] 0x1c92472d32d313201404001413202104002101401401402113204904004904904910f04904204913210f04010f04210f1ca2472d32d32d32d314d057042014042021,l2C 127 7 0 [w921,w920,w930,w918,w917,w939,w916,w915] 0x1c91c91ca1ca,l2C 127 8 0 [w920,w930,w918,w917,w939,w922,w916,w915] 0x1ca1cab3314db3206414d14d2d41ca3a70471ca0471ca0801ca3a71ca0f50f50f50f50f50f50f50f50f50f50f50f511a11a11a11a11a11a11a11a11a11a11a11a0f50f50f511a10910910910910910910910910910910910910910912d10912d12d12d12d12d12d12d12d12d12d12d12d,l2C 127 8 0 [w921,w920,w930,w925,w918,w917,w916,w915] 0x1c91c90dd0dd0dd0dd0dd0dd0dd0dd1191191191191191191191190dd0dd0dd119b33147b320570570dd0dd0dd147b2b1191190572d41c92d20f40f40f40f40f40f40f40f40f40f41470f4aa00f40f412c0f40f40f412c12c12c12c12c12c12c12c12c12c12c12c0471c90471c90801c92d21c90dd0dd119119,l2C 127 9 0 [w920,w930,w925,w918,w917,w922,w916,w915] 0x8008032808a057b35057154057064057047047047047047047047047047047047047047047047047047047081081081081081081081081081081081081081081081081081081081081047047047047047047081047064b34148148057057057057057057064057057057047047047047047047064b2c04708108108108108108104b04b04b04b04b04b04b04b04b04b04b04b04b04b04b04b04b04b04704704704708108108108104b04b04b04b04b06404baa104b04b04b04b04b04b05804b04b058058058058058058058058058058058058058058058058058058058058047047047047081081081081058058058058058058,l2C 127 10 0 [w920,w930,w925,w923,w918,w917,w922,w916] 0x1c81802d10870870870a40870870870a40870870870870870870870870870870b20b20b21020b20b20b21020b20b20b20b20b20b20870870870870870870b20870b20b20b20b20b20800b20b208008008008008a08a080b36080b2408008a0800800800800801c80800801c81c82a61c81c81c81801c81c81c8087087087087087087180b2d0870b20b20b20b20b20b20800800800800800801800800b70b70b71180b70b70b71180b70b70b70b70b70b70870870870870b20b20b20b20800800800800b70b70b70b70b71800b7aa20b70b70b70b70b70b71460b70b71461461461c71461461461c71461461461461461460870870870870b20b20b20b2080080080080080080146080146146146146146146,l2C 127 8 0 [w921,w920,w930,w925,w918,w917,w927,w915] 0x1c918117a17a17a17a17a17a17a17a1f31f31f31f31f31f31f31f317a17a17a1f3040247247040147b091c914714717a17a17a1471f31f30571c917b17b17b17b17b17b17b17b17b17b14717b17b17b1f217b17b17b1f21f21f21f21f21f21f21f21f21f208218109a0821c90801c94051c917a17a,l2C 127 9 0 [w920,w930,w925,w918,w917,w922,w927,w915] 0x64064340057b3818118108008008008208208209a08208208209a0820820820820820820820820820820820820820820ba0ba0ba10c0ba0ba0ba10c0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0ba0820820820820820820ba082064040071064040064b0a0640640640640640570570570800570570820820820820820820640820ba0ba0ba0ba0ba0ba0a90a90a90ee0a90a90a90ee0a90a90a90a90a90a90a90a90a90a90a90a90a90a90820820820820ba0ba0ba0ba0a90a90a90a90a90640a90a90a90a90a90a90a910d0a90a910d10d10d16210d10d10d16210d10d10d10d10d10d10d10d10d10d10d10d0820820820820ba0ba0ba0ba10d10d10d10d10d10d,l2C 127 8 0 [w920,w930,w925,w918,w917,w939,w967,w922] 0x3443ef3f217724c06824c3f108834424c0140142b20142b20402b20142b20022b10022b10402b10022b101401401400224c24c1783f01783ee04017817817801417824c0490492b00492b00402b00492b017817817804906806806804924c24c040343040068040088068088068014068002178178,l2C 127 8 0 [w920,w930,w925,w918,w917,w968,w922] 0x6808a06806808a0680680681d20680141d20401d20401d20681ee0681ee0400401ee0400021ee1d20141ee0140140140021d234306806806806806805504003d1d20550550550550140551d21ee0550551ee06806821a06804921a04021a04021a1d221a0141d21ee21a0491ee05505521a05505505504921a08806821a06806806804921a3ed0880680680680880680400681d20880681d21ee0880681ee0680883ec088,l2C 127 6 0 [w920,w934,w925,w918,w969,w939,w922] 0x0,l2C 127 7 0 [w920,w934,w925,w918,w917,w939,w970,w922] 0xb3c2f8049,l2C 127 8 0 [w920,w934,w925,w918,w917,w939,w922] 0x2602af1582602af2601581581d31585e21d315f1d305a1d31581f11581f115f0021f10020021f11d30021f10020025e20021d326015815815815815806daf82d51d306d06d06d06d5e206d1d31f106d06d1f115815815815815f527b3d15f1d35275271d31f10020021f106d06d06d06d06d06d1580881581581580880680680880680680881d30880680685e21d31f10880680680021f106d08806d0883463463ae,l2C 127 8 0 [w920,w930,w925,w918,w940,w939,w922] 0x2ae3451572ae3452ae15715715715715e62762715e15705e15715715705e02502505e02502505e18b18b3fa2ae1571571571571570de96d3fb0de0de0de0de0de0de05e0de0de05e1571571f01578c41f015e1f009f1f0a7e1f0a7e1f005e0251f0025a7e05e0de0de1f00de0de0dea7e1f021b0021f0002002002a7e1f015721b15721b15e00221b00200221b00221b00221b05e02521b02500205e0de21b0de21b,l2C 127 8 0 [w920,w930,w925,w918,w917,w971,w922] 0x253f70250253f93f50250251790255e017902d1795e017902505e3f805e02504002517902505e0250251793f502502502502502502502502501004305e1790100100100105e001017905e02502502501005e02502519a0258c419a02d19a8e019a17919a00817905e02519a0255e005e01001019a0100100105e019a1b200219a0020020025e019a0251b20251b20020021b20020021b21791b200217905e1b202505e0101b20101b2,l2C 127 8 0 [w920,w930,w925,w918,w917,w939,w971,w922] 0x3f33ef3f617724d02524d3f505e05e24d01401417901417904017901417924d24d04034204002504005e02505e02502501402524d24d1ef3f41ef05e0401ef1ef1ef0141ef1ef1ef24d04904919a04919a04019a04919a0250491ef1ef1ef0490490490020490021b20021b20401b20021b2025002,l2C 127 8 0 [w920,w930,w925,w918,w917,w972,w922] 0x2508a02502508a0250250251d10250141d10401d10401d13eb05e02502502505e0250400251d102505e0250250140251d13420250250250250250100400431d10100100100100140101d105e0253ea05e0250252190250492190402190402191d12190141d105e21902505e01001021901001001004921922f04921904904900204921902522f02522f04004022f04000222f1d122f0141d105e22f02505e01022f01022f,l2C 127 9 0 [w920,w930,w925,w918,w917,w939,w922] 0x17708a14817708a1771481480711485e207104007101407114805e14805e040b4205eb41b4005e0715e205e5e25e25e2b3f071177148148148148148064b0a0800710640640640645e206407105e06406405e14814808f1485e208f04008f04908f07108f08407105e08f5e205e06406408f0640640645e208f0885e208f5e25e2b3e5e208f148088148088040b3b088b3a68c0880710885e207105e08800205e064088064088,l2C 127 9 0 [w920,w930,w925,w918,w917,w939,w922,w927] 0x17717717717708a14840117708a17740406440206407107107107107107107107107107107107107107107107107109a07107107109a05e05e05e05e05e05e05e05e05e05e05e05e05e05e05e3fe05e05e05e40307107107107107107105e071064064064064064040064b0a06406417714814814814814806404008207107107107107107106407105e05e05e05e08f08f08f08f08f08f08f08f08f08f08f08f08f08f08f08f08f3fd08f08f08f40007107107107105e05e05e05e08f08f08f08f08f06408f08f08f08f08f08f08f08808f08f0880880880880880880880880880880880880880880883fc0880880883ff07107107107105e05e05e05e088088088088,l2C 127 10 0 [w920,w930,w925,w918,w917,w922,w927] 0x8a08a33e09a09a09a09a09a09a09a09a09a09a10c10c10c10c10c10c10c10c10c10c09a09a09a09a09a09a10c09ab44b43064b39b240641c81c81c81c809a09a09a09a09a09ab2f09a10c10c10c10c0ee0ee0ee0ee0ee0ee0ee0ee0ee0ee09a09a09a09a10c10c10c10c0ee0ee0ee0ee0eeaa50ee0ee0ee0ee0ee0ee0ee1620ee0ee16216216216216216216216216216209a09a09a09a10c10c10c10c162162162162,l2C 127 11 0 (w920::w930::w925::w923::v44) 0xa40a40a40a40a40a40a40a41021021021020a40a40a40a40a40a41020a410210210210210208a10210208a08a08a08a08ab4508a08a1c8180b371c80a40a40a40a40a40a4b310a410210210210208a08a08a08a08a08ab2a08a1181181181180a40a40a40a410210210210208a08a08a08a118118118118118aa61181181181181181181181c71181181c71c71c71c70a40a40a40a410210210210208a08a08a08a08a08a1c708a1c71c71c71c7,l2C 127 11 1 (w920::w930::w925::w923::v44) 0xb46]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
def l2Data (i : ℕ) : L2Cell :=
  let bloc := (if i < 928 then (if i < 448 then (if i < 224 then (if i < 96 then (if i < 32 then l2DataB0 else (if i < 64 then l2DataB1 else l2DataB2)) else (if i < 160 then (if i < 128 then l2DataB3 else l2DataB4) else (if i < 192 then l2DataB5 else l2DataB6))) else (if i < 320 then (if i < 256 then l2DataB7 else (if i < 288 then l2DataB8 else l2DataB9)) else (if i < 384 then (if i < 352 then l2DataB10 else l2DataB11) else (if i < 416 then l2DataB12 else l2DataB13)))) else (if i < 672 then (if i < 544 then (if i < 480 then l2DataB14 else (if i < 512 then l2DataB15 else l2DataB16)) else (if i < 608 then (if i < 576 then l2DataB17 else l2DataB18) else (if i < 640 then l2DataB19 else l2DataB20))) else (if i < 800 then (if i < 736 then (if i < 704 then l2DataB21 else l2DataB22) else (if i < 768 then l2DataB23 else l2DataB24)) else (if i < 864 then (if i < 832 then l2DataB25 else l2DataB26) else (if i < 896 then l2DataB27 else l2DataB28))))) else (if i < 1376 then (if i < 1152 then (if i < 1024 then (if i < 960 then l2DataB29 else (if i < 992 then l2DataB30 else l2DataB31)) else (if i < 1088 then (if i < 1056 then l2DataB32 else l2DataB33) else (if i < 1120 then l2DataB34 else l2DataB35))) else (if i < 1248 then (if i < 1184 then l2DataB36 else (if i < 1216 then l2DataB37 else l2DataB38)) else (if i < 1312 then (if i < 1280 then l2DataB39 else l2DataB40) else (if i < 1344 then l2DataB41 else l2DataB42)))) else (if i < 1600 then (if i < 1472 then (if i < 1408 then l2DataB43 else (if i < 1440 then l2DataB44 else l2DataB45)) else (if i < 1536 then (if i < 1504 then l2DataB46 else l2DataB47) else (if i < 1568 then l2DataB48 else l2DataB49))) else (if i < 1728 then (if i < 1664 then (if i < 1632 then l2DataB50 else l2DataB51) else (if i < 1696 then l2DataB52 else l2DataB53)) else (if i < 1792 then (if i < 1760 then l2DataB54 else l2DataB55) else (if i < 1824 then l2DataB56 else l2DataB57))))))
  bloc.getD (i % 32) default
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem lcBloc (a n k : ℕ) (g : l2Span l2Data a n) (d : l2Span l2Data (a+n) k) : l2Span l2Data a (n+k) := l2SpanAdd g d
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom0 : l2Span l2Data 0 40 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom40 : l2Span l2Data 40 49 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom89 : l2Span l2Data 89 34 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom123 : l2Span l2Data 123 48 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom171 : l2Span l2Data 171 36 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom207 : l2Span l2Data 207 46 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom253 : l2Span l2Data 253 50 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom303 : l2Span l2Data 303 49 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom352 : l2Span l2Data 352 47 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom399 : l2Span l2Data 399 34 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom433 : l2Span l2Data 433 27 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom460 : l2Span l2Data 460 47 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom507 : l2Span l2Data 507 36 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom543 : l2Span l2Data 543 32 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom575 : l2Span l2Data 575 55 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom630 : l2Span l2Data 630 43 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom673 : l2Span l2Data 673 33 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom706 : l2Span l2Data 706 25 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom731 : l2Span l2Data 731 39 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom770 : l2Span l2Data 770 47 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom817 : l2Span l2Data 817 45 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom862 : l2Span l2Data 862 49 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom911 : l2Span l2Data 911 29 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom940 : l2Span l2Data 940 31 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom971 : l2Span l2Data 971 20 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom991 : l2Span l2Data 991 18 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1009 : l2Span l2Data 1009 22 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1031 : l2Span l2Data 1031 21 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1052 : l2Span l2Data 1052 33 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1085 : l2Span l2Data 1085 25 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1110 : l2Span l2Data 1110 24 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1134 : l2Span l2Data 1134 25 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1159 : l2Span l2Data 1159 31 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1190 : l2Span l2Data 1190 20 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1210 : l2Span l2Data 1210 16 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1226 : l2Span l2Data 1226 28 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1254 : l2Span l2Data 1254 34 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1288 : l2Span l2Data 1288 27 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1315 : l2Span l2Data 1315 21 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1336 : l2Span l2Data 1336 22 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1358 : l2Span l2Data 1358 35 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1393 : l2Span l2Data 1393 16 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1409 : l2Span l2Data 1409 20 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1429 : l2Span l2Data 1429 41 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1470 : l2Span l2Data 1470 39 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1509 : l2Span l2Data 1509 20 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1529 : l2Span l2Data 1529 34 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1563 : l2Span l2Data 1563 33 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1596 : l2Span l2Data 1596 20 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1616 : l2Span l2Data 1616 52 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1668 : l2Span l2Data 1668 15 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1683 : l2Span l2Data 1683 21 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1704 : l2Span l2Data 1704 57 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1761 : l2Span l2Data 1761 27 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1788 : l2Span l2Data 1788 27 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1815 : l2Span l2Data 1815 8 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1823 : l2Span l2Data 1823 10 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1833 : l2Span l2Data 1833 10 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem spanFrom1843 : l2Span l2Data 1843 8 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2All : l2Span l2Data 0 1851 := (lcBloc 0 1085 766 (lcBloc 0 575 510 (lcBloc 0 303 272 (lcBloc 0 123 180 (lcBloc 0 40 83 spanFrom0 (lcBloc 40 49 34 spanFrom40 spanFrom89)) (lcBloc 123 84 96 (lcBloc 123 48 36 spanFrom123 spanFrom171) (lcBloc 207 46 50 spanFrom207 spanFrom253))) (lcBloc 303 130 142 (lcBloc 303 49 81 spanFrom303 (lcBloc 352 47 34 spanFrom352 spanFrom399)) (lcBloc 433 74 68 (lcBloc 433 27 47 spanFrom433 spanFrom460) (lcBloc 507 36 32 spanFrom507 spanFrom543)))) (lcBloc 575 287 223 (lcBloc 575 131 156 (lcBloc 575 55 76 spanFrom575 (lcBloc 630 43 33 spanFrom630 spanFrom673)) (lcBloc 706 64 92 (lcBloc 706 25 39 spanFrom706 spanFrom731) (lcBloc 770 47 45 spanFrom770 spanFrom817))) (lcBloc 862 129 94 (lcBloc 862 78 51 (lcBloc 862 49 29 spanFrom862 spanFrom911) (lcBloc 940 31 20 spanFrom940 spanFrom971)) (lcBloc 991 40 54 (lcBloc 991 18 22 spanFrom991 spanFrom1009) (lcBloc 1031 21 33 spanFrom1031 spanFrom1052))))) (lcBloc 1085 385 381 (lcBloc 1085 169 216 (lcBloc 1085 74 95 (lcBloc 1085 25 49 spanFrom1085 (lcBloc 1110 24 25 spanFrom1110 spanFrom1134)) (lcBloc 1159 51 44 (lcBloc 1159 31 20 spanFrom1159 spanFrom1190) (lcBloc 1210 16 28 spanFrom1210 spanFrom1226))) (lcBloc 1254 104 112 (lcBloc 1254 61 43 (lcBloc 1254 34 27 spanFrom1254 spanFrom1288) (lcBloc 1315 21 22 spanFrom1315 spanFrom1336)) (lcBloc 1358 51 61 (lcBloc 1358 35 16 spanFrom1358 spanFrom1393) (lcBloc 1409 20 41 spanFrom1409 spanFrom1429)))) (lcBloc 1470 213 168 (lcBloc 1470 93 120 (lcBloc 1470 39 54 spanFrom1470 (lcBloc 1509 20 34 spanFrom1509 spanFrom1529)) (lcBloc 1563 53 67 (lcBloc 1563 33 20 spanFrom1563 spanFrom1596) (lcBloc 1616 52 15 spanFrom1616 spanFrom1668))) (lcBloc 1683 132 36 (lcBloc 1683 78 54 (lcBloc 1683 21 57 spanFrom1683 spanFrom1704) (lcBloc 1761 27 27 spanFrom1761 spanFrom1788)) (lcBloc 1815 18 18 (lcBloc 1815 8 10 spanFrom1815 spanFrom1823) (lcBloc 1833 10 8 spanFrom1833 spanFrom1843))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R5 (ih : l2IH 5) : Wide 208 (lb 5-1) (basis 5) := by
  have h := l2Global l2All 0 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R15 (ih : l2IH 15) : Wide 208 (lb 15-1) (basis 15) := by
  have h := l2Global l2All 1 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R19 (ih : l2IH 19) : Wide 208 (lb 19-1) (basis 19) := by
  have h := l2Global l2All 2 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R21 (ih : l2IH 21) : Wide 208 (lb 21-1) (basis 21) := by
  have h := l2Global l2All 3 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R23 (ih : l2IH 23) : Wide 208 (lb 23-1) (basis 23) := by
  have h := l2Global l2All 4 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R27 (ih : l2IH 27) : Wide 208 (lb 27-1) (basis 27) := by
  have h := l2Global l2All 5 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R31 (ih : l2IH 31) : Wide 208 (lb 31-1) (basis 31) := by
  have h := l2Global l2All 12 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R51 (ih : l2IH 51) : Wide 208 (lb 51-1) (basis 51) := by
  have h := l2Global l2All 13 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R55 (ih : l2IH 55) : Wide 208 (lb 55-1) (basis 55) := by
  have h := l2Global l2All 14 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R63 (ih : l2IH 63) : Wide 208 (lb 63-1) (basis 63) := by
  have h := l2Global l2All 43 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R83 (ih : l2IH 83) : Wide 208 (lb 83-1) (basis 83) := by
  have h := l2Global l2All 44 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R85 (ih : l2IH 85) : Wide 208 (lb 85-1) (basis 85) := by
  have h := l2Global l2All 64 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R87 (ih : l2IH 87) : Wide 208 (lb 87-1) (basis 87) := by
  have h := l2Global l2All 65 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R91 (ih : l2IH 91) : Wide 208 (lb 91-1) (basis 91) := by
  have h := l2Global l2All 69 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R95 (ih : l2IH 95) : Wide 208 (lb 95-1) (basis 95) := by
  have h := l2Global l2All 542 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R103 (ih : l2IH 103) : Wide 208 (lb 103-1) (basis 103) := by
  have h := l2Global l2All 544 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R111 (ih : l2IH 111) : Wide 208 (lb 111-1) (basis 111) := by
  have h := l2Global l2All 1430 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R115 (ih : l2IH 115) : Wide 208 (lb 115-1) (basis 115) := by
  have h := l2Global l2All 1431 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R119 (ih : l2IH 119) : Wide 208 (lb 119-1) (basis 119) := by
  have h := l2Global l2All 1673 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2R123 (ih : l2IH 123) : Wide 208 (lb 123-1) (basis 123) := by
  have h := l2Global l2All 1682 (by decide)
  exact h ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem l2rep (s : Fin 127) (hs : s.val ∈ repsIso) (ih : l2IH s.val) : Wide 208 (lb s.val-1) (basis s.val) := by
  simp only [repsIso,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq <;> rw [eq] at ih ⊢
  · exact l2R5 ih
  · exact l2R15 ih
  · exact l2R19 ih
  · exact l2R21 ih
  · exact l2R23 ih
  · exact l2R27 ih
  · exact l2R31 ih
  · exact l2R51 ih
  · exact l2R55 ih
  · exact l2R63 ih
  · exact l2R83 ih
  · exact l2R85 ih
  · exact l2R87 ih
  · exact l2R91 ih
  · exact l2R95 ih
  · exact l2R103 ih
  · exact l2R111 ih
  · exact l2R115 ih
  · exact l2R119 ih
  · exact l2R123 ih
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem petits (s : Fin 127) (h : 0 < lb s.val) : Wide 208 (lb s.val - 1) (basis s.val) := petitsParIso l2rep s h
set_option maxRecDepth 40000 in
set_option maxHeartbeats 50000000 in
theorem racine (H : ∀ t : Fin 127, 0 < lb t.val → Wide 208 (lb t.val-1) (basis t.val)) : Ban 208 11 (basis 127) := by
  have w := l2Global l2All 1850 (by decide)
  have cert : Wide 208 11 (basis 127) := w (fun t _ hp => H t hp)
  intro k lim run
  exact cert ⟨k,_,lim,run,fun x hx => List.mem_toFinset.mp hx⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def posBits : ℕ := 0xc183060c183060c183060c183060a142850a142850a142850a1428508912244891224489122448912244850a142850a142850a142850a14283060c183060c183060c183060c150a142850a142850a142850a1428448912244891224489122448912242850a142850a142850a142850a12850a142850a142850a142850a1424489122448912244891224489122244891224489122448912244891142850a142850a142850a142850a0a142850a142850a142850a14285
def negBits : ℕ := 0x9101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c122030406080809101824406080c12203040608080
def sample (bank : ℕ) (i : Fin 208) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := basis 127
def seeds : List Wire := inputs.map (fun a => (false,a))
set_option maxHeartbeats 1000000 in
theorem listed : ∀ i : Fin 208, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (208+i.val))=List.ofFn (sample negBits i) := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem labels : ∀ i : Fin 208, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem essential : ∀ a∈inputs, ∃ i : Fin 208, ∀ b∈inputs, b.testBit i.val≠b.testBit (208+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 208 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 208 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 208 out.2 := by
    intro i hi same
    let j : Fin 208 := ⟨i,hi⟩
    have diff : read i out=read (208+i) out := by simp [read,same]
    have p := ev i;have n := ev (208+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩


end Seven

namespace Bin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 8 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 8) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 8) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 8) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 8) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e


def Prog (s : Set F) (f : F) (k : Nat) : Prop :=
  match k with
  | 0 => Av s f
  | n + 1 => ∃ (a b : F) (t : Bool), Av s a ∧ Av s b ∧
      Prog (insert (comb t a b) s) f n

theorem Prog.done {s f} (h : Av s f) : Prog s f 0 := h

theorem Prog.gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
    (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k+1) :=
  ⟨a,b,t,ha,hb,tail⟩

theorem Prog.byLength {M : ∀ s f k, Prog s f k → Prop}
    (done : ∀ {s f} (h : Av s f), M s f 0 (.done h))
    (gate : ∀ {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k),
      M _ _ _ tail → M s f (k+1) (.gate t ha hb tail))
    {s f k} (p : Prog s f k) : M s f k p := by
  induction k generalizing s with
  | zero => exact done p
  | succ k ih =>
    obtain ⟨a,b,t,ha,hb,tail⟩ := p
    exact gate t ha hb tail (ih tail)

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p using Prog.byLength with
  | done h => exact fun t hs => ⟨0, le_rfl, .done (av_rs hs h), fun _ h' => smp_av h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, .gate tag pa pb q, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 8} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 8} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p using Prog.byLength with
  | done h => exact absurd (li_smp (li_av hs h)) (hf true)
  | @gate s f a b k tag ha hb tail ih =>
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, .gate tag (av_rs ht ha) (av_rs ht hb) q⟩

def stock : Set F := Set.range fun (i : Fin 8) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

def rd (w : List F) (i : ℕ) : F := fun x => (w.map fun f => f x).getD i false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => rd w i x)

theorem rd_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (i : ℕ) : Av s (rd w i) := by
  by_cases h : i < w.length
  · have e : rd w i = w[i] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, Nat.le_of_not_lt h]⟩

theorem gv_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av s (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av s a ∧ Av s b ∧ gv w g = comb t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · left
    exact Or.inl ⟨op.eval [], by funext x; simp [gv]⟩
  · left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.or, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.not, [i]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · left
      rw [show gv w ⟨.not, [i, j]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem toProg (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w : List F) (s : Set F), (∀ u ∈ w, Av s u) →
    ∃ k ≤ (gs.filter fun g => !isNot g).length,
      Prog s (rd (gs.foldl (fun w g => w ++ [gv w g]) w) o) k := by
  induction gs with
  | nil => exact fun w s hw => ⟨0, le_rfl, .done (rd_av hw o)⟩
  | cons g gs ih =>
    intro w s hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    have hlen : (gs.filter fun g => !isNot g).length ≤
        ((g :: gs).filter fun g => !isNot g).length := by
      rw [List.filter_cons]
      split <;> simp
    rcases gv_av hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) s (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      exact ⟨k, hk.trans hlen, p⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) (insert (comb t a b) s) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_ins _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_mem (Set.mem_insert _ _))
      refine ⟨k + 1, ?_, .gate t ha hb p⟩
      have : isNot g = false := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      simp [this]
      simpa using hk

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl (fun w g => w ++ [gv w g]) w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_not_not {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 8) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 8) (x : X) => x i)) o = f := by
    funext x
    rw [← he x, rd, fold_eval, List.map_ofFn]
    rfl
  rw [e] at p
  have h := hl k p
  have hle := List.length_filter_le (fun g => !isNot g) gs
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.length_filter_eq_length_iff]
    omega
  intro g hm
  have h2 := hall g hm
  refine ⟨?_, (hg g hm).2⟩
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2


end Bin

namespace Reify
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Bin
abbrev Y := Fin 7 → Bool
abbrev F7 := Y → Bool
def liftInput (j : Fin 8) : Fin 7 := ![0,1,0,2,3,6,4,5] j
def pull (u : F) : F7 := fun x => u (x ∘ liftInput)
def neg (u : F7) : F7 := fun x => !(u x)
def paired (w : List F7) (u : F7) : Prop := u ∈ w ∧ neg u ∈ w
def stockOk (w : List F7) (s : Set F) : Prop :=
  (∀ b : Bool, (fun _ : Y => b) ∈ w) ∧ (∀ u ∈ s, paired w (pull u))
def charged (g : Gate) : Bool := match g.op with | .not => false | _ => true
def legal (g : Gate) : Prop := g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2
def tick (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
theorem avail {s w f} (env : stockOk w s) (h : Av s f) : pull f ∈ w := by
  rcases h with ⟨b,rfl⟩ | ⟨u,hu,rfl | rfl⟩
  · exact env.1 b
  · exact (env.2 _ hu).1
  · exact (env.2 _ hu).2

theorem locate {w : List F7} {u : F7} (h : u ∈ w) :
    ∃ i : Nat, ∀ x : Y, (w.map (fun f => f x)).getD i false = u x := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  refine ⟨i,?_⟩
  intro x
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,eq]

/-- Keep both polarities of every synthesized wire. Negations do not consume a binary gate. -/
theorem realize {s f k} (program : Prog s f k) (w : List F7) (env : stockOk w s) :
    ∃ (gs : List Gate) (o : Nat), (∀ g ∈ gs, legal g) ∧ gs.countP charged ≤ k ∧
      ∀ x : Y, (gs.foldl tick (w.map (fun u => u x))).getD o false = pull f x := by
  induction program using Prog.byLength generalizing w with
  | done h =>
    obtain ⟨o,ho⟩ := locate (avail env h)
    exact ⟨[],o,by simp,by simp,ho⟩
  | @gate s f a b k t ha hb tail ih =>
    obtain ⟨i,hi⟩ := locate (avail env ha)
    obtain ⟨j,hj⟩ := locate (avail env hb)
    let g : Gate := ⟨if t then .and else .or, [i,j]⟩
    let inv : Gate := ⟨.not,[w.length]⟩
    let u := pull (comb t a b)
    let w' := w ++ [u,neg u]
    have ext : stockOk w' (insert (comb t a b) s) := by
      constructor
      · intro v
        exact List.mem_append_left _ (env.1 v)
      · intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl|m
        · exact ⟨by simp [w',u],by simp [w',u]⟩
        · exact ⟨List.mem_append_left _ (env.2 _ m).1,List.mem_append_left _ (env.2 _ m).2⟩
    obtain ⟨gs,o,hs,hk,he⟩ := ih w' ext
    refine ⟨g::inv::gs,o,?_,?_,?_⟩
    · intro gate h
      rcases List.mem_cons.mp h with rfl | h
      · cases t <;> simp [legal,g]
      · rcases List.mem_cons.mp h with rfl|m
        · simp [legal,inv]
        · exact hs _ m
    · cases t <;> simpa [g,inv,charged,List.countP_cons] using hk
    · intro x
      have hg : tick (w.map (fun h => h x)) g = w.map (fun h => h x) ++ [u x] := by
        have h₁ := hi x
        have h₂ := hj x
        simp [pull] at h₁ h₂
        cases t <;> simp [g,tick,GateOp.eval,u,comb,pull,h₁,h₂]
      have hw : tick (w.map (fun h => h x) ++ [u x]) inv = w'.map (fun h => h x) := by
        simp [tick,inv,w',neg,GateOp.eval,List.getD_append_right, List.append_assoc]
      simpa only [List.foldl_cons,hg,hw] using he x

def seedW : List F7 := List.ofFn (fun i : Fin 7 => fun x : Y => x i) ++
  List.ofFn (fun i : Fin 7 => fun x : Y => !(x i)) ++ [fun _ => true,fun _ => false]
def seedG : List Gate := [⟨.not,[0]⟩,⟨.not,[1]⟩,⟨.not,[2]⟩,⟨.not,[3]⟩,⟨.not,[4]⟩,
  ⟨.not,[5]⟩,⟨.not,[6]⟩,⟨.not,[]⟩,⟨.not,[14]⟩]
theorem seed_env : stockOk seedW stock := by
  constructor
  · intro b; cases b <;> simp [seedW]
  · rintro u ⟨i,rfl⟩
    constructor
    · apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_ofFn.mpr ⟨liftInput i,rfl⟩
    · apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_ofFn.mpr ⟨liftInput i,rfl⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem run {f k} (p : Prog stock f k) :
    ∃ c : Circuit, FanInTwo c ∧ c.gates.countP charged ≤ k ∧
      ∀ x : Y, c.eval (List.ofFn x) = pull f x := by
  obtain ⟨gs,o,hl,hk,he⟩ := realize p seedW seed_env
  refine ⟨⟨seedG++gs,o⟩,?_,?_,?_⟩
  · intro g h
    rcases List.mem_append.mp h with h|h
    · simp only [seedG,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    · exact hl g h
  · change (seedG++gs).countP charged ≤ k
    simpa [List.countP_append,seedG,charged] using hk
  · intro x
    have seed : ∀ y : Y, seedG.foldl tick (List.ofFn y) = seedW.map (fun u => u y) := by decide
    change ((seedG++gs).foldl tick (List.ofFn x)).getD o false = _
    rw [List.foldl_append,seed]
    exact he x
end Reify

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def graph8 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)
def mon : List Gate := [⟨.or,[3,5]⟩, ⟨.or,[4,5]⟩, ⟨.or,[0,6]⟩, ⟨.or,[1,7]⟩, ⟨.or,[6,7]⟩, ⟨.or,[1,2]⟩, ⟨.or,[0,13]⟩, ⟨.and,[8,10]⟩, ⟨.and,[9,11]⟩, ⟨.and,[3,5]⟩, ⟨.and,[12,14]⟩, ⟨.or,[15,16]⟩, ⟨.or,[17,19]⟩, ⟨.or,[18,20]⟩]
set_option maxRecDepth 8192 in
theorem graphSpec : ∀ x : Fin 8 → Bool, graph8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 8192 in
theorem monoEval : ∀ x : Fin 8 → Bool, (⟨mon,21⟩ : Circuit).eval (List.ofFn x) = graph8 x := by decide +kernel
theorem monoOps : ∀ g ∈ mon, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mon,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem restricted_lower : Bin.Low 12 (Bin.rs 2 false graph8) := by
  intro k program
  obtain ⟨c,basis,cost,he⟩ := Reify.run program
  have graph_eq : ∀ x : Reify.Y, Reify.pull (Bin.rs 2 false graph8) x = Seven.graph x := by
    decide +kernel
  have same : circuitFun 7 c = Seven.graph := by
    funext x
    exact (he x).trans (graph_eq x)
  obtain ⟨j,steps,live⟩ := Seven.trace c basis same
  change c.gates.countP Seven.counted ≤ k at cost
  by_contra! small
  exact (Seven.racine Seven.petits) j (by omega) live

set_option maxRecDepth 20000 in
theorem binary_lower : Bin.Low 13 graph8 :=
  Bin.one 2 false (Bin.good_at 64 9 0 (by decide +kernel)) restricted_lower

end PEqualNP.Outside.L_meta_31335
open PEqualNP.Outside.L_meta_31335 in
theorem PEqualNP.Outside.L_meta_31335 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ he
  by_cases large : 14 ≤ gs.length
  · exact ⟨mon,21,monoOps, (show mon.length = 14 by rfl) ▸ large,
      fun x => (monoEval x).trans (graphSpec x)⟩
  · exact ⟨gs,o,Bin.all_not_not binary_lower gs o legal (by omega)
      (fun x => (he x).trans (graphSpec x).symm),le_rfl,he⟩

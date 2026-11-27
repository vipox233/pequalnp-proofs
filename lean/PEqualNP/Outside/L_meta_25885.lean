import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25885
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {X : Type}
abbrev Signal (X : Type) := X → Bool
abbrev Tape (X : Type) := List (Signal X)
def Good (g : Gate) := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
def atWire (T : Tape X) (i : Nat) : Signal X := T.getD i (fun _ => false)
def signal (T : Tape X) (g : Gate) : Signal X :=
  fun x => g.op.eval (g.inputs.map fun i => atWire T i x)
-- A tape records each wire as a Boolean function of the original input.
inductive Chain : Tape X → List Gate → Tape X → Prop where
  | nil (T) : Chain T [] T
  | cons {T gs M} (g : Gate) (good : Good g) (reads : ∀ i∈g.inputs, i<T.length)
      (tail : Chain (T++[signal T g]) gs M) : Chain T (g::gs) M

theorem Chain.trans {T M V : Tape X} {a b} (h : Chain T a M) (h' : Chain M b V) :
    Chain T (a++b) V := by
  induction h with
  | nil => exact h'
  | cons g good r _ ih => exact .cons g good r (ih h')

theorem Chain.sub {T M : Tape X} {gs} (h : Chain T gs M) : T ⊆ M := by
  induction h with
  | nil => exact fun _ h => h
  | cons g good r _ ih => exact fun _ hx => ih (List.mem_append_left _ hx)

theorem Chain.len {T M : Tape X} {gs} (h : Chain T gs M) : M.length=T.length+gs.length := by
  induction h with
  | nil => simp
  | cons _ _ _ _ ih => simp_all; omega

theorem Chain.good {T M : Tape X} {gs} (h : Chain T gs M) : ∀g∈gs,Good g := by
  induction h with
  | nil => simp
  | cons g ok _ _ ih => simpa using And.intro ok ih

theorem Chain.reads {T M : Tape X} {gs} (h : Chain T gs M) (out : Nat) :
    ReadsBack T.length ⟨gs,out⟩ := by
  induction h with
  | nil => intro j hj; simp at hj
  | cons g ok r tail ih =>
    intro j hj u hu
    cases j with
    | zero => exact r u (by simpa [gateAt] using hu)
    | succ j =>
      have z := ih j (by simpa using hj) u (by simpa [gateAt] using hu)
      simp only [List.length_append,List.length_cons,List.length_nil] at z
      omega

theorem get_signal (T : Tape X) (i : Nat) (x : X) :
    (T.map (fun f => f x)).getD i false = atWire T i x := by
  simp [atWire,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases T[i]? <;> rfl

theorem Chain.eval {T M : Tape X} {gs} (h : Chain T gs M) (x : X) :
    gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (T.map fun f => f x) = M.map fun f => f x := by
  induction h with
  | nil => rfl
  | cons g _ _ _ ih =>
    simpa only [List.foldl_cons,List.map_append,List.map_cons,List.map_nil,signal,get_signal] using ih

def Build (T : Tape X) (b : Nat) (P : Tape X → Prop) :=
  ∃ gs M, Chain T gs M ∧ gs.length ≤ b ∧ P M

theorem done {T : Tape X} {P : Tape X → Prop} (h : P T) : Build T 0 P :=
  ⟨[],T,.nil T,by simp,h⟩

theorem Build.bind {T : Tape X} {a b P Q} (h : Build T a P)
    (next : ∀ M : Tape X, T ⊆ M → P M → Build M b Q) : Build T (a+b) Q := by
  obtain ⟨gs,M,c,len,pt⟩ := h
  obtain ⟨gs',V,c',len',q⟩ := next M c.sub pt
  exact ⟨gs++gs',V,c.trans c',by simp; omega,q⟩

theorem Build.weak {T : Tape X} {a b P Q} (h : Build T a P) (ab : a≤b)
    (imp : ∀ M : Tape X, P M → Q M) : Build T b Q := by
  obtain ⟨gs,M,c,len,p⟩ := h
  exact ⟨gs,M,c,len.trans ab,imp M p⟩

theorem emit (T : Tape X) (g : Gate) (ok : Good g) (r : ∀i∈g.inputs,i<T.length) :
    Build T 1 (fun M => signal T g∈M) :=
  ⟨[g],_,.cons g ok r (.nil _),by simp,by simp⟩

abbrev Has (f : Signal X) (M : Tape X) := f∈M
theorem wire {f : Signal X} {T : Tape X} (h : f∈T) : ∃ i:Fin T.length, atWire T i=f := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  exact ⟨⟨i,hi⟩,by simpa [atWire,List.getD_eq_getElem?_getD,hi] using eq⟩

theorem bin (T : Tape X) {a b : Signal X} (ha : a∈T) (hb : b∈T)
    (o : GateOp) (ho : o=.and ∨ o=.or) :
    Build T 1 (Has (fun x => o.eval [a x,b x])) := by
  obtain ⟨i,ei⟩ := wire ha
  obtain ⟨j,ej⟩ := wire hb
  let g : Gate := ⟨o,[i,j]⟩
  have r (u) (hu : u∈g.inputs) : u<T.length := by
    change u∈[i.val,j.val] at hu
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl <;> exact Fin.isLt _
  have z := emit T g ⟨by simp [g],ho.imp_right Or.inl⟩ r
  have eq : signal T g = (fun x => o.eval [a x,b x]) := by funext x; simp [g,signal,ei,ej]
  rw [eq] at z
  exact z

theorem inv (T : Tape X) {a : Signal X} (ha : a∈T) :
    Build T 1 (Has (fun x => !(a x))) := by
  obtain ⟨i,ei⟩ := wire ha
  let g : Gate := ⟨.not,[i]⟩
  have r (u) (hu : u∈g.inputs) : u<T.length := by
    have := show u=i.val by simpa [g] using hu
    omega
  have z := emit T g ⟨by simp [g],Or.inr (Or.inr ⟨rfl,rfl⟩)⟩ r
  have eq : signal T g = (fun x => !(a x)) := by funext x; simp [g,signal,ei,GateOp.eval]
  rw [eq] at z
  exact z

theorem genAnd (T : Tape X) {a b : Signal X} (ha : a∈T) (hb : b∈T) :
    Build T 1 (Has (fun x => a x && b x)) := by
  simpa [GateOp.eval] using bin T ha hb .and (Or.inl rfl)
theorem genOr (T : Tape X) {a b : Signal X} (ha : a∈T) (hb : b∈T) :
    Build T 1 (Has (fun x => a x || b x)) := by
  simpa [GateOp.eval] using bin T ha hb .or (Or.inr rfl)

theorem consts (T : Tape X) : Build T 2 (fun M => (fun _ => false)∈M ∧ (fun _ => true)∈M) := by
  let l : Gate := ⟨.or,[]⟩
  let h : Gate := ⟨.and,[]⟩
  have left := emit T l (by simp [Good,l]) (by simp [l])
  apply left.bind (b:=1)
  intro M _ hl
  obtain ⟨gs,U,c,le,hu⟩ := emit M h (by simp [Good,h]) (by simp [h])
  exact ⟨gs,U,c,le,c.sub hl,hu⟩

theorem many {T : Tape X} (n c : ℕ) (f : Fin n → Signal X)
    (each : ∀ M : Tape X, T ⊆ M → ∀ i, Build M c (Has (f i))) :
    Build T (n*c) (fun M => ∀ i, f i∈M) := by
  induction n with
  | zero =>
    rw [Nat.zero_mul]
    exact done (P:=fun M => ∀ i, f i∈M) (fun i => i.elim0)
  | succ n ih =>
    rw [Nat.succ_mul]
    apply (ih (fun i => f i.castSucc) (fun M sub i => each M sub i.castSucc)).bind (b:=c)
    intro M sub hh
    obtain ⟨gs,U,ch,le,w⟩ := each M sub (Fin.last n)
    exact ⟨gs,U,ch,le,Fin.lastCases w (fun i => ch.sub (hh i))⟩

variable {X : Type}
abbrev F := ZMod 2
def enc (f : X → F) : Signal X := fun x => decide (f x = 1)
def bit (b : Bool) : F := if b then 1 else 0
theorem encode_bit (b : X → Bool) : enc (fun x => bit (b x)) = b := by
  funext x; cases h : b x <;> simp [enc,bit,h]
theorem bit_enc (u : F) : bit (decide (u=1)) = u := by revert u; decide
theorem mul_enc (a b : X → F) : enc (fun x => a x*b x) = fun x => enc a x && enc b x := by
  have h : ∀ u v : F, decide (u*v=1) = (decide (u=1) && decide (v=1)) := by decide
  funext x; exact h _ _
theorem mulG (T : Tape X) {a b : X → F} (ha : enc a∈T) (hb : enc b∈T) :
    Build T 1 (Has (enc (fun x => a x*b x))) := by rw [mul_enc]; exact genAnd T ha hb

theorem addG (T : Tape X) {a b : X → F} (ha : enc a∈T) (hb : enc b∈T) :
    Build T 4 (Has (enc (fun x => a x+b x))) := by
  have h : ∀ u v : F, decide (u+v=1) =
    ((decide (u=1) || decide (v=1)) && !(decide (u=1) && decide (v=1))) := by decide
  have e : enc (fun x => a x+b x) = fun x =>
      (enc a x || enc b x) && !(enc a x && enc b x) := by funext x; exact h _ _
  rw [e]
  apply (genOr T ha hb).bind (b:=3)
  intro M sub hor
  apply (genAnd M (sub ha) (sub hb)).bind (b:=2)
  intro U s hand
  apply (inv U hand).bind (b:=1)
  intro V t hn
  exact genAnd V (t (s hor)) hn

theorem sumG (T : Tape X) (n : Nat) (pos : 0<n) (f : Fin n → X → F)
    (live : ∀ i,enc (f i)∈T) : Build T (4*(n-1)) (Has (enc (fun x => ∑ i, f i x))) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simpa using (done (P:=Has (enc (f 0))) (live 0))
    | succ n =>
      have prev := ih (by omega) (fun i => f i.castSucc) (fun i => live i.castSucc)
      have h := prev.bind (b:=4) (Q:=Has (enc (fun x => (∑ i : Fin (n+1), f i.castSucc x) + f (Fin.last (n+1)) x))) (by
        intro M sub old
        exact addG M old (sub (live _)))
      apply h.weak (by omega)
      intro M hm
      simpa only [Fin.sum_univ_castSucc] using hm

theorem mux (T : Tape X) {b y n : Signal X} (hb : b∈T) (hy : y∈T) (hn : n∈T) :
    Build T 4 (Has (fun x => if b x then y x else n x)) := by
  apply (inv T hb).bind (b:=3)
  intro M s neg
  apply (genAnd M (s hb) (s hy)).bind (b:=2)
  intro U t high
  apply (genAnd U (t neg) (t (s hn))).bind (b:=1)
  intro V r low
  have h := genOr V (r high) low
  have eq : (fun x => (b x && y x) || (!b x && n x)) = fun x => if b x then y x else n x := by
    funext x; cases b x <;> simp
  rw [← eq]
  exact h

theorem lookupG (T : Tape X) (t : Nat) (a : X → Fin t → Bool) (f : (Fin t → Bool) → Bool)
    (lo : (fun _ => false)∈T) (hi : (fun _ => true)∈T) (av : ∀ i, (fun x => a x i)∈T) :
    Build T (4*(2^t-1)) (Has (fun x => f (a x))) := by
  induction t generalizing T with
  | zero =>
    have same (x : X) : a x = Fin.elim0 := Subsingleton.elim _ _
    simp_rw [same]
    cases v : f Fin.elim0
    · exact done lo
    · exact done hi
  | succ t ih =>
    let tail := fun x (i : Fin t) => a x i.succ
    let cut := fun b (w : Fin t → Bool) => f (Fin.cases b w)
    have h := ih T tail (cut true) lo hi (fun i => av i.succ)
    have z := h.bind (b:=4*(2^t-1)+4) (Q:=Has (fun x => f (a x))) (by
      intro M s yes
      apply (ih M tail (cut false) (s lo) (s hi) (fun i => s (av i.succ))).bind (b:=4)
      intro U r no
      have result := mux U (r (s (av 0))) (r yes) no
      have eq : (fun x => if a x 0 then cut true (tail x) else cut false (tail x)) = fun x => f (a x) := by
        funext x
        have w : Fin.cases (a x 0) (tail x) = a x := by funext i;exact Fin.cases rfl (fun _ => rfl) i
        cases b : a x 0 <;> simp [cut,← b,w]
      rw [← eq]
      exact result)
    apply z.weak _ (fun _ h => h)
    rw [pow_succ]
    have : 0<2^t := Nat.two_pow_pos _
    omega
variable {K : Type} [Field K] [Algebra F K] {s k : ℕ}
abbrev Coord (K : Type) [Field K] [Algebra F K] (s : Nat) := K ≃ₗ[F] (Fin s → F)
def basis (c : Coord K s) (i : Fin s) : K := c.symm (fun j => if j=i then 1 else 0)
theorem decompose (c : Coord K s) (y : K) : ∑ i, c y i • basis c i = y := by
  apply c.injective
  ext j
  simp [basis,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_ite]

theorem prod_form (c : Coord K s) (u v : K) (i : Fin s) :
    c (u*v) i = ∑ j, c u j * c (basis c j*v) i := by
  conv_lhs => rw [← decompose c u]
  simp [Finset.sum_mul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem matrix_form (c : Coord K s) (x : Fin s → F) (j i : Fin s) :
    c (basis c j * c.symm x) i = ∑ l, x l * c (basis c j*basis c l) i := by
  rw [mul_comm,prod_form]
  simp_rw [c.apply_symm_apply,mul_comm (basis c _) (basis c j)]

def coeff (r : Fin k → Bool) (h : Nat) (i : Fin s) : F :=
  if u : h*s+i.val<k then bit (r ⟨_,u⟩) else 0
def block (c : Coord K s) (r : Fin k → Bool) (h : Nat) : K := c.symm (coeff r h)
def horner (c : Coord K s) (r : Fin k → Bool) (x : K) (h : Nat) : Nat → K
  | 0 => block c r h
  | d+1 => block c r h + horner c r x (h+1) d * x

theorem horner_sum (c : Coord K s) (r : Fin k → Bool) (x : K) (h d : Nat) :
    horner c r x h d = ∑ b ∈ Finset.range (d+1), block c r (h+b)*x^b := by
  induction d generalizing h with
  | zero => simp [horner]
  | succ d ih =>
    rw [horner,ih,Finset.sum_mul,Finset.sum_range_succ' (f:=fun b => block c r (h+b)*x^b)]
    simp only [Nat.add_zero,pow_zero,mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [pow_succ,mul_assoc]
    congr 2
    omega

def extended (c : Coord K s) (r : Fin k → Bool) (x : K) (hs : 0<s) (j : Nat) : K :=
  if z : j<k then (if r ⟨j,z⟩ then basis c ⟨j%s,Nat.mod_lt _ hs⟩ * x^(j/s) else 0) else 0

theorem block_sum (c : Coord K s) (r : Fin k → Bool) (x : K) (hs : 0<s) (b : Nat) :
    block c r b*x^b = ∑ z ∈ Finset.range s, extended c r x hs (b*s+z) := by
  rw [← decompose c (block c r b),Finset.sum_mul,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro z _
  have div : (b*s+z.val)/s=b := by rw [Nat.mul_comm b s,Nat.mul_add_div hs,Nat.div_eq_of_lt z.isLt,Nat.add_zero]
  have modEq : (b*s+z.val)%s=z.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt z.isLt]
  have idx : (⟨(b*s+z.val)%s,Nat.mod_lt _ hs⟩ : Fin s)=z := Fin.ext modEq
  simp only [block,LinearEquiv.apply_symm_apply,coeff,extended,div,idx]
  split <;> rename_i h
  · cases hr : r ⟨b*s+z.val,h⟩ <;> simp [bit]
  · simp

theorem horner_result (c : Coord K s) (r : Fin k → Bool) (x : K) (hk : 0<k) (hs : 0<s) :
    horner c r x 0 ((k-1)/s) =
      ∑ j : Fin k, if r j then basis c ⟨j.val % s,Nat.mod_lt _ hs⟩*x^(j.val/s) else 0 := by
  let q := (k-1)/s
  have blocks (h : ℕ) : (∑ b ∈ Finset.range h, block c r b*x^b) =
      ∑ j ∈ Finset.range (h*s), extended c r x hs j := by
    induction h with
    | zero => simp
    | succ h ih =>
      rw [Finset.sum_range_succ,ih,Nat.succ_mul,Finset.sum_range_add,block_sum c r x hs h]
  rw [horner_sum]
  simp only [Nat.zero_add]
  rw [blocks]
  have le : k≤(q+1)*s := by
    have h₁ := Nat.mod_add_div (k-1) s
    have h₂ := Nat.mod_lt (k-1) hs
    dsimp [q]; rw [Nat.add_mul,one_mul,Nat.mul_comm ((k-1)/s) s]; omega
  have small : (∑ j ∈ Finset.range k, extended c r x hs j) =
      ∑ j ∈ Finset.range ((q+1)*s), extended c r x hs j := by
    apply Finset.sum_subset (Finset.range_mono le)
    intro i _ hi
    simp only [Finset.mem_range] at hi
    simp [extended,hi]
  change (∑ j ∈ Finset.range ((q+1)*s), _) = _
  rw [← small,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [extended,i.isLt]
variable {K : Type} [Field K] [Algebra F K] {k s t : Nat}
structure Input (k s t : Nat) where
  row : Fin k → Bool
  xb : Fin s → Bool
  index : Fin t → Bool

def pointX (c : Coord K s) (z : Input k s t) := c.symm (fun i => bit (z.xb i))
def entry (c : Coord K s) (j i : Fin s) (z : Input k s t) := c (basis c j*pointX c z) i
def coeffSig (c : Coord K s) (h : Nat) (i : Fin s) (z : Input k s t) := c (block c z.row h) i
def stage (c : Coord K s) (h d : Nat) (i : Fin s) (z : Input k s t) :=
  c (horner c z.row (pointX c z) h d) i

def Rows (T : Tape (Input k s t)) := ∀ j, (fun z : Input k s t => z.row j)∈T
def XBits (T : Tape (Input k s t)) := ∀ j, (fun z : Input k s t => z.xb j)∈T
def Indices (T : Tape (Input k s t)) := ∀ j, (fun z : Input k s t => z.index j)∈T
def Zero (T : Tape (Input k s t)) := (fun _ => false)∈T
def Matrix (c : Coord K s) (T : Tape (Input k s t)) := ∀ j i, enc (entry c j i)∈T
def Coords (c : Coord K s) (h d : Nat) (T : Tape (Input k s t)) := ∀ i, enc (stage c h d i)∈T

theorem coeff_mem (c : Coord K s) (T : Tape (Input k s t)) (h i) (rz : Rows T) (lo : Zero T) :
    enc (coeffSig c h i)∈T := by
  by_cases n : h*s+i.val<k
  · have e : enc (@coeffSig _ _ _ k s t c h i) = fun z => z.row ⟨_,n⟩ := by
      funext z
      simp only [coeffSig,block,LinearEquiv.apply_symm_apply,enc,coeff,dite_eq_left n]
      cases z.row ⟨_,n⟩ <;> decide
    rw [e]; exact rz _
  · have e : enc (@coeffSig _ _ _ k s t c h i) = fun _ => false := by
      funext z; simp [enc,coeffSig,block,coeff,n]
    rw [e]; exact lo

-- The matrix depends on the point alone, so all Horner steps can read its entries.
theorem matrixG (c : Coord K s) (T : Tape (Input k s t)) (hs : 0<s) (lo : Zero T) (xb : XBits T) :
    Build T ((s*s)*(4*(s-1))) (Matrix c) := by
  let pair := (@finProdFinEquiv s s).symm
  let f := fun n : Fin (s*s) => enc (@entry _ _ _ k s t c (pair n).1 (pair n).2)
  have one (M : Tape (Input k s t)) (sub : T⊆M) (n : Fin (s*s)) : Build M (4*(s-1)) (Has (f n)) := by
    let j := (pair n).1
    let i := (pair n).2
    let part := fun l : Fin s => fun z : Input k s t => bit (z.xb l) * c (basis c j*basis c l) i
    have live (l) : enc (part l)∈M := by
      have dich : ∀ q:F, q=0 ∨ q=1 := by decide
      rcases dich (c (basis c j*basis c l) i) with e|e
      · have eq : enc (part l) = fun _ => false := by funext x;simp [part,enc,e]
        rw [eq];exact sub lo
      · have eq : enc (part l) = fun z => z.xb l := by
          simpa only [part,e,mul_one] using encode_bit (fun z : Input k s t => z.xb l)
        rw [eq];exact sub (xb l)
    have eq : f n = enc (fun z => ∑ l,part l z) := by
      funext z; unfold f enc entry pointX; rw [matrix_form]
    rw [eq]
    exact sumG M s hs part live
  obtain ⟨gs,M,ch,le,h⟩ := many (T:=T) (s*s) _ f one
  refine ⟨gs,M,ch,le,?_⟩
  intro j i
  simpa only [f,pair,Equiv.symm_apply_apply] using h (finProdFinEquiv (j,i))

theorem dotG {X : Type} (T : Tape X) (n : Nat) (hn : 0<n) (f g : Fin n → X → F)
    (a : ∀j,enc (f j)∈T) (b : ∀j,enc (g j)∈T) :
    Build T (n+4*(n-1)) (Has (enc (fun x => ∑ j, f j x*g j x))) := by
  let p := fun j => enc (fun x => f j x*g j x)
  have all := many (T:=T) n 1 p (fun M sub i => mulG M (sub (a i)) (sub (b i)))
  rw [Nat.mul_one] at all
  apply all.bind
  intro M _ h
  exact sumG M n hn _ h

theorem hornerG (c : Coord K s) (T : Tape (Input k s t)) (hs : 0<s)
    (lo : Zero T) (row : Rows T) (mat : Matrix c T) (h d : Nat) :
    Build T (8*s^2*d) (Coords c h d) := by
  induction d generalizing T h with
  | zero =>
    rw [Nat.mul_zero]
    exact done (P:=Coords c h 0) (fun i => coeff_mem c T h i row lo)
  | succ d ih =>
    rw [Nat.mul_succ]
    apply (ih T lo row mat (h+1)).bind
    intro M sub old
    have each (U : Tape (Input k s t)) (sm : M⊆U) (i : Fin s) :
        Build U (s+4*(s-1)+4) (Has (enc (stage c h (d+1) i))) := by
      have prod := dotG U s hs (stage c (h+1) d) (fun j => entry c j i)
        (fun j => sm (old j)) (fun j => sm (sub (mat j i)))
      apply prod.bind (b:=4)
      intro V sv ph
      have e : stage c h (d+1) i = fun x : Input k s t =>
          coeffSig c h i x + ∑ j,stage c (h+1) d j x * entry c j i x := by
        funext x
        simp only [stage,horner,map_add,Pi.add_apply,coeffSig,entry]
        rw [prod_form]
      rw [e]
      exact addG V (sv (sm (sub (coeff_mem c T h i row lo)))) ph
    have ret := many (T:=M) s _ (fun i => enc (stage c h (d+1) i)) each
    apply ret.weak _ (fun _ h => h)
    have e : s+4*(s-1)+4 ≤ 8*s := by omega
    exact (Nat.mul_le_mul_left s e).trans (by rw [pow_two]; nlinarith)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {K : Type} [Field K] [Algebra F K] {k s t : Nat}
def initial (k s t : Nat) : Tape (Input k s t) :=
  (List.ofFn fun i => fun z : Input k s t => z.row i) ++
  (List.ofFn fun i => fun z : Input k s t => z.xb i) ++
  (List.ofFn fun i => fun z : Input k s t => z.index i)
theorem initial_len : (initial k s t).length=k+s+t := by simp [initial,Nat.add_assoc]
theorem initial_rows : Rows (initial k s t) := by
  intro j
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
theorem initial_bits : XBits (initial k s t) := by
  intro j
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
theorem initial_idx : Indices (initial k s t) := by
  intro j;exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
theorem initial_eval (z : Input k s t) :
    (initial k s t).map (fun f => f z) = List.ofFn z.row ++ List.ofFn z.xb ++ List.ofFn z.index := by
  simp [initial,List.map_ofFn,Function.comp_def]

def result (c : Coord K s) (label : (Fin t → Bool) → Fin s → F) (z : Input k s t) : F :=
  ∑ i, label z.index i * stage c 0 ((k-1)/s) i z

theorem build_all (c : Coord K s) (label : (Fin t → Bool) → Fin s → F) (hs : 0<s) :
    Build (initial k s t)
      (2+((s*s)*(4*(s-1))+(8*s^2*((k-1)/s)+(s*(4*(2^t-1))+(s+4*(s-1))))))
      (Has (enc (result c label))) := by
  apply (consts (initial k s t)).bind
  intro A a const
  apply (matrixG c A hs const.1 (fun j => a (initial_bits j))).bind
  intro M m mat
  apply (hornerG c M hs (m const.1) (fun j => m (a (initial_rows j))) mat 0 ((k-1)/s)).bind
  intro H h vec
  let f := fun i : Fin s => enc (fun z : Input k s t => label z.index i)
  have bank := many (T:=H) s (4*(2^t-1)) f (by
    intro V v i
    exact lookupG V t Input.index (fun a => decide (label a i=1))
      (v (h (m const.1))) (v (h (m const.2))) (fun j => v (h (m (a (initial_idx j))))))
  apply bank.bind
  intro L l table
  exact dotG L s hs (fun i z => label z.index i) (stage c 0 ((k-1)/s))
    table (fun j => l (vec j))

theorem budget (k s t : Nat) :
    2+((s*s)*(4*(s-1))+(8*s^2*((k-1)/s)+(s*(4*(2^t-1))+(s+4*(s-1))))) ≤
    4*((s+2)*2^t+s^2*(s-1)+2*s^2*((k-1)/s)+2*s)+t+2 := by
  have a := Nat.mul_le_mul_left (4*s) (Nat.sub_le (2^t) 1)
  have b := Nat.sub_le s 1
  nlinarith only [a,b,Nat.zero_le t,Nat.zero_le s,Nat.zero_le (2^t)]

theorem assembled (c : Coord K s) (label : (Fin t → Bool) → Fin s → F) (hs : 0<s) :
    ∃ C : Circuit, ReadsBack (k+s+t) C ∧ C.output<k+s+t+C.size ∧
    C.size≤4*((s+2)*2^t+s^2*(s-1)+2*s^2*((k-1)/s)+2*s)+t+2 ∧
    (∀ g∈C.gates, Good g) ∧ ∀ z : Input k s t,
      C.eval (List.ofFn z.row ++ List.ofFn z.xb ++ List.ofFn z.index) = enc (result c label) z := by
  obtain ⟨gs,U,ch,hc,out⟩ := build_all (k:=k) c label hs
  obtain ⟨i,eq⟩ := wire out
  let C : Circuit := ⟨gs,i.val⟩
  refine ⟨C,?_,?_,hc.trans (budget k s t),ch.good,?_⟩
  · simpa [initial_len,C] using ch.reads i.val
  · change i.val < k+s+t+gs.length
    simpa [ch.len,initial_len] using i.isLt
  · intro z
    have hh := ch.eval z
    rw [initial_eval] at hh
    change (C.wires _).getD i.val false = _
    change C.wires _ = _ at hh
    rw [hh,get_signal,eq]
end PEqualNP.Outside.L_meta_25885

open PEqualNP.Outside.L_meta_25885

theorem PEqualNP.Outside.L_meta_25885 : ∀ k s t : ℕ, 0 < k → 0 < s →
  let F := ZMod 2
  let K := GaloisField 2 s
  let W := Fin s → F
  ∀ (coord : K ≃ₗ[F] W) (label : (Fin t → Bool) → W),
    let basisBit := fun j : Fin k => coord.symm
      (fun z : Fin s => if z.val = j.val % s then (1 : F) else 0)
    let B := (s+2)*2^t+s^2*(s-1)+2*s^2*((k-1)/s)+2*s
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+s+t) C ∧
      C.output < k+s+t+C.size ∧ C.size ≤ 4*B+t+2 ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      ∀ (row : Fin k → Bool) (xb : Fin s → Bool) (index : Fin t → Bool),
        let x := coord.symm (fun i => if xb i then (1 : F) else 0)
        let v := ∑ j : Fin k, if row j then basisBit j * x^(j.val/s) else (0 : K)
        C.eval (List.ofFn row ++ List.ofFn xb ++ List.ofFn index) =
          decide ((∑ i : Fin s, label index i * coord v i) = 1) := by
  intro k s t hk hs
  dsimp only
  intro coord label
  obtain ⟨C,reads,output,size,legal,ev⟩ := assembled (k:=k) coord label hs
  refine ⟨C,reads,output,size,legal,?_⟩
  intro row xb index
  let z : Input k s t := ⟨row,xb,index⟩
  have h := ev z
  change C.eval (List.ofFn row ++ List.ofFn xb ++ List.ofFn index) = _ at h
  rw [h]
  simp only [enc,result,stage,z,pointX,horner_result coord row _ hk hs]
  simp [basis,bit,Fin.ext_iff]

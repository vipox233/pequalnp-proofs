import PEqualNP.Defs


namespace PEqualNP.Outside.L_clb_059_aux
abbrev Q (w : Nat) := Fin (2^w)
abbrev I (n w : Nat) := n*2^(w+1)
def edgeCode (w : Nat) (s : Q w) (b : Bool) := s.val + b.toNat * 2^w
lemma edgeLt (w : Nat) (s : Q w) (b : Bool) : edgeCode w s b < 2^(w+1) := by
  have := s.isLt; cases b <;> simp [edgeCode,Nat.pow_succ] <;> omega
def next (w : Nat) (s : Q w) (b : Bool) : Q w :=
  ⟨edgeCode w s b / 2,by have := edgeLt w s b;rw [Nat.pow_succ] at this;omega⟩
def addr {n} (w : Nat) (i : Fin n) (s : Q w) (b : Bool) : Fin (I n w) :=
  ⟨i.val*2^(w+1)+edgeCode w s b,by
    have h := Nat.mul_le_mul_right (2^(w+1)) (show i.val+1≤n from i.isLt)
    rw [Nat.add_mul,Nat.one_mul] at h
    have := edgeLt w s b;unfold I;omega⟩

def edge59 {n w} (i : Fin n) (s t : Q w) (x : Fin (I n w) → Bool) : Bool :=
  if next w s false = t then
    if next w s true = t then x (addr w i s false) || x (addr w i s true)
    else x (addr w i s false)
  else if next w s true = t then x (addr w i s true) else false

theorem edge59_iff {n w} (i : Fin n) (s t : Q w) (x : Fin (I n w) → Bool) :
    edge59 i s t x = true ↔ ∃ b, next w s b=t ∧ x (addr w i s b)=true := by
  rw [Bool.exists_bool]
  by_cases q : next w s false=t <;> by_cases r : next w s true=t <;> simp [edge59,q,r]

def tableInput59 {n w} (table : Fin n → (Fin (w+1) → Bool) → Bool) (j : Fin (I n w)) : Bool :=
  table ⟨j.val / 2^(w+1), (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr j.isLt⟩
    (fun k => (j.val % 2^(w+1)).testBit k.val)

theorem getInput59 {n w} (table : Fin n → (Fin (w+1) → Bool) → Bool) (i : Fin n)
    (p : Nat) (hp : p<2^(w+1)) (haddr : i.val*2^(w+1)+p < I n w) :
    tableInput59 table ⟨i.val*2^(w+1)+p,haddr⟩ = table i (fun j=>p.testBit j.val) := by
  simp [tableInput59, Nat.mul_comm i.val, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hp, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

theorem inputList59 {n w} (table : Fin n → (Fin (w+1) → Bool) → Bool) :
    List.ofFn (tableInput59 table) = (List.ofFn (fun i : Fin n => List.ofFn (fun p : Fin (2 ^ (w+1)) =>
        table i (fun j => p.val.testBit j.val)))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext p
  exact getInput59 table i p.val p.isLt _

def args59 {n w} (i : Fin n) (s t : Q w) : List (Fin (I n w)) :=
  (if next w s false = t then [addr w i s false] else []) ++
  (if next w s true = t then [addr w i s true] else [])

theorem args59_length {n w} (i : Fin n) (s t : Q w) : (args59 i s t).length ≤ 2 := by
  by_cases q : next w s false=t <;> by_cases r : next w s true=t <;> simp [args59,q,r]

theorem args59_any {n w} (i : Fin n) (s t : Q w) (x : Fin (I n w) → Bool) :
    (args59 i s t).any x = edge59 i s t x := by
  by_cases q : next w s false=t <;> by_cases r : next w s true=t <;> simp [args59,edge59,q,r]

end PEqualNP.Outside.L_clb_059_aux


namespace PEqualNP.Outside.L_clb_059_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  mono : Monotone2 ⟨gates,0⟩
  back : ReadsBack n ⟨gates,0⟩

namespace Bank
variable {n : Nat}

def val (B : Bank n) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).getD i false

def dep (B : Bank n) (i : Nat) : Nat := (⟨B.gates,i⟩ : Circuit).depth n

def Has (B : Bank n) (d : Nat) (f : BitFn n) : Prop :=
  ∃ i < n + B.gates.length, B.dep i ≤ d ∧ ∀ x, B.val i x = f x

def Ext (B D : Bank n) : Prop := ∀ {d f}, B.Has d f → D.Has d f

def Grow (B : Bank n) (cost : Nat) (p : Bank n → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ p D

def empty (n : Nat) : Bank n := ⟨[],by simp [Monotone2],by simp [ReadsBack]⟩

lemma input (i : Fin n) : (empty n).Has 0 (fun x => x i) := by
  refine ⟨i,i.isLt,?_,?_⟩
  · simp [dep,empty,Circuit.depth,Circuit.depths,List.getD_eq_getElem?_getD,i.isLt]
  · intro x
    simp [val,empty,Circuit.wires,List.getD_eq_getElem?_getD,i.isLt]

lemma Has.raise {B : Bank n} {a b f} (h : B.Has a f) (le : a≤b) : B.Has b f := by
  obtain ⟨i,h,d,e⟩:=h
  exact ⟨i,h,d.trans le,e⟩

lemma Grow.pure (B : Bank n) {p : Bank n → Prop} (h : p B) : B.Grow 0 p :=
  ⟨B,fun h => h,by omega,h⟩

lemma Grow.weaken {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (hab : a ≤ b) (hpq : ∀ D, p D → q D) : B.Grow b q := by
  obtain ⟨D,e,c,t⟩ := h
  exact ⟨D,e,by omega,hpq D t⟩

lemma Grow.bind {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (f : ∀ D, B.Ext D → p D → D.Grow b q) : B.Grow (a+b) q := by
  obtain ⟨D,e,c,t⟩ := h
  obtain ⟨E,e',c',t'⟩ := f D e t
  exact ⟨E,fun h => e' (e h),by omega,t'⟩

private lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires,List.foldl_append] at ih ⊢
    omega

private lemma depthLen (gs : List Gate) (n : Nat) :
    ((⟨gs,0⟩ : Circuit).depths n).length = n+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.depths]
  | append_singleton gs g ih =>
    simp [Circuit.depths,List.foldl_append] at ih ⊢
    omega

private lemma gate (B : Bank n) (g : Gate) (d : Nat)
    (ok : g.op ∈ ({GateOp.and, .or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n+B.gates.length)
    (bound : (g.inputs.map B.dep).foldr max 0 ≤ d) :
    B.Grow 1 (fun D => D.Has (d+1) (fun x => g.op.eval (g.inputs.map fun i => B.val i x))) := by
  let D : Bank n :=
    { gates := B.gates ++ [g]
      mono := by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h|h
        · exact B.mono g' h
        · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
      back := by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw }
  have hv (x : Fin n → Bool) :
      ((⟨D.gates,0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D,val,Circuit.wires,List.foldl_append]
  have hd : ((⟨D.gates,0⟩ : Circuit).depths n) =
      ((⟨B.gates,0⟩ : Circuit).depths n) ++ [(g.inputs.map B.dep).foldr max 0+1] := by
    simp [D,Circuit.depths,List.foldl_append]
    rfl
  have hl (x : Fin n → Bool) :
      ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).length = n+B.gates.length := by
    simp [wireLen]
  have dh := depthLen B.gates n
  have depthAt (C : Bank n) (i : Nat) : C.dep i = ((⟨C.gates,0⟩ : Circuit).depths n).getD i 0 := rfl
  refine ⟨D,?_,by simp [D],n+B.gates.length,by simp [D],?_,?_⟩
  · intro dz f hf
    obtain ⟨i,hi,dd,he⟩ := hf
    refine ⟨i,by simp [D]; omega,?_,?_⟩
    · rwa [depthAt,hd,List.getD_append _ _ _ _ (by omega)]
    · intro x
      unfold val
      rw [hv,List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
      exact he x
  · rw [depthAt,hd,←dh]
    simpa [List.getD_eq_getElem?_getD] using Nat.succ_le_succ bound
  · intro x
    unfold val
    rw [hv,← hl x]
    simp [val,List.getD_eq_getElem?_getD]

lemma const (B : Bank n) (b : Bool) : B.Grow 1 (fun D => D.Has 1 (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using B.gate ⟨.or,[]⟩ 0 (by simp) (by simp) (by simp)
  | true => simpa [GateOp.eval] using B.gate ⟨.and,[]⟩ 0 (by simp) (by simp) (by simp)

lemma meet {B : Bank n} {d} {f g : BitFn n} (a : B.Has d f) (b : B.Has d g) :
    B.Grow 1 (fun D => D.Has (d+1) (fun x => f x && g x)) := by
  obtain ⟨i,hi,di,he⟩ := a
  obtain ⟨j,hj,dj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.and,[i,j]⟩ d (by simp) (by simp [hi,hj]) (by simp [di,dj])

lemma join {B : Bank n} {d} {f g : BitFn n} (a : B.Has d f) (b : B.Has d g) :
    B.Grow 1 (fun D => D.Has (d+1) (fun x => f x || g x)) := by
  obtain ⟨i,hi,di,he⟩ := a
  obtain ⟨j,hj,dj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.or,[i,j]⟩ d (by simp) (by simp [hi,hj]) (by simp [di,dj])

lemma inputsOr (B : Bank n) (e : (empty n).Ext B) (l : List (Fin n)) (hl : l.length≤2) :
    B.Grow 1 (fun D=>D.Has 1 (fun x=>l.any x)) := by
  cases l with
  | nil => simpa using B.const false
  | cons i t =>
    cases t with
    | nil =>
      have h := (e (input i)).raise (by decide : 0≤1)
      simpa using (Grow.pure B h).weaken (by decide : 0≤1) (fun _ ok => ok)
    | cons j tail =>
      have z : tail=[] := by apply List.length_eq_zero_iff.mp; simpa using hl
      subst tail
      simpa using join (e (input i)) (e (input j))

lemma collectList {α : Type} (B : Bank n) (l : List α) (cost : Nat) (P : α → Bank n → Prop)
    (mono : ∀ {B D : Bank n}, B.Ext D → ∀ i,P i B → P i D)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (P i)) :
    B.Grow (l.length*cost) (fun D => ∀ i ∈ l, P i D) := by
  induction l with
  | nil => simpa using (Grow.pure B (p:=fun D => ∀ i ∈ ([] : List α), P i D) (by simp))
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost) (q:=fun E => ∀ i ∈ a::l, P i E) (by
      intro D e haveL
      obtain ⟨E,e',c',ha⟩ := emit D e a (by simp)
      refine ⟨E,e',c',?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact mono e' i (haveL i h))
    simpa [Nat.succ_mul] using out

lemma collectFin (B : Bank n) (m cost : Nat) (P : Fin m → Bank n → Prop)
    (mono : ∀ {B D : Bank n}, B.Ext D → ∀ i,P i B → P i D)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (P i)) :
    B.Grow (m*cost) (fun D => ∀ i, P i D) := by
  simpa using B.collectList (List.finRange m) cost P mono (fun D e i _ => emit D e i)

lemma finish {f : BitFn n} {b d : Nat} (h : (empty n).Grow b (fun B => B.Has d f)) :
    ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.output < n+C.size ∧ C.size ≤ b ∧
      C.depth n ≤ d ∧ ∀ bits, C.eval (List.ofFn bits) = f bits := by
  obtain ⟨B,_,budget,i,hi,hd,he⟩ := h
  exact ⟨⟨B.gates,i⟩, B.mono, B.back, hi, by simpa [Circuit.size,empty] using budget, hd, he⟩

end Bank
end PEqualNP.Outside.L_clb_059_aux


namespace PEqualNP.Outside.L_clb_059_aux

theorem leavesBank59 (n w : Nat) : (Bank.empty (I n w)).Grow (n*4^w)
    (fun B => ∀ i : Fin n, ∀ s t : Q w, B.Has 1 (edge59 i s t)) := by
  classical
  let A := Fin n × (Q w × Q w)
  let l := (Finset.univ : Finset A).toList
  let D := Bank.empty (I n w)
  let P (v : A) (B : Bank (I n w)) := B.Has 1 (edge59 v.1 v.2.1 v.2.2)
  have mono {U V : Bank (I n w)} (ext : U.Ext V) (i : A) : P i U → P i V := fun h => ext h
  have emit (B : Bank (I n w)) (hb : D.Ext B) (i : A) (_ : i∈l) : B.Grow 1 (P i) := by
    have a := Bank.inputsOr B hb (args59 i.1 i.2.1 i.2.2) (args59_length ..)
    exact a.weaken (le_refl 1) (fun U h => by simpa only [P,args59_any] using h)
  have count : l.length*1=n*4^w := by
    simp only [l,A,Q,Finset.length_toList,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,mul_one]
    rw [←mul_pow]
    norm_num
  have hh := D.collectList l 1 P mono emit
  refine hh.weaken count.le (fun B h i s t => ?_)
  exact h ⟨i,s,t⟩ (by simp [l])

end PEqualNP.Outside.L_clb_059_aux

namespace PEqualNP.Outside.L_clb_059_aux

def Path59 {α : Type} (E : Nat → α → α → Prop) (off len : Nat) (u v : α) : Prop :=
  ∃ f : Nat → α, f 0 = u ∧ f len = v ∧ ∀ j < len, E (off+j) (f j) (f (j+1))

theorem pathFin59 {α : Type} (E : Nat → α → α → Prop) (off len : Nat) (u v : α) :
    Path59 E off len u v ↔ ∃ f : Fin (len+1)→α,
      f 0 = u ∧ f (Fin.last len) = v ∧
      ∀ j : Fin len, E (off+j.val) (f j.castSucc) (f j.succ) := by
  constructor
  · rintro ⟨f,first,last,step⟩
    exact ⟨fun j => f j.val,first,last,fun j => step j.val j.isLt⟩
  · rintro ⟨f,first,last,step⟩
    let atJ (j : Nat) : Fin (len+1) := ⟨min j len,by omega⟩
    have a0 : atJ 0 = 0 := Fin.ext (by simp [atJ])
    have aL : atJ len = Fin.last len := Fin.ext (by simp [atJ])
    refine ⟨fun j => f (atJ j), by simpa only [a0] using first,
      by simpa only [aL] using last,?_⟩
    intro j hj
    let i : Fin len := ⟨j,hj⟩
    have h₁ : atJ j=i.castSucc := Fin.ext (Nat.min_eq_left (by omega))
    have h₂ : atJ (j+1)=i.succ := Fin.ext (Nat.min_eq_left (by omega))
    change E (off+j) (f (atJ j)) (f (atJ (j+1)))
    rw [h₁,h₂]
    exact step i

theorem pathOne59 {α : Type} (E : Nat → α → α → Prop) (off : Nat) (u v : α) :
    Path59 E off 1 u v ↔ E off u v := by
  constructor
  · rintro ⟨f,hu,hv,h⟩
    simpa [hu,hv] using h 0 (by decide)
  · intro h
    refine ⟨fun i => if i=0 then u else v,by simp,by simp,?_⟩
    intro j hj
    obtain rfl : j=0 := by omega
    simpa using h

theorem pathAdd59 {α : Type} (E : Nat → α → α → Prop) (off a b : Nat) (u v : α) :
    Path59 E off (a+b) u v ↔ ∃ z, Path59 E off a u z ∧ Path59 E (off+a) b z v := by
  constructor
  · rintro ⟨f,hu,hv,h⟩
    refine ⟨f a,⟨f,hu,rfl,fun j hj => h j (by omega)⟩,
      fun j => f (a+j),by simp,hv,?_⟩
    intro j hj
    simpa [Nat.add_assoc] using h (a+j) (by omega)
  · rintro ⟨z,⟨p,hp,pe,hs⟩,⟨q,hq,qe,ht⟩⟩
    let f (j : Nat) := if j<a then p j else q (j-a)
    have left (j : Nat) (hj : j≤a) : f j=p j := by
      by_cases small : j<a
      · simp [f,small]
      · obtain rfl : j=a := by omega
        simp [f,pe,hq]
    have right (j : Nat) (hj : a≤j) : f j=q (j-a) := by simp [f,Nat.not_lt.mpr hj]
    refine ⟨f,(left 0 (by omega)).trans hp,?_,?_⟩
    · rw [right _ (by omega),Nat.add_sub_cancel_left,qe]
    · intro j hj
      by_cases low : j<a
      · rw [left _ (by omega),left _ (by omega)]
        exact hs j low
      · rw [right _ (by omega),right _ (by omega)]
        have h := ht (j-a) (by omega)
        rwa [show off+a+(j-a)=off+j by omega,show j-a+1=j+1-a by omega] at h

end PEqualNP.Outside.L_clb_059_aux

namespace PEqualNP.Outside.L_clb_059_aux

theorem balancedRange59 (P : Nat → Nat → Nat → Prop)
    (one : ∀ h off, P h off 1)
    (fork : ∀ h off a b, 0<a → 0<b →
      P h off a → P h (off+a) b → P (h+1) off (a+b))
    (h off n : Nat) (pos : 0<n) (lim : n≤2^h) : P h off n := by
  induction h generalizing off n with
  | zero =>
    simp only [pow_zero] at lim
    obtain rfl : n=1 := by omega
    exact one 0 off
  | succ h ih =>
    by_cases eqOne : n=1
    · subst n
      exact one _ _
    · rw [pow_succ] at lim
      let a := n/2
      let b := n-a
      have ha : 0<a := by dsimp [a]; omega
      have hb : 0<b := by dsimp [a,b]; omega
      have ca : a≤2^h := by dsimp [a];omega
      have cb : b≤2^h := by dsimp [a,b];omega
      have sum : a+b=n := by dsimp [a,b]; omega
      exact sum ▸ fork h off a b ha hb (ih off a ha ca) (ih (off+a) b hb cb)

end PEqualNP.Outside.L_clb_059_aux

namespace PEqualNP.Outside.L_clb_059_aux

abbrev Mat59 (I w : Nat) := Fin (2^w) → Fin (2^w) → BitFn I
def HasMat {I w} (B : Bank I) (d : Nat) (A : Mat59 I w) : Prop := ∀ i j, B.Has d (A i j)
def mul59 {I w} (A C : Mat59 I w) : Mat59 I w :=
  fun i j x => decide (∃t, A i t x=true ∧ C t j x=true)
def any59 {I w} (f : Fin (2^w) → BitFn I) : BitFn I := fun x=>decide (∃i, f i x=true)

private def left59 {w} (i : Fin (2^w)) : Fin (2^(w+1)) :=
  ⟨i.val,by rw [pow_succ]; omega⟩
private def right59 {w} (i : Fin (2^w)) : Fin (2^(w+1)) :=
  ⟨2^w+i.val,by rw [pow_succ]; omega⟩

private lemma anySplit59 {w I} (f : Fin (2^(w+1)) → BitFn I) :
    (fun x=>any59 (fun i=>f (left59 i)) x || any59 (fun i=>f (right59 i)) x) = any59 f := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,any59,decide_eq_true_eq]
  constructor
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · exact ⟨_,hi⟩
    · exact ⟨_,hi⟩
  · rintro ⟨i,hi⟩
    by_cases h : i.val < 2^w
    · left
      exact ⟨⟨i.val,h⟩,hi⟩
    · right
      have hi' : i.val<2^w*2 := lt_of_lt_of_eq i.isLt (pow_succ 2 w)
      let j : Fin (2^w) := ⟨i.val-2^w,by omega⟩
      have e : right59 j=i := by apply Fin.ext; change 2^w+(i.val-2^w)=i.val; omega
      exact ⟨j,e ▸ hi⟩

lemma balancedOr59 {I w d} (B : Bank I) (f : Fin (2^w) → BitFn I)
    (hf : ∀ i, B.Has d (f i)) : B.Grow (2^w-1) (fun E=>E.Has (d+w) (any59 f)) := by
  induction w generalizing B with
  | zero =>
    have he : any59 f = f ⟨0,by decide⟩ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [any59,decide_eq_true_eq]
      constructor
      · rintro ⟨i,hi⟩
        have e : i=⟨0,by decide⟩ := by apply Fin.ext; have := i.isLt; simp at this; omega
        exact e ▸ hi
      · intro h; exact ⟨_,h⟩
    simpa [he] using Bank.Grow.pure B (p:=fun D=>D.Has d (f ⟨0,by decide⟩)) (hf _)
  | succ w ih =>
    have out := (ih B (fun i=>f (left59 i)) (fun i=>hf _)).bind
      (b:=2^w-1+1) (q:=fun E=>E.Has (d+w+1) (any59 f)) (by
        intro D ext left
        apply (ih D (fun i=>f (right59 i)) (fun i=>ext (hf _))).bind
        intro E ext' right
        simpa only [anySplit59] using Bank.join (ext' left) right)
    have pos : 0 < 2^w := by positivity
    exact out.weaken (by rw [pow_succ]; omega) (fun E h=>by simpa [Nat.add_assoc] using h)

private lemma dot59 {I w d} (B : Bank I) (u v : Fin (2^w) → BitFn I)
    (hu : ∀i,B.Has d (u i)) (hv : ∀i,B.Has d (v i)) :
    B.Grow (2*2^w) (fun E=>E.Has (d+(w+1))
      (fun x=>decide (∃i,u i x=true ∧ v i x=true))) := by
  let ps (i : Fin (2^w)) : BitFn I := fun x=>u i x && v i x
  have all := B.collectFin (2^w) 1 (fun i E=>E.Has (d+1) (ps i))
    (fun e i hi=>e hi) (fun D e i=>Bank.meet (e (hu i)) (e (hv i)))
  have t := all.bind (b:=2^w-1) (q:=fun E=>E.Has (d+1+w) (any59 ps)) (by
    intro D _ hp
    exact balancedOr59 D ps hp)
  apply t.weaken (by simp;omega)
  intro E ok
  have eqn : any59 ps = (fun x=>decide (∃i,u i x=true ∧ v i x=true)) := by
    funext x; simp [any59,ps]
  simpa [eqn,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ok

lemma multiply59 {I w d} (B : Bank I) {A C : Mat59 I w} (ha : HasMat B d A) (hc : HasMat B d C) :
    B.Grow (2*8^w) (fun E=>HasMat E (d+(w+1)) (mul59 A C)) := by
  let entry (i j : Fin (2^w)) (E : Bank I) := E.Has (d+(w+1)) (mul59 A C i j)
  have t := B.collectFin (2^w) (2^w*(2*2^w)) (fun i E=>∀j, entry i j E)
    (fun e i h j=>e (h j)) (by
      intro D e i
      apply D.collectFin (2^w) (2*2^w) (entry i) (fun e' j h=>e' h)
      intro E e' j
      exact dot59 E (A i) (fun t=>C t j) (fun a=>e' (e (ha i a))) (fun a=>e' (e (hc a j))))
  have cost : 2^w*(2^w*(2*2^w)) = 2*8^w := by
    rw [show 8 = 2*(2*2) by decide,mul_pow,mul_pow]
    ring
  exact t.weaken cost.le (fun _ h=>h)
end PEqualNP.Outside.L_clb_059_aux


namespace PEqualNP.Outside.L_clb_059_aux

noncomputable def segment59 {I w : Nat} (M : Nat → Mat59 I w) (off len : Nat) : Mat59 I w :=
  fun u v x => @decide (Path59 (fun j a b => M j a b x=true) off len u v) (Classical.propDecidable _)

theorem segmentOne59 {I w : Nat} (M : Nat → Mat59 I w) (off : Nat) : segment59 M off 1=M off := by
  funext u v x
  cases hh : M off u v x <;> simp [segment59,pathOne59,hh]

theorem segmentAdd59 {I w : Nat} (M : Nat → Mat59 I w) (off a b : Nat) :
    segment59 M off (a+b)=mul59 (segment59 M off a) (segment59 M (off+a) b) := by
  classical
  funext u v x
  apply Bool.eq_iff_iff.mpr
  let E := fun j a b => M j a b x=true
  constructor
  · intro hl
    obtain ⟨z,first,last⟩ := (pathAdd59 E off a b u v).mp (of_decide_eq_true hl)
    apply decide_eq_true
    exact ⟨z,decide_eq_true first,decide_eq_true last⟩
  · intro hr
    apply decide_eq_true
    obtain ⟨z,first,last⟩ := of_decide_eq_true hr
    exact (pathAdd59 E off a b u v).mpr ⟨z,of_decide_eq_true first,of_decide_eq_true last⟩

theorem segmentTrace59 {I w : Nat} (M : Nat → Mat59 I w) (n : Nat) (x : Fin I → Bool) :
    (∃ u, segment59 M 0 n u u x=true) ↔
      ∃ f : Fin (n+1) → Fin (2^w), f 0=f (Fin.last n) ∧
        ∀ i : Fin n, M i.val (f i.castSucc) (f i.succ) x=true := by
  simp only [segment59,decide_eq_true_eq,pathFin59,Nat.zero_add]
  constructor
  · rintro ⟨u,f,first,last,h⟩
    exact ⟨f,first.trans last.symm,h⟩
  · rintro ⟨f,closed,h⟩
    exact ⟨f 0,f,rfl,closed.symm,h⟩

private theorem productAt59 {I w : Nat} (M : Nat → Mat59 I w) (d h off n : Nat)
    (pos : 0<n) (lim : n≤2^h) (B : Bank I)
    (leaf : ∀ j, off≤j → j<off+n → HasMat B d (M j)) :
    B.Grow ((n-1)*(2*8^w)) (fun F => HasMat F (d+h*(w+1)) (segment59 M off n)) := by
  let P := fun h off n => ∀ B : Bank I, (∀ j, off≤j → j<off+n → HasMat B d (M j)) →
    B.Grow ((n-1)*(2*8^w)) (fun F => HasMat F (d+h*(w+1)) (segment59 M off n))
  apply balancedRange59 P ?_ ?_ h off n pos lim B leaf
  · intro k s B leaf
    refine ⟨B,fun {_ _} hf => hf,by simp,?_⟩
    rw [segmentOne59]
    intro u v
    exact (leaf s (by omega) (by omega) u v).raise (by omega)
  · intro k s a b ha hb left right B leaf
    obtain ⟨L,extL,billL,hl⟩ := left B (fun j hj hj' => leaf j hj (by omega))
    obtain ⟨R,extR,billR,hr⟩ := right L (fun j hj hj' u v =>
      extL (leaf j (by omega) (by omega) u v))
    have hl' : HasMat R (d+k*(w+1)) (segment59 M s a) := fun u v => extR (hl u v)
    obtain ⟨F,extF,billF,hf⟩ := multiply59 R hl' hr
    refine ⟨F,fun {_ _} hh => extF (extR (extL hh)),?_,?_⟩
    · have eq : a+b-1=(a-1)+(b-1)+1 := by omega
      rw [eq,Nat.add_mul,Nat.add_mul,Nat.one_mul]
      omega
    · rw [segmentAdd59, Nat.succ_mul,←Nat.add_assoc]
      exact hf

theorem product59 {I w : Nat} (B : Bank I) (M : Nat → Mat59 I w) (d off len : Nat)
    (hl : 0<len) (leaf : ∀ j, off≤j → j<off+len → HasMat B d (M j)) :
    B.Grow ((len-1)*(2*8^w)) (fun E => HasMat E (d+(Nat.log2 len+1)*(w+1)) (segment59 M off len)) := by
  exact productAt59 M d _ off len hl (Nat.lt_log2_self.le) B leaf

end PEqualNP.Outside.L_clb_059_aux


namespace PEqualNP.Outside.L_clb_059_aux.Cyclic59

lemma lowBit {w : Nat} (s : Q w) (a : Bool) {j : Nat} (hj : j < w) :
    (edgeCode w s a).testBit j = s.val.testBit j := by
  unfold edgeCode
  rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ s.isLt, ite_eq_left hj]

lemma highBit {w : Nat} (s : Q w) (a : Bool) :
    (edgeCode w s a).testBit w = a := by
  unfold edgeCode
  rw [Nat.add_comm, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ s.isLt]
  cases a <;> simp

def readTime {n w : Nat} (_hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (t j : Nat) := (edgeCode w (q (t % n)) (a (t % n))).testBit j

lemma cyclicStep {n w : Nat} (hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (close : q n = q 0) (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (t j : Nat) (hj : j < w) :
    readTime hn q a t (j+1) = readTime hn q a (t+1) j := by
  have ht := Nat.mod_lt t hn
  have qstep : q ((t+1)%n) = next w (q (t%n)) (a (t%n)) := by
    rw [←Nat.mod_add_mod t n 1]
    by_cases h : t%n+1<n
    · rw [Nat.mod_eq_of_lt h,step _ ht]
    · have eq : t%n+1=n := by omega
      rw [eq,Nat.mod_self]
      exact close.symm.trans ((congrArg q eq.symm).trans (step _ ht))
  unfold readTime
  rw [lowBit _ _ hj, qstep]
  exact Nat.testBit_add_one .. 

lemma shiftWindow {n w : Nat} (hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (close : q n = q 0) (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (t j : Nat) (hj : j ≤ w) :
    readTime hn q a t j = readTime hn q a (t+j) 0 := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [cyclicStep hn q a close step t j (by omega), ih (t+1) (by omega)]
    congr 1; omega

lemma recoveredTime {n w : Nat} (hn : 0 < n) (q : Nat → Q w) (a : Nat → Bool)
    (close : q n = q 0) (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (p : Nat) :
    a ((p%n+n-w%n)%n) = readTime hn q a p 0 := by
  let t := p%n+n-w%n
  have shift := shiftWindow hn q a close step t w (by omega)
  change (edgeCode w _ _).testBit w = _ at shift
  rw [highBit] at shift
  have hmod : (t+w)%n=p%n := by
    calc
      (t+w)%n = (t+w%n)%n := by simp
      _ = (p%n+n)%n := by
        congr 1
        dsimp [t]
        have := Nat.mod_lt w hn
        omega
      _ = p%n := by simp
  change a (t%n) = _
  rw [shift]
  unfold readTime
  rw [hmod]

theorem validPicked {n w : Nat} (hn : 0 < n)
    {table : Fin n → (Fin (w+1) → Bool) → Bool}
    (q : Nat → Q w) (a : Nat → Bool) (close : q n = q 0)
    (step : ∀ t < n, q (t+1) = next w (q t) (a t))
    (ok : ∀ t (ht:t<n), table ⟨t,ht⟩ (fun j => (edgeCode w (q t) (a t)).testBit j.val) = true) :
    ∀ i : Fin n, table i (fun j =>
      a ((((i.val+j.val)%n)+n-w%n)%n)) = true := by
  intro i
  have good := ok i.val i.isLt
  convert good using 2
  funext j
  rw [recoveredTime hn q a close step (i.val+j.val),
    ←shiftWindow hn q a close step i.val j.val (by omega)]
  simp [readTime,Nat.mod_eq_of_lt i.isLt]

def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | w+1 => 2^w * (f w).toNat + pack f w

lemma packLt (f : Nat → Bool) (w : Nat) : pack f w < 2^w := by
  induction w with
  | zero => simp [pack]
  | succ w ih => cases hb : f w <;> simp [pack,hb,Nat.pow_succ] <;> omega

lemma packBit (f : Nat → Bool) {w j : Nat} (hj : j < w) : (pack f w).testBit j = f j := by
  induction w with
  | zero => omega
  | succ w ih =>
    rw [pack, Nat.testBit_two_pow_mul_add _ (packLt f w)]
    by_cases h : j < w
    · simp [h,ih h]
    · have : j=w := by omega
      subst j
      cases f w <;> simp

def stream {n : Nat} (hn : 0 < n) (word : Fin n → Bool) (t j : Nat) : Bool :=
  word ⟨(t+j)%n,Nat.mod_lt _ hn⟩

def state {n : Nat} (hn : 0 < n) (word : Fin n → Bool) (w t : Nat) : Q w :=
  ⟨pack (stream hn word t) w,packLt ..⟩

lemma edgeWindow {n w : Nat} (hn : 0 < n) (word : Fin n → Bool) (t j : Nat) (hj : j ≤ w) :
    (edgeCode w (state hn word w t) (stream hn word t w)).testBit j = stream hn word t j := by
  by_cases h : j<w
  · rw [lowBit _ _ h]
    exact packBit _ h
  · have : j=w := by omega
    subst j
    exact highBit ..

lemma stateStep {n w : Nat} (hn : 0 < n) (word : Fin n → Bool) (t : Nat) :
    state hn word w (t+1) = next w (state hn word w t) (stream hn word t w) := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < w
  · change (pack _ w).testBit j = (edgeCode .. / 2).testBit j
    rw [packBit _ h,Nat.testBit_div_two, edgeWindow hn word _ _ (by omega)]
    unfold stream
    congr 3; omega
  · have hbound : 2^w ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (state hn word w (t+1)).isLt hbound),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (next w (state hn word w t) (stream hn word t w)).isLt hbound)]

theorem wordWalk {n w : Nat} (hn : 0 < n)
    {table : Fin n → (Fin (w+1) → Bool) → Bool} (word : Fin n → Bool)
    (ok : ∀ i : Fin n, table i (fun j => word ⟨(i.val + j.val)%n,Nat.mod_lt _ hn⟩) = true) :
    ∃ (q : Nat → Q w) (a : Nat → Bool), q n = q 0 ∧
      (∀ t < n, q (t+1) = next w (q t) (a t)) ∧
      (∀ t (ht:t<n), table ⟨t,ht⟩ (fun j => (edgeCode w (q t) (a t)).testBit j.val) = true) := by
  refine ⟨state hn word w, fun t => stream hn word t w, ?_, fun t _ => stateStep hn word t, ?_⟩
  · have per : stream hn word n = stream hn word 0 := by funext j; simp [stream]
    apply Fin.ext
    exact congrArg (fun f => pack f w) per
  · intro t ht
    have eq : (fun j : Fin (w+1) => (edgeCode w (state hn word w t) (stream hn word t w)).testBit j.val)
        = fun j => word ⟨(t+j.val)%n,Nat.mod_lt _ hn⟩ := by
      funext j
      exact edgeWindow hn word t j.val (by omega)
    rw [eq]
    exact ok ⟨t,ht⟩

end PEqualNP.Outside.L_clb_059_aux.Cyclic59

namespace PEqualNP.Outside.L_clb_059_aux

theorem trace59 {n w} (hn : 0<n) (table : Fin n → (Fin (w+1) → Bool) → Bool) :
    (∃ s : Fin (n+1) → Q w, s 0=s (Fin.last n) ∧ ∀ i : Fin n,
      edge59 i (s i.castSucc) (s i.succ) (tableInput59 table)=true) ↔
    ∃ word : Fin n → Bool, ∀ i, table i (fun j=>word ⟨(i.val+j.val)%n,Nat.mod_lt _ hn⟩)=true := by
  constructor
  · rintro ⟨s,closed,steps⟩
    have each (i : Fin n) := (edge59_iff ..).mp (steps i)
    choose bit hnext htest using each
    let q (j : Nat) := s ⟨min j n, by omega⟩
    let b (j : Nat) := if hj : j<n then bit ⟨j,hj⟩ else false
    have atQ (j : Nat) (hj : j≤n) : q j=s ⟨j,by omega⟩ := by simp [q,Nat.min_eq_left hj]
    have hclosed : q n=q 0 := by
      rw [atQ n le_rfl,atQ 0 (Nat.zero_le n)]
      exact closed.symm
    have hstep (j : Nat) (hj : j<n) : q (j+1)=next w (q j) (b j) := by
      rw [atQ (j+1) (by omega),atQ j (by omega),show b j=bit ⟨j,hj⟩ by simp [b,hj]]
      exact (hnext ⟨j,hj⟩).symm
    have hgood (j : Nat) (hj : j<n) :
        table ⟨j,hj⟩ (fun t=>(edgeCode w (q j) (b j)).testBit t.val)=true := by
      rw [atQ j (by omega),show b j=bit ⟨j,hj⟩ by simp [b,hj]]
      have h := htest ⟨j,hj⟩
      rw [show tableInput59 table (addr w ⟨j,hj⟩ (s (⟨j,hj⟩ : Fin n).castSucc) (bit ⟨j,hj⟩)) = _
        from getInput59 table ⟨j,hj⟩ _ (edgeLt ..) _] at h
      exact h
    exact ⟨fun p=>b ((p.val+n-w%n)%n),Cyclic59.validPicked hn q b hclosed hstep hgood⟩
  · rintro ⟨word,ok⟩
    obtain ⟨q,b,closed,steps,valid⟩:=Cyclic59.wordWalk hn word ok
    refine ⟨fun t=>q t.val,closed.symm,?_⟩
    intro i
    refine (edge59_iff ..).mpr ⟨b i.val,(steps i.val i.isLt).symm,?_⟩
    exact (getInput59 table i _ (edgeLt ..) _).trans (valid i.val i.isLt)

end PEqualNP.Outside.L_clb_059_aux

namespace PEqualNP.Outside.L_clb_059_aux

theorem tracePath59 {n w} (hn : 0<n) (table : Fin n → (Fin (w+1) → Bool) → Bool)
    (E : Nat → Q w → Q w → Prop)
    (onTable : ∀ (i : Fin n) s t, E i.val s t ↔ edge59 i s t (tableInput59 table)=true) :
    (∃ u, Path59 E 0 n u u) ↔
      ∃ word : Fin n → Bool, ∀ i, table i (fun j=>word ⟨(i.val+j.val)%n,Nat.mod_lt _ hn⟩)=true := by
  rw [← trace59 hn table]
  constructor
  · rintro ⟨u,path⟩
    obtain ⟨f,first,last,each⟩:=(pathFin59 E 0 n u u).mp path
    exact ⟨f,first.trans last.symm,fun i => (onTable i ..).mp (by simpa only [Nat.zero_add] using each i)⟩
  · rintro ⟨f,closed,each⟩
    refine ⟨f 0,(pathFin59 ..).mpr ⟨f,rfl,closed.symm,?_⟩⟩
    intro i
    simpa only [Nat.zero_add] using (onTable i ..).mpr (each i)

end PEqualNP.Outside.L_clb_059_aux

namespace PEqualNP.Outside.L_clb_059_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
theorem circuit59 (n w : Nat) (hn : 0<n) :
  ∃ C : Circuit, Monotone2 C ∧ ReadsBack (I n w) C ∧ C.output<I n w+C.size ∧
    C.size≤6*n*8^w+3 ∧ C.depth (I n w) ≤ 1+(Nat.log2 n+1)*(w+1)+w ∧
    ∀ table : Fin n→(Fin (w+1)→Bool)→Bool,
      C.eval (List.ofFn (tableInput59 table))=true ↔
        ∃ word : Fin n→Bool,∀ i, table i (fun j=>word ⟨(i.val+j.val)%n,Nat.mod_lt _ hn⟩)=true := by
  classical
  let M : Nat → Mat59 (I n w) w := fun j => edge59 ⟨j%n,Nat.mod_lt _ hn⟩
  let d := 1+(Nat.log2 n+1)*(w+1)
  let mat := segment59 M 0 n
  let sig := any59 (fun u => mat u u)
  obtain ⟨B,_,cB,leaf⟩ := leavesBank59 n w
  obtain ⟨D,_,cD,hmat⟩ := product59 B M 1 0 n hn (by
    intro j _ hj
    exact fun s t => leaf _ s t)
  obtain ⟨F,_,cF,out⟩ := balancedOr59 D (fun u => mat u u) (d:=d) (fun u => hmat u u)
  have c1 : B.gates.length≤n*4^w := by simpa [Bank.empty] using cB
  have a : 4^w≤8^w := Nat.pow_le_pow_left (by decide) w
  have b : 2^w≤8^w := Nat.pow_le_pow_left (by decide) w
  have c := Nat.mul_le_mul_left n a
  have e := Nat.mul_le_mul_right (2*8^w) (show n-1≤n by omega)
  have j := Nat.mul_le_mul_right (8^w) (show 1≤n by omega)
  have price : F.gates.length ≤ 6*n*8^w+3 := by
    have eq1 : n*(2*8^w)=2*(n*8^w) := by ring
    have eq2 : 6*n*8^w=6*(n*8^w) := by ring
    rw [eq2]
    rw [eq1] at e
    simp only [one_mul] at j
    omega
  obtain ⟨index,bound,depth,cval⟩ := out
  refine ⟨⟨F.gates,index⟩,F.mono,F.back,bound,price,depth,?_⟩
  intro table
  change F.val index (tableInput59 table)=true ↔ _
  rw [cval]
  let E (j : Nat) (s t : Q w) := M j s t (tableInput59 table)=true
  have edge (i : Fin n) (s t : Q w) : E i.val s t ↔ edge59 i s t (tableInput59 table)=true := by
    simp [E,M,Nat.mod_eq_of_lt i.isLt]
  simpa only [sig,any59,mat,segment59,decide_eq_true_eq,E] using tracePath59 hn table E edge

end PEqualNP.Outside.L_clb_059_aux

theorem PEqualNP.Outside.L_clb_059 :
∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 6 * n * 8 ^ w + 3 ∧
    C.depth I ≤ 1 + (Nat.log2 n + 1) * (w + 1) + w ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let x := (List.ofFn (fun i : Fin n => List.ofFn (fun p : Fin (2 ^ (w + 1)) =>
        table i (fun j => p.val.testBit j.val)))).flatten
      C.eval x = true ↔ ∃ word : Fin n → Bool, ∀ i : Fin n,
        table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true := by
  intro n w hn
  dsimp only
  obtain ⟨C,m,b,o,s,d,h⟩ := PEqualNP.Outside.L_clb_059_aux.circuit59 n w hn
  refine ⟨C,m,b,o,s,d,?_⟩
  intro table
  simpa only [PEqualNP.Outside.L_clb_059_aux.inputList59] using h table

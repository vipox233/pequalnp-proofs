import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27701
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def Base {R S} (rows : S → R) (roots : List (Wire S)) (p : ℕ) (ws : List (Wire R)) :=
  ∃ bank, Reach roots p bank ∧ ∀ v ∈ ws, Available bank (restrictRows rows v)

theorem base_mono {R S} {rows : S → R} {roots p} {ws us : List (Wire R)}
    (env : Base rows roots p ws) (h : ∀ v ∈ us, v ∈ ws) : Base rows roots p us := by
  obtain ⟨bank,reach,sup⟩ := env
  exact ⟨bank,reach,fun v hv => sup _ (h _ hv)⟩

theorem base_one {R S} {rows : S → R} {roots p} {a : Wire R} {ws}
    (env : Base rows roots p (a::ws)) (k : Bool) :
    Base rows roots (p+1) (inv a::kept k a ws) := by
  obtain ⟨bank,reach,sup⟩ := env
  refine ⟨_,Reach.one reach (sup a (by simp)),?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hr
  · exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
  · exact available_cons _ (sup w (List.mem_cons.mpr (mem_kept hr)))

theorem base_two {R S} {rows : S → R} {roots p} {a b : Wire R} {ws}
    (env : Base rows roots p (a::b::ws)) (op ka kb : Bool) :
    Base rows roots (p+1) (combine op a b :: kept ka a (kept kb b ws)) := by
  obtain ⟨bank,reach,sup⟩ := env
  refine ⟨_,Reach.two op reach (sup a (by simp)) (sup b (by simp)),?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hr
  · exact Or.inl (List.mem_cons.mpr (Or.inl (by cases op <;> rfl)))
  · apply available_cons _ (sup w ?_)
    rcases mem_kept hr with rfl | hr
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hr))

theorem base_free_one {R S} {rows : S → R} {roots p} {a : Wire R} {ws}
    (env : Base rows roots p (a::ws)) (ha : Constant (restrictRows rows a)) (k : Bool) :
    Base rows roots p (inv a::kept k a ws) := by
  obtain ⟨bank,reach,sup⟩ := env
  refine ⟨bank,reach,?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hr
  · exact Or.inr (inv_constant ha)
  · exact sup _ (List.mem_cons.mpr (mem_kept hr))

theorem base_free_two {R S} {rows : S → R} {roots p} {a b : Wire R} {ws}
    (env : Base rows roots p (a::b::ws))
    (con : Constant (restrictRows rows a) ∨ Constant (restrictRows rows b)) (op ka kb : Bool) :
    Base rows roots p (combine op a b :: kept ka a (kept kb b ws)) := by
  obtain ⟨bank,reach,sup⟩ := env
  refine ⟨bank,reach,?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hr
  · have := from_constant op con (sup a (by simp)) (sup b (by simp))
    cases op <;> exact this
  · apply sup
    rcases mem_kept hr with rfl | hr
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hr))

def LowerOn {S} (roots : List (Wire S)) (f : Wire S) (l : ℕ) :=
  ∀ p bank, Reach roots p bank → Available bank f → l ≤ p

theorem free_bound {R S} {rows : S → R} {roots p} {g u : Wire R} {us s l}
    (run : Run g s (u::us)) (ng : ¬Constant (restrictRows rows g))
    (env : Base rows roots p (u::us)) (lo : LowerOn roots (restrictRows rows g) l) :
    l+cost (restrictRows rows u) ≤ p+s := by
  obtain ⟨b,r,sup⟩ := env
  have h := projected_bound rows run ng r (by
    intro w hw
    rcases List.mem_map.mp hw with ⟨v,hv,rfl⟩
    exact sup _ hv) lo
  simp only [List.map_cons,mass_cons] at h
  omega

theorem controlling {R S} (rows : Bool → S → R) (mark : Wire R)
    (bits : ∀ b, restrictRows (rows b) mark = fun _ => b)
    (roots : Bool → List (Wire S)) {goal : Wire R}
    (nc : ∀ b, ¬Constant (restrictRows (rows b) goal)) (lo : Bool → ℕ)
    (hl : ∀ b, LowerOn (roots b) (restrictRows (rows b) goal) (lo b))
    {s ws} (run : Run goal s ws) (mem : mark∈ws) (p : ℕ)
    (env : ∀ b, Base (rows b) (roots b) p ws) :
    (∀ b, lo b+1≤s+p) ∧ ∃ b, lo b+2≤s+p := by
  induction run generalizing p with
  | stop =>
    have eq : mark=goal := by simpa using mem
    exact False.elim (nc false ⟨false,eq ▸ bits false⟩)
  | perm perm _ ih =>
    exact ih (perm.mem_iff.mpr mem) p (fun b => base_mono (env b) (fun _ h => perm.mem_iff.mp h))
  | @one s a rest k tail ih =>
    by_cases same : mark=a
    · subst a
      have bound (b : Bool) := free_bound tail (nc b)
        (base_free_one (env b) ⟨b,bits b⟩ k) (hl b)
      have c (b : Bool) : Constant (restrictRows (rows b) (inv mark)) := inv_constant ⟨b,bits b⟩
      simp only [cost,c,ite_true] at bound
      exact ⟨fun b => by have := bound b; omega,⟨false,by have := bound false; omega⟩⟩
    · have hr := (List.mem_cons.mp mem).resolve_left same
      have hm : mark ∈ inv a::kept k a rest := by cases k <;> simp [kept,hr]
      obtain ⟨each,b,hb⟩ := ih hm (p+1) (fun b => base_one (env b) k)
      exact ⟨fun i => by have := each i; omega, ⟨b,by omega⟩⟩
  | @two s a b rest op ka kb tail ih =>
    by_cases hit : mark=a ∨ mark=b
    · have con (i : Bool) : Constant (restrictRows (rows i) a) ∨ Constant (restrictRows (rows i) b) := by
        rcases hit with rfl | rfl
        · exact Or.inl ⟨i,bits i⟩
        · exact Or.inr ⟨i,bits i⟩
      have bound (i : Bool) := free_bound tail (nc i) (base_free_two (env i) (con i) op ka kb) (hl i)
      have ctrl : Constant (restrictRows (rows op) (combine op a b)) := by
        refine ⟨op,?_⟩
        have eq : ∀ x, mark (rows op x)=op := congrFun (bits op)
        funext x
        rcases hit with rfl | rfl <;> cases op <;> simp [combine,restrictRows,eq]
      have h := bound op
      simp only [cost,ctrl,ite_true] at h
      exact ⟨fun i => by have := bound i; omega, ⟨op,by omega⟩⟩
    · have hr : mark ∈ rest := by simpa [not_or.mp hit |>.1,not_or.mp hit |>.2] using mem
      have hm : mark ∈ combine op a b :: kept ka a (kept kb b rest) := by cases ka <;> cases kb <;> simp [kept,hr]
      obtain ⟨each,i,hi⟩ := ih hm (p+1) (fun i => base_two (env i) op ka kb)
      exact ⟨fun j => by have := each j; omega, ⟨i,by omega⟩⟩
def pinMove (w : Sig) (d : Row) (b : Bool) : Move :=
  if b then (neg w,zero,d) else (zero,w,d)

theorem lower_pair {raw : List Sig} {T mark : Sig} (δ : Row) (pT : proper T)
    (needed : Essential T raw mark) (G : Bool → Sig) (L : Bool → ℕ)
    (maps : ∀ b, checkMap [pinMove mark δ b] raw T raw (G b) = true)
    (pinned : ∀ b, movedWord [pinMove mark δ b] mark = if b then one else zero)
    (ps : ∀ b, proper (G b)) (priors : ∀ b, Lower raw (G b) (L b)) (n : ℕ)
    (hn : n ≤ max ((max (L false) (L true))+1) ((min (L false) (L true))+2)) :
    Lower raw T n := by
  classical
  intro p bank reach hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT reach hit
  obtain ⟨r,s,hd,iso⟩ := needed
  have hm := raw_required run raw mark sub r s hd iso
  have run' := list_run run S.toList (Finset.nodup_toList _) (by simp)
  let row (b : Bool) := movedRow [pinMove mark δ b]
  have eq (b : Bool) : restrictRows (row b) (observe T) = observe (G b) :=
    (observe_rename _ _).symm.trans (congrArg observe (map_correct (maps b)).1)
  have bm (b : Bool) : restrictRows (row b) (observe mark) = fun _ => b := by
    funext r
    change bit (movedRow [pinMove mark δ b] r) mark = b
    rw [←bit_moved,pinned b]
    cases b <;> simp [bit_zero,bit_one]
  have env (b : Bool) : Base (row b) (raw.map observe) 0 (S.toList.map observe) := by
    refine ⟨_,Reach.start,?_⟩
    intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    rw [←observe_rename]
    exact (map_correct (maps b)).2 a (sub _ (Finset.mem_toList.mp ha))
  have key := controlling row (observe mark) bm (fun _ => raw.map observe)
    (fun b => eq b ▸ observe_proper (ps b)) L (fun b => eq b ▸ priors b) run'
    (List.mem_map_of_mem (Finset.mem_toList.mpr hm)) 0 env
  obtain ⟨each,b,hb⟩ := key
  have h0 := each false
  have h1 := each true
  cases b <;> omega

theorem gate_list_bound {raw : List Sig} {T : Sig} {n : ℕ} (lo : Lower raw T n) (pt : proper T)
    (gs : List Gate) (w : List Sig) (leg : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ok : w.all (freeWord raw) = true) (out : T ∈ execute gs w) : n ≤ gs.length := by
  obtain ⟨k,t,S,hk,run,sub⟩ := extract gs w leg pt out
  have run' := list_run run S.toList (Finset.nodup_toList _) (by simp)
  obtain ⟨q,next,hr,ha,hq⟩ := contraction (observe_proper pt) run' (raw.map observe) Reach.start (by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    exact freeWord_ok (List.all_eq_true.mp ok a (sub _ (Finset.mem_toList.mp ha))))
  have := lo _ _ hr ha
  omega

theorem circuit_table {C : Circuit} (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (orig : List Sig) (sample : Row → Fin 9 → Bool) (hs : ∀ r, List.ofFn (sample r) = orig.map (bit r))
    {T : Sig} (hp : proper T) (output : ∀ r, C.eval (List.ofFn (sample r)) = bit r T) :
    T ∈ execute C.gates orig := by
  have he : (execute C.gates orig).getD C.output zero = T := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates orig).getD C.output zero) = bit r T
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),←hs]
    exact output r
  exact he ▸ ((get_rep _ _).resolve_right (by rw [he]; exact fun hn => hn hp))

def wordOfChunks (xs : List Nat) : Sig :=
  BitVec.ofNat 512 (xs.foldr (fun a b => a + (b <<< 32)) 0)

def x0 : Sig := wordOfChunks [2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530,2863311530]

def x1 : Sig := wordOfChunks [3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836,3435973836]

def x2 : Sig := wordOfChunks [4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160,4042322160]

def x3 : Sig := wordOfChunks [4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360,4278255360]

def x4 : Sig := wordOfChunks [4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760,4294901760]

def x5 : Sig := wordOfChunks [0,4294967295,0,4294967295,0,4294967295,0,4294967295,0,4294967295,0,4294967295,0,4294967295,0,4294967295]

def x6 : Sig := wordOfChunks [0,0,4294967295,4294967295,0,0,4294967295,4294967295,0,0,4294967295,4294967295,0,0,4294967295,4294967295]

def x7 : Sig := wordOfChunks [0,0,0,0,4294967295,4294967295,4294967295,4294967295,0,0,0,0,4294967295,4294967295,4294967295,4294967295]

def x8 : Sig := wordOfChunks [0,0,0,0,0,0,0,0,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

def rawVars : List Sig := [x0,x1,x2,x3,x4,x5,x6,x7,x8]

def matchPinned : Sig := wordOfChunks [0,0,4042260480,4244425932,4026593280,4294967295,4042321920,4294967295,4294953984,4294953984,4294953984,4294954188,4294966272,4294967295,4294966272,4294967295]

def tab10 : Sig := wordOfChunks [0,0,0,3435973836,4026593280,4294967295,4026593280,4294967295,3422604288,3422604288,3422604288,3435973836,4227922944,4294967295,4227922944,4294967295]

def tab11 : Sig := wordOfChunks [0,0,0,3435973836,0,4294967295,0,4294967295,3422604288,3422604288,3422604288,3435973836,3422604288,4294967295,3422604288,4294967295]

def tab12 : Sig := wordOfChunks [0,0,0,0,0,4294967295,0,4294967295,3422604288,3422604288,3422604288,3422604288,3422604288,4294967295,3422604288,4294967295]

theorem lb_tab12_4 : Lower rawVars tab12 4 := by
  let cert : List (Sig × Row × Row) := [(x1,264,266),(x3,258,266),(x5,128,160),(x7,32,160),(x8,10,266)]
  have h := lower_count (raw:=rawVars) (T:=tab12) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

def tab13 : Sig := wordOfChunks [0,3435973836,0,3435973836,0,4294967295,0,4294967295,3422604288,3435973836,3422604288,3435973836,3422604288,4294967295,3422604288,4294967295]

theorem lb_tab13_4 : Lower rawVars tab13 4 := by
  let cert : List (Sig × Row × Row) := [(x1,32,34),(x3,258,266),(x5,2,34),(x7,32,160),(x8,10,266)]
  have h := lower_count (raw:=rawVars) (T:=tab13) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

theorem lb_tab11_6 : Lower rawVars tab11 6 := by
  let G (b : Bool) : Sig := if b then tab13 else tab12
  let L (b : Bool) : ℕ := if b then 4 else 4
  apply lower_pair (mark:=x6) 64 (by unfold proper; decide +kernel) (witnessB_sound (rs:=(34,98)) (by decide +kernel)) G L
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> unfold proper <;> decide +kernel
  · intro b; cases b
    · exact lb_tab12_4
    · exact lb_tab13_4
  · decide +kernel

def tab14 : Sig := wordOfChunks [0,0,0,3435973836,4278255360,4294967295,4278255360,4294967295,3422604288,3422604288,3422604288,3435973836,4278255360,4294967295,4278255360,4294967295]

def tab15 : Sig := wordOfChunks [0,0,0,0,4278255360,4294967295,4278255360,4294967295,3422604288,3422604288,3422604288,3422604288,4278255360,4294967295,4278255360,4294967295]

theorem lb_tab15_4 : Lower rawVars tab15 4 := by
  let cert : List (Sig × Row × Row) := [(x1,264,266),(x3,128,136),(x5,128,160),(x7,8,136),(x8,10,266)]
  have h := lower_count (raw:=rawVars) (T:=tab15) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

def tab16 : Sig := wordOfChunks [0,3435973836,0,3435973836,4278255360,4294967295,4278255360,4294967295,3422604288,3435973836,3422604288,3435973836,4278255360,4294967295,4278255360,4294967295]

theorem lb_tab16_4 : Lower rawVars tab16 4 := by
  let cert : List (Sig × Row × Row) := [(x1,32,34),(x3,128,136),(x5,2,34),(x7,8,136),(x8,10,266)]
  have h := lower_count (raw:=rawVars) (T:=tab16) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

theorem lb_tab14_6 : Lower rawVars tab14 6 := by
  let G (b : Bool) : Sig := if b then tab16 else tab15
  let L (b : Bool) : ℕ := if b then 4 else 4
  apply lower_pair (mark:=x6) 64 (by unfold proper; decide +kernel) (witnessB_sound (rs:=(34,98)) (by decide +kernel)) G L
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> unfold proper <;> decide +kernel
  · intro b; cases b
    · exact lb_tab15_4
    · exact lb_tab16_4
  · decide +kernel

theorem lb_tab10_8 : Lower rawVars tab10 8 := by
  let G (b : Bool) : Sig := if b then tab14 else tab11
  let L (b : Bool) : ℕ := if b then 6 else 6
  apply lower_pair (mark:=x2) 4 (by unfold proper; decide +kernel) (witnessB_sound (rs:=(136,140)) (by decide +kernel)) G L
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> unfold proper <;> decide +kernel
  · intro b; cases b
    · exact lb_tab11_6
    · exact lb_tab14_6
  · decide +kernel

def tab17 : Sig := wordOfChunks [0,0,4042322160,4244438268,4026593280,4294967295,4042322160,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

def tab18 : Sig := wordOfChunks [0,0,4042322160,4042322160,4026593280,4294967295,4042322160,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

def tab19 : Sig := wordOfChunks [0,0,4042322160,4042322160,0,4294967295,4042322160,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

theorem lb_tab19_4 : Lower rawVars tab19 4 := by
  let cert : List (Sig × Row × Row) := [(x2,64,68),(x5,128,160),(x6,4,68),(x7,32,160),(x8,0,256)]
  have h := lower_count (raw:=rawVars) (T:=tab19) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

def tab20 : Sig := wordOfChunks [0,0,4042322160,4042322160,4042322160,4294967295,4042322160,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

theorem lb_tab20_4 : Lower rawVars tab20 4 := by
  let cert : List (Sig × Row × Row) := [(x2,64,68),(x5,128,160),(x6,4,68),(x7,4,132),(x8,0,256)]
  have h := lower_count (raw:=rawVars) (T:=tab20) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

theorem lb_tab18_6 : Lower rawVars tab18 6 := by
  let G (b : Bool) : Sig := if b then tab20 else tab19
  let L (b : Bool) : ℕ := if b then 4 else 4
  apply lower_pair (mark:=x3) 8 (by unfold proper; decide +kernel) (witnessB_sound (rs:=(132,140)) (by decide +kernel)) G L
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> unfold proper <;> decide +kernel
  · intro b; cases b
    · exact lb_tab19_4
    · exact lb_tab20_4
  · decide +kernel

def tab21 : Sig := wordOfChunks [0,0,4042322160,4294967295,4026593280,4294967295,4042322160,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

def tab22 : Sig := wordOfChunks [0,0,4042322160,4294967295,0,4294967295,4042322160,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

theorem lb_tab22_4 : Lower rawVars tab22 4 := by
  let cert : List (Sig × Row × Row) := [(x2,64,68),(x5,64,96),(x6,4,68),(x7,32,160),(x8,0,256)]
  have h := lower_count (raw:=rawVars) (T:=tab22) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

def tab23 : Sig := wordOfChunks [0,0,4042322160,4294967295,4042322160,4294967295,4042322160,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295,4294967295]

theorem lb_tab23_4 : Lower rawVars tab23 4 := by
  let cert : List (Sig × Row × Row) := [(x2,64,68),(x5,64,96),(x6,4,68),(x7,4,132),(x8,0,256)]
  have h := lower_count (raw:=rawVars) (T:=tab23) (by unfold proper; decide +kernel) cert (by decide +kernel)
  have hc : (cert.map Prod.fst).toFinset.card - 1 = 4 := by decide +kernel
  rw [hc] at h
  exact h

theorem lb_tab21_6 : Lower rawVars tab21 6 := by
  let G (b : Bool) : Sig := if b then tab23 else tab22
  let L (b : Bool) : ℕ := if b then 4 else 4
  apply lower_pair (mark:=x3) 8 (by unfold proper; decide +kernel) (witnessB_sound (rs:=(132,140)) (by decide +kernel)) G L
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> unfold proper <;> decide +kernel
  · intro b; cases b
    · exact lb_tab22_4
    · exact lb_tab23_4
  · decide +kernel

theorem lb_tab17_8 : Lower rawVars tab17 8 := by
  let G (b : Bool) : Sig := if b then tab21 else tab18
  let L (b : Bool) : ℕ := if b then 6 else 6
  apply lower_pair (mark:=x1) 2 (by unfold proper; decide +kernel) (witnessB_sound (rs:=(96,98)) (by decide +kernel)) G L
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> unfold proper <;> decide +kernel
  · intro b; cases b
    · exact lb_tab18_6
    · exact lb_tab21_6
  · decide +kernel

theorem lb_matchPinned_10 : Lower rawVars matchPinned 10 := by
  let G (b : Bool) : Sig := if b then tab17 else tab10
  let L (b : Bool) : ℕ := if b then 8 else 8
  apply lower_pair (mark:=x4) 16 (by unfold proper; decide +kernel) (witnessB_sound (rs:=(68,84)) (by decide +kernel)) G L
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> decide +kernel
  · intro b; cases b <;> unfold proper <;> decide +kernel
  · intro b; cases b
    · exact lb_tab10_8
    · exact lb_tab17_8
  · decide +kernel

def pinnedInputs : List Sig := [one,x1,x2,x3,x4,x5,x6,x7,x8]
def rowInput (r : Row) (i : Fin 9) := bit r (pinnedInputs.getD i.val zero)
theorem rowInput_list (r : Row) : List.ofFn (rowInput r) = pinnedInputs.map (bit r) := by
  have h : List.ofFn (fun i : Fin 9 => pinnedInputs.getD i.val zero) = pinnedInputs := rfl
  rw [←h,List.map_ofFn]
  rfl

def matching (x : Fin 9 → Bool) := (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) ||
  (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)
set_option maxRecDepth 4096 in
theorem pin_matches : ∀ r, matching (rowInput r) = bit r matchPinned := by decide +kernel

theorem bad_prefix (C : Circuit) (leg : PEqualNP.MetaComplexity.FanInTwo C)
    (sz : C.size ≤ 11) (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x)
    (a b : Gate) (h1 : C.gates.head? = some a) (h2 : C.gates.tail.head? = some b)
    (free : (execute [a,b] pinnedInputs).all (freeWord rawVars) = true) : False := by
  have pt : proper matchPinned := by unfold proper; decide +kernel
  have hout := circuit_table leg pinnedInputs rowInput rowInput_list pt
    (fun r => (correct (rowInput r)).trans (pin_matches r))
  obtain ⟨tail,hg⟩ : ∃ tail, C.gates = a::b::tail := by
    cases h : C.gates with
    | nil => simp [h] at h1
    | cons u rest =>
      cases ht : rest with
      | nil => simp [h,ht] at h2
      | cons v tail =>
        have hu : u = a := by simpa [h] using h1
        have hv : v = b := by simpa [h,ht] using h2
        exact ⟨tail,by rw [hu,hv]⟩
  rw [hg] at hout
  have small := gate_list_bound lb_matchPinned_10 pt tail (execute [a,b] pinnedInputs)
    (fun g hm => leg g (by simp [hg,hm])) free hout
  change C.gates.length ≤ 11 at sz
  simp only [hg,List.length_cons] at sz
  omega

end PEqualNP.Outside.L_meta_27701

theorem PEqualNP.Outside.L_meta_27701 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩) := by
  rintro ⟨C,leg,sz,correct,_,_,_,_,h1,h2⟩
  exact PEqualNP.Outside.L_meta_27701.bad_prefix C leg sz correct _ _ h1 h2 (by decide +kernel)

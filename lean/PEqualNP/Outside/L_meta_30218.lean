import PEqualNP.Defs






namespace PEqualNP.Outside.L_meta_30218.Core7
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

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
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffefffffffafffeffeefefeaa00fffffffefffffffafffeffeefefeaa00fffffffefffffffafffeffeefefeaa00fffffffefffffffafffeffeefefeaa00
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def nineInputs : List Sig := vars 127
def sampleNine (r : Row) (i : Fin 7) : Bool := bit r (nineInputs.getD i.val zero)
def nineEdge (x : Fin 7 → Bool) := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)

theorem nineTable : ∀ r : Row, bit r graph = nineEdge (sampleNine r) := by decide +kernel
theorem nineList : List.ofFn (fun i : Fin 7 => nineInputs.getD i.val zero) = nineInputs := rfl
theorem nineSampled (r : Row) : List.ofFn (sampleNine r) = nineInputs.map (bit r) := by
  rw [← nineList, List.map_ofFn]
  rfl

theorem nineEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates nineInputs).getD i zero) =
      (C.wires (List.ofFn (sampleNine r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),nineSampled]
  rfl
def neighborRow (i : Fin 7) : Nat := [3,4,4,0,0,0,0].getD i.val 0
def absentRowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< neighborRow i)
def presentRowRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighborRow i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 7, bit (absentRowRow i) graph ≠ bit (presentRowRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (absentRowRow i) (nineInputs.getD j.val zero) =
      bit (presentRowRow i) (nineInputs.getD j.val zero)) := by decide +kernel

theorem binaryLower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 7 C = nineEdge)
    (no : ∀ k, k ≤ 11 → ¬Live true graph k nineInputs.toFinset) :
    12 ≤ C.gates.countP (fun g => !isNot g) := by
  have goalEq : (execute C.gates nineInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (nineEval C legal C.output r).trans ((congrFun computes (sampleNine r)).trans (nineTable r).symm)
  have out := get_rep (u:=true) (execute C.gates nineInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates nineInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : nineInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ nineInputs) : ∃ i : Fin 7, nineInputs.getD i.val zero = a := by
    rw [←nineList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = nineInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run nineInputs (nineInputs.getD i.val zero) sub (absentRowRow i) (presentRowRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  by_contra! small
  exact no k (by omega) (eq ▸ run)


def g41Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffdd,0xffffffffffffffffffffffffffffffffffffd1),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffe7,0x24),(0x0,0x0),(0x3a,0xa),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[]]
def g41D3 (j : Nat) : Nat := 0x7
def g41L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g41D3)
  | _ => emptyPacking
def g41I (_ _ : Nat) : Option (Nat × Nat) := none
def g41 : Forest := ⟨41,3,fun i => g41Y[i]?.getD (0,0),g41C,g41A,g41L,g41I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41P3_0 : block g41 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : block g41 3 0 1=true := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(81,[101,67]),(84,[101,67,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffd87f7,0xfffffffffffffffffffffffffffffffffc8215),(0x2f838,0x9ab8),(0x0,0x0),(0xffffffffffffffffffffffffffffffffff01bb,0x355aa),(0x3fe4c,0x36540),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[]]
def g27D3 (j : Nat) : Nat := 0xf
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K41 V41) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K41 4 [(27,[]),(29,[33]),(53,[83,33]),(54,[83,16,32]),(58,[67,49,16,80]),(90,[96]),(99,[67,100,83]),(101,[100,83,33]),(106,[67,100,48,80]),(108,[100,48,16,81,32]),(114,[49,99,16,80]),(120,[65,48,97,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffe0fc7f2971,0xffffffffffffffffffffffffffffc014280111),(0x0,0x0),(0x10079816da,0x1445b82658),(0x1f081ee3ac,0x11081560ac),(0xffffffffffffffffffffffffffffe00fe3dc8b,0x298a47d882),(0x3ff002d654,0x2ee3429640),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(32,0,29,0,4),(16,4,41,0,4),(20,0,41,0,4),(8,0,53,0,4)]
def g61A : List (List Nat) := [[],[83]]
def g61D4 (j : Nat) : Nat := 0x4fd5120
def g61D5 (j : Nat) : Nat := 0x88401090fd42fe20fd20
def g61H5 (j : Nat) : Nat := 0x600000000000
def g61D6 (j : Nat) : Nat := 0x5889f
def g61H6 (j : Nat) : Nat := 0x28a200900000368000000000000a00
def g61L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g61D4)
  | 5 => (3,1,2,0,0,4,0,g61D5)
  | 6 => (1,0,2,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g61H5
  | 6 => lookupWord 1 17 0 7 2 1 g61H6
  | _ => fun _ => none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 1=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 3=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 1=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
  · exact g61B5
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=1027) (before_sound K27 V27) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K27 7 [(61,[]),(118,[82,98,50,64,16]),(124,[82,66,50,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V27 low61 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffff00787e4cb,0xfffffffffffffffffffffffffffff00282200b),(0x406fa09b4,0x696da61b0),(0x0,0x0),(0xfffffffffffffffffffffffffffff8f90389b1,0x939358990),(0xf01fc1e16,0x921251c04),(0x0,0x0),(0xffe007368,0x6c4404260),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(16,2,73,0,4),(64,0,27,0,4),(10,0,81,0,4),(1,0,90,0,4)]
def g91A : List (List Nat) := [[]]
def g91D4 (j : Nat) : Nat := 0x5bd4940
def g91D5 (j : Nat) : Nat := 0x1083fd40
def g91H5 (j : Nat) : Nat := 0x28000000000
def g91D6 (j : Nat) : Nat := 0x6c09f
def g91H6 (j : Nat) : Nat := 0x0
def g91L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g91D4)
  | 5 => (1,1,2,0,0,0,0,g91D5)
  | 6 => (1,0,2,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g91H5
  | 6 => lookupWord 1 8 0 6 1 1 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 1=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 1=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K61 V61) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K61 7 [(91,[]),(107,[84,99]),(109,[67,84,99,33]),(117,[81,49,33,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V61 low91 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffc2c74c97,0xffffffffffffffffffffffffffffffc2400415),(0x0,0x0),(0x3782d68,0x3590c60),(0xffffffffffffffffffffffffffffffec832e63,0x3cb72862),(0x30fcb0ac,0x38a63088),(0x0,0x0),(0x3f00d350,0xc300),(0x0,0x0),(0x0,0x0)]
def g93C : List ColumnInfo := [(20,0,73,0,4),(9,0,84,0,4)]
def g93A : List (List Nat) := [[]]
def g93D6 (j : Nat) : Nat := 0x105f
def g93L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g93D6)
  | _ => emptyPacking
def g93I (_ _ : Nat) : Option (Nat × Nat) := none
def g93 : Forest := ⟨93,6,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P6_0 : block g93 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g93B6 : block g93 6 0 1=true := g93P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact (rfl : block g93 4 0 0 = true)
  · exact (rfl : block g93 5 0 0 = true)
  · exact g93B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 7 := lower_forest (g:=g93) (i:=0) (hints:=1027) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 7 [(93,[]),(121,[67,66,48,82,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)
def g122Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffffffffffffffffffffffffc80cfe4c9d,0xffffffffffffffffffffffffffffc81453cc0d),(0x0,0x0),(0x307700bd5a,0x1014021c52),(0x1f881f0b74,0x11890c0170),(0xffffffffffffffffffffffffffffe00fe073e1,0x254ba823a0),(0x3ff001c6aa,0x2e62d1c288),(0x0,0x0),(0x0,0x0)]
def g122C : List ColumnInfo := [(32,0,90,0,4),(64,0,58,0,4),(16,0,106,0,4),(8,0,114,0,4),(2,0,120,0,4)]
def g122A : List (List Nat) := [[],[99,84],[49,100],[65,101],[81,67],[97,83]]
def g122D4 (j : Nat) : Nat := 0x57d4d10
def g122D5 (j : Nat) : Nat := 0x1a0fd20fd10
def g122H5 (j : Nat) : Nat := 0x80
def g122D6 (j : Nat) : Nat := 0x23440bf
def g122H6 (j : Nat) : Nat := 0x208006800000000000000022402e294008344020c0001eed9
def g122L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g122D4)
  | 5 => (2,1,3,0,0,4,0,g122D5)
  | 6 => (1,0,3,0,0,0,0,g122D6)
  | _ => emptyPacking
def g122I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 8 1 3 g122H5
  | 6 => lookupWord 2 27 1 8 1 3 g122H6
  | _ => fun _ => none
def g122 : Forest := ⟨122,6,fun i => g122Y[i]?.getD (0,0),g122C,g122A,g122L,g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P4_0 : block g122 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B4 : block g122 4 0 1=true := g122P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5_0 : block g122 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B5 : block g122 5 0 2=true := g122P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P6_0 : block g122 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B6 : block g122 6 0 1=true := g122P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122T : checkedTables g122 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g122 0 0 0 = true)
  · exact (rfl : block g122 1 0 0 = true)
  · exact (rfl : block g122 2 0 0 = true)
  · exact (rfl : block g122 3 0 0 = true)
  · exact g122B4
  · exact g122B5
  · exact g122B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 7 := lower_forest (g:=g122) (i:=0) (hints:=51466304) (before_sound K93 V93) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K93 7 [(122,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V93 low122 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[(0x10e0e7d30dfff0552631aa4,0x66c30cd990008620884),(0xfffffffffffffffe281061c0e0784aa88d6a8f,0xffffffffffffffffbf5dfbe4cb7d4aa88d2a8d),(0xfffffffffffffffe301f82ff0380d02d0188bd,0x3a16cff78fd7502c0188ac),(0x3fe0030003ff65d429a17e,0x7ae0838e3266477409a13a),(0x1c00003fffc006e11dcdd1a,0x4080000830002451105112),(0x0,0x0),(0xfffffffffffffffffffffc000000f4ae1627c1,0xffffffffffffffff8509100000008082840641),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(20,2,73,0,4),(11,0,84,0,4),(68,0,27,0,4),(5,0,90,0,4),(2,0,93,0,7),(14,0,81,0,4),(66,0,29,0,4),(4,0,91,0,7)]
def g95A : List (List Nat) := [[]]
def g95D4 (j : Nat) : Nat := 0x41ddddddddddd0ddddd0b0d821955450ec660065551438e580dc965d0639e0976d4f418e7825db41d4239e0976d05508d587d8f415426621d4354140c67759956148239e1975d05209e3855c3414827221d4354120f095450d50482d8e1561541209e187d0550482d86174154120d8b7550d40483625d54350120
def g95D5 (j : Nat) : Nat := 0x304314204100504004004254a952a54a952a54a952a544891254a952a54a951254a952a54c093054a952a54a952a604891260a982a24c0f302449530553982a60f1830547891224026fb9ac1aa4ed70d89549dee4b26a73bdc96550e7db82caa1e5f65d4d43cbecb32a87675d26550ecfba2caa1dcf7259543bb6e0b2a87735c86550eecb80caa1f1f6555143e38caaa287e3dc95450ecfb82a8a1ee772597419eee0b2e833d5db53d067bbaac1a0cef7259350d3ac8a1ea1c755143d427abb683a857575d07509bae9b1aa1b55c7635426f3b286a84dc7650d50e3aa8a1aa1b5d8d615436bb1aa2a84f576d0550aeaeba0aa1b5d8f41542f8b8682a84df73595409dee4b2a81a7d95435034eb2a86a079b7050d40e72a8a8281e650d50502f4b84ca905cf7359520bd2e1aa2413bdd954483c6aa286907cb7050d20bceeab0a41b999561482f3bb2a2905e576d0520bcaeba0a417add150483b5aa2a0907695454120f96e6a8241f250d50483f0b8aa0907e16154120fc2a2a8241f8d0550482f5baa80905e97550120f52a8a024139dc965d06f0b8682907894350120
def g95H5 (j : Nat) : Nat := 0x71e00001a680000000001840038b8769400000000000050000000000000058f60d880000000000c88000000000001c800000000000000020600000000000000144800000000000000000000000000000499c580000000e300000510001
def g95D6 (j : Nat) : Nat := 0x104c1080508620044e0020f00198200c00fc21002114610081004308430803f94ff9a425252525254f256f252525254f4ff96ff9256f256f4f6f6fee25dede2525ce256f00b4252500a48f7a6f255f4f4f3525251500bf58f54bf58354bfd8d54fbd8954bfd8154bf59353bfd9153bfd9543bf59543ef55143f7d4d43f754d43f7d9543f799543f759543f719543f7d8143f758143fd54d51fdd4f41fd54f41bf59350df55350f750f50fdd0750bfd9150dfd5150df55150f7d8d50f750d50fd58550fd54550fdd0550bfd9540bf59540ef55140fe54140fb99520fb59520fb59120fbd5120fb55120bbd8954e755143bdd8151bd59741bd58341b7d8d50e750d40f350d20f958520f954520f9d0520fa54120fa50120
def g95H6 (j : Nat) : Nat := 0x4fe4eb07402f46f48d071c5d4cfcfa8940000000020415118b80034c80019140000024a68da03800241d001c928490780014c000000000241000107c0000030f000000000000086a10800000000000043f49c00040c00000204c8f4001cac000414000889004000000000c980000000a94d00000000008e00000000000004500000008868800000014368300000004bc0000014c4000001d0c0000004540008640010d40edc08000418001cb0000000826ca305b104000000000001c440000000000020e4000420000003c280015024dc0010b5c60000000020001d0acc0204c1
def g95D7 (j : Nat) : Nat := 0x58032c101080430210c83c44010b04032100cc043100a8a31a149e9a1488110c880003803fea9fd54ffa9ff54ffa87ff50fea87f503bc87dd43faa8fdd07da41f510
def g95H7 (j : Nat) : Nat := 0x244fa500000000000746000007a80000000030bf2482800000000000000000006b30be0dd000000000000106c0000000000357693001cc400503000000000000000000000000000000000f0e00000000000000000001480004800000007400301040ac00000000000000798001e5800000d04054000008420000009a0004d706000a23664000000000000000021c0000071c66c00242800000000002220004c91339e31141a0200000000000000028000000000000ad5500033e002da00094e00000000000000000000000000072da52000001330000000020f0000000000035e0000000030421000b20
def g95D8 (j : Nat) : Nat := 0x9c813f
def g95H8 (j : Nat) : Nat := 0x81800d800002080000000000000000004a0062000000074104000000001920050000960000002da000000000000029c016600000012a8
def g95L : Nat → Packing
  | 4 => (18,4,3,0,0,4,0,g95D4)
  | 5 => (70,3,3,0,0,7,0,g95D5)
  | 6 => (55,2,3,0,0,8,0,g95D6)
  | 7 => (14,1,3,0,0,8,0,g95D7)
  | 8 => (1,0,3,0,0,0,0,g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 3 79 1 10 5 1 g95H5
  | 6 => lookupWord 14 147 5 12 7 1 g95H6
  | 7 => lookupWord 11 172 4 11 6 1 g95H7
  | 8 => lookupWord 2 49 2 9 4 1 g95H8
  | _ => fun _ => none
def g95 : Forest := ⟨95,8,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 18=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 18=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_3 : block g95 5 3 48=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_51 : block g95 5 51 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 70=true := (@block_merge g95 5 0 3 67 g95P5_0 (@block_merge g95 5 3 48 19 g95P5_3 g95P5_51))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_13 : block g95 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 55=true := (@block_merge g95 6 0 13 42 g95P6_0 g95P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_6 : block g95 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 14=true := (@block_merge g95 7 0 6 8 g95P7_0 g95P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 1=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact g95B4
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=1091) (before_sound K122 V122) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K122 9 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V122 low95 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[(0xfffffffffffffffffff441079b0741614cd215,0x1040b0040214cc204),(0x82042df886815466ba,0x12450f488201544698),(0xb03f84e00f81ca5b348,0x3180e11d80945b300),(0x0,0x0),(0xfffffffffffffffffff3fc007000ff3f964d43,0xfffffffffffffffffff9040030222506800843),(0xc00007fff00dc23b9e4,0xfe49270b735dc233960),(0xfffff8000001e6b0eb8,0x6f8e3c0c400103204b8),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(38,0,81,0,4),(20,0,99,0,4),(3,32,84,0,4),(1,0,118,0,7),(66,0,53,0,4),(65,0,54,0,4),(2,0,117,0,7),(35,0,84,0,4)]
def g119A : List (List Nat) := [[]]
def g119D5 (j : Nat) : Nat := 0x17a5c06254ed7b92a7a1daf7254d43d3ec6a1aa5d354f52cca77b92ca9974d5354932
def g119D6 (j : Nat) : Nat := 0x1083b076108250a0b682da0ab6d055c16d060c16cae0b68305b2b4000800bf58b53bf59653bfd8953fbd8953fb18953efd4f43ef54f43efd4d43ef54d43bf58f52df54f52ef50f52bfd8d52dfd4d52df54d52ef50d52bf59732f754f32fbd4b32bf59532f754d32fb54932bbd8953bb58853bd58453be58053
def g119H6 (j : Nat) : Nat := 0x44000000000000b1000000000000a6000093000000a20000000000000000a5000000
def g119D7 (j : Nat) : Nat := 0x850145e420b118b9042c64210514414341b0110ac0454b0110841c40120f5ae26a01b960f8a04803fea7fe53fea9ff14ffea5fd52ff997f4cb7e87bd43
def g119H7 (j : Nat) : Nat := 0x14a0000023800000000000090e4b7055463c0000399000000000800000000000000000000001d200189f18008400094c0000000000000000000256c08970000051c0000185b440000000001d800000000000000000000000000000000000000000000000000e1000000000000000000000009540000000630c0000000000000000000cd000000000000080
def g119D8 (j : Nat) : Nat := 0xc9813f
def g119H8 (j : Nat) : Nat := 0x840000000000124007880000a2b180000000000000248000000007a14e63000000160000024
def g119L : Nat → Packing
  | 5 => (7,3,3,0,0,0,0,g119D5)
  | 6 => (26,2,3,0,0,7,0,g119D6)
  | 7 => (10,1,3,0,0,8,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 35 0 8 3 1 g119H6
  | 7 => lookupWord 5 111 4 10 5 1 g119H7
  | 8 => lookupWord 3 37 2 9 4 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 7=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_4 : block g119 6 4 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 26=true := (@block_merge g119 6 0 4 22 g119P6_0 g119P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_2 : block g119 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 10=true := (@block_merge g119 7 0 2 8 g119P7_0 g119P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 1=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1092) (before_sound K95 V95) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K95 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[(0x2913f8f78c82cc053253d20,0x448c0008112003900),(0xfffffffffffffffc2002328024d2898cdb1f19,0x889006588052898c991d18),(0x0,0x0),(0x341c7c33e15035622994a6e,0x4000331080460589022e),(0x7e0403c72a9c291d4492ee,0x10240d9a3288c2201448266),(0xffffffffffffffff8007fc063c6382e0a6e0d3,0xffffffffffffffff7327f9842e29106026c0c1),(0x3fff80007cf023c401ac594,0x2fdbf220407721860124490),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(82,0,41,0,4),(48,2,73,0,4),(42,0,81,0,4),(1,0,122,0,7),(9,0,114,0,4),(24,0,99,0,4),(17,0,106,0,4),(16,0,107,0,7),(65,0,58,0,4),(3,0,120,0,4),(33,0,90,0,4),(2,0,121,0,7),(96,0,27,0,4),(50,0,73,0,4),(32,0,91,0,7)]
def g123A : List (List Nat) := [[],[99,84]]
def g123D5 (j : Nat) : Nat := 0x140004302040410304000003000000000000000000000600000002219400000000000000000018002a761b5350e428fb805d9544cb1bd977255132f0d5450d524ca9b60b6594930c5f655ce524c21fe157690930e4f65949324c21fe1573d912087f855d9534821fe157650d20b6980d5152482da6165254120b6b83549504839ad8d5254120b698590950482da6163254120b69854c950483d254d3254120d697554940483ca5515250120ba985509404836add54250120da97550940482ea6113250120f89434c9404827ce0175949109f183dc1524427ce0175909109f3805d632442f8e01528c9109f3805d532442f8e01524c910bd1839c930442dce15724c110bd183949304427ce1d524c110bd3854c930442f4615324c110fc2524c930443f0549324c110
def g123D6 (j : Nat) : Nat := (if j<1 then 0x20882256822708214082256820ae8222e85208852148521482208850ae82140781aa5d0ae56940219263c0c8218ae218862185e0a0013fdc16594a7eba6c6a94fd70d8d529fceca1aa5b7d8d4354afbb8a86a94fd73d81529fee6b2c853fdc16590a7ebb6a7216bd6550e42f3ea6a1c85af50d6090a7ebb6a6a15bd74d4d429fee0b2c657bdc1528cb76a92c1194fd74d95329fae1b2a653fdd1654cb6fb9aca994ff70595329faebb22653f5c3644ca7fbaac8994ff70591329faecaa2657bdc9544caeebaa869979d5450d32bdae12926577dcd524cbb6aa2a4997cf7354932f9a86a92657bdc1524ca7ebaec0994fd74d8132dbaa7b0265b750f604cb76a96c09957f75581329fee0b2e433f5d3654c27eb96ca984fd75d91309fae5b22613fdc9644c33fb2aa8985dd7550d30f3aa8a1a613f5d7624c27eba6c4986dd53d8930dba87b12613f5da624c2eeb9cc4985f97098930afeeab12613f5da524c33fb2ca4985dd73949309feeca92613f5da424c2eeb9c849879d4390930bbeea99261775d5324c36fb2a64985df744c930bbae899261b7d91324c36eb2264987ce524c930f9aa4992613fdcd65c827ebb6a7905ed72d4f209faeca9e41b758d53c82f7b9aa5906ed6354b20bdaea99641bb59532c83e6a9a65904fd74d95209fae7b2a417b5ca654827fb9aca906fb70595209faebb22413f5cf644827fbaac8904ff73591209faedaa2417b5cb54482fab8ea8905f970d5120d7ac8aa2413f5d7634827eba6c69057f7558d20af8eab1a413fdd5634833fbaac69067c7558d209fee8b1a413f5db53482f6b96a6905f970d4d209faeca9a41b758d534827ebb286906bf6450d20dbac6a1a417ddc5434827ebb6a4905f970d4920bdaeb292417b5ce5248376b1ca4905fb7054920bdee8a9241dbd5152483b6aa2a4905ef7354920ddec6a9241bb58d52483f5b82a4905ed7590920bdae721241eb50e42482f6baa84907ad5450920bdaeb19241bb59632482f7baa64905ed754c920ddeca99241bb59532482f7ba264905ed744c920f9aa699241f350d32482dfba2c2904fd76d4520cfecba8a416f5d351482f6b96a2905f970d4520cfecaa8a41bed8d50483f5292a0907e95254120fd484a8241fa50950483f5192a0907e93254120bf6eaa02417e5d540483dcaa280907b94350120fd2a4a0241fa4c9404827ebaec4885fb7054910beaebb12217d5d462442fabaca4885f57394910beee6a9221fcdc152442fabac84885f5758c910fcaa5192217ddd532442fabaa64887d5534c910fcca499221f954932443f8baa60887f2724c110fe2e498221fc94930443f8a9260884f570d8543de2e2b00a51fdd563483b4a92a0907a94250120ecea5292217cdc1524427b3b0a4885d57314910be2e0292213d9da32443e8a9a60887d1324c110 else 0x19820448414004140840c0840008404104dc110081001020210c042035c104085041800818200800106000430c10006181020e30410086183041000410008084080060218602120850208e11408220882208821408220882270822088238513208ff2085020882385091409c3fc82256f5208e1208823848220882208823848214082208503ace120882208500ae502d88220882270820aeb614049a1482140b62d8d72088220882208820ae822088220882208d094082328820ae82208820ae820ae2ba0850208822082ba08822082b8ae820aec02d8afa08821402ba142b9408220882208820ae9c20885208852a48220849a14a29408521482270820ae82208501402ba082b8ae82)
def g123H6 (j : Nat) : Nat := 0x6000a6a391200099a0018f0000000034611bdb7b400070231ee408b0000007100000081b2840031900000000000f95898000000000000000000000000000529b654580060a00000358000000000000010740061c10c002eab070000000015d00029c00000000001ca800000a8c0079f000002c90006b4000000000000000000000000000000000000c180000000000000000000000000000018b8000000000059aeac000000000000000000000000000000001a8800509a4000000191000002a900000000000000000e290c648000a10000000006a0000000000031280000000000000fa80000000000140400000000002a89d70000000068800013d4980040c40038420
def g123D7 (j : Nat) : Nat := 0x400420810030804c32044c30010831400850810cc1410c61440131481800ca18004418c0431401841060800c21820811830050840481022840833040861440d70040c40021020430040a30021048c51032410830801030400830800c50c00842800820014c40440801060820481421020420040830c0083002080067084141cc014414a0030881411052010840450031400811050800c005314400304210010108408018308004610a18d0800461a30031808c11000460c51820631418c20c01630842230831630830370441081008c114a1230021570011041441978c10070021030801231040821230835c21031440425e31802040ca1030848c20030012432410230852410808c5263042005004043023042102023044cc20011020010c2002cc00811031800449428be93067e9189008e87aa8d003c8be8a688e49286a85283481c38a7fe7e67d47bc7bc7aa03c79e78c77469076274a7327207086f66d86c06a869067e67e1446666482346366185fa5e85ca5b85a058857655253451c4fe4e04c84aa4924924744564384204023d83c03a238a36634e3303183002e22be23429a27c24c2342162041ec1d41aa19217415c15c1441441441200fc0d80c00a20a208406603c03c04e03c01e01e000ffd8d52ff58d52ff50d52ffd8552ff58552ffd8152ff58152ffd4e42ffd4d42ff54d42ff59532ff59132ff55132ff54932ff58132ff59530ff59130ff55130ff98930ff58930ff94930ff54930ff90930ff50930ffd4f20ff54f20ff99520ff59520ff59120ffd5120ff55120ff58d20ffd4d20ff54d20ff50d20ffd4920ff54920ff4c920ff58520ffd4520ff54520ff4c520ff54910bf59652bf58e52bf58252bfd8d52bfd8152bf58052bf59642bf58e42ef50e42bf58242bf59632fb54a32bf58232bfd9532bf59532bfd9132bf59132f754d32f750d32fb94932fb54932bfd8132bf59721bf58321bfd9530bfd9130bf59130f754d30f750d30bfd8930f74c930bf59720bf58f20fb54b20fb4cb20bfd9520bf59520bfd9120bf59120bfd8d20bf58d20fb94920fb54920fb90920fb50920fb8c920fb4c920fe54120fe50120fd54b10fd4cb10bfd8910fdd8910fd18910fd94910fd54910fd14910fd90910fd50910fd8c910fd4c910bdd8543dbd4a52b758c52bd58452be58052bd58632b758f21fc4c110
def g123H7 (j : Nat) : Nat := 0x16ad6277c49f53e90f0500000016bd41d8000001c7d0004170000000f069a9000000000075291120000005d400000000000000000000a1900000000000000002d460000000000000f45e6010720ff45200000000000000000000000000157b90912a00000018060f0000b36800000000000042c8000000d62800000184820280000000000000002a56000000000391d86749500030c0000000000000000000011cc906000000000000000080d89f80004910000000000000000000395107a5a48002ce200095d0000000000a3c9c974bfe9ea027a6c000000000000209642c0000001053a9d00068c000061e60780031528090000000883a260000000070000e55b5b5d1600e1010000000000d4552c394e91b4a669ec00145b0000000608000bbe8000000000000000000000021f000000068172aea840006b1e8afc92006987722d9b0000000000000000000010400000000000001afc000000bb2b0d40000007dcd230000000000000000000000014d016d4173ad00024e562800050f78220005cb42cc0000000003a48000000a11800000000030d0000001a2fd30800182c0000006c0400000000000018200000000001c6d22e44b80000018b90000000c5b23aa3accb05009525a08003a81020000000029e0000004554000d0d00050cc660000753000064dc1f64b50878f91290003a8996f669c49b6a993ed66618e0a80006c31096af0c8fb271120003934559d1280034a60000000003504f7800049d0000000491fe8c00044a31100004008c4e1a0000d7cb3169f59190dd4b4947fb06928b3200600026c62a500000000000003610000000000f378ab38c73640000000a5a0000001a18000c57000000136d239905fcb8001c85000442080c000000745ecb2000000094000000000000000000004ca000000000000049de4ca000e2c79ac0000000000000d6a000e57000390e00000000000000006abaa63d1000000000014787b800000000000000000002954000a940000001b4b027c90386e8517b38000000000f384198001a8d20982640000000000000001427c268000000000715b0fc57164cb32201c888c4310a800000149c000000227408400049a1629414263212400181d000000164400000000000000008ac000000000000011d80009c200000010b505420c5e4c3808569504174001c1900071780000005d171aa4c56bb403e2404000088e1082013081184471000140400004c1230e550cad0146da0062
def g123D8 (j : Nat) : Nat := 0x1ab988011a601061988023967188030261108b3cc0214a7980411a6208043cc0208b30082208c71802302e31081012e310c202c6115ab18802ac610f71a3c4d96974b96421dccf5aa44ee531a05401fd43ff297f54bf8a5fe42fea17f8cbfa65fd31ff90ff487fa61ff20fe907f443ee21f510
def g123H8 (j : Nat) : Nat := (if j<1 then 0xf8e00000000000000023e0000000000000000000005cb000000000000000000000eef000d6800000000000000000000000000000000000000039400000000000000000000000000000000000000000000000000010b000000000000819000000000000000890444000000000000000000000000000000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000b300008de000000000000000000000000000000000000000000000da900000000000000000075846b000cd600000005b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b6100000000000000000000000000000000000012f90600000000000000000000000000000000000000000000000000000000000000000000075fccd0000000000000000000000000000000000000000000000000000000000000000001da7b4f594d700000000000000000000000000000000000000044e00000000000000000024673700000000000000000000002b000000000000000000000000000000000000653000000000000000603000a45000000000000000000000000000000000000934000000000000000000000000000000000f8f000000015000000a47000000000000000000292000436000000000000000000000000000000000000000f3f000000000000000000000000000000000000000000000000000000000000000000a35142000000000000000000b5c000a56000000463000000000000000000c890004120000000000000002269b38b9000541000000000000000688000000000000000000000000cee2b0000000000000000110000000000000000d40000000000000d9e000000000000000000000000000000000000000000000000000000000000000000000000a4c00068b000000000000000000808000000000000f16000069000000000000000000000000000000f3a000000000000000000000000000000000000000000000000000de20bc000000000000000000d13232966000000000000000000000000000a1d000000000000000000000000000000000000c14000000000000000000000000000000000000000000000000000000f1e000000000000c38000000000f62000000000000000000fd200000000000000000000000000000045e000000f5500000010d00000000000081a2490005220000000000000000000000000000000000000001e7000f00000000000000000000000000000000000000000000000721000000000000000ece00000000002d7cc000b0f000000000000000000000000000850000000000000000bc10000000000000000003270000000000000000000000000000000000000000000005049a30005004444000c1008 else 0x7c7000000000128000000000d230000000000000000000000000000000000000000000005cf000000c31000000000424000000000000000000000000000000000000000000000000000000000000c2a00012c000e5a000000000000333000000000000000000000000000000000000000000000000000000d39000000000000364000b91f0700000000000000000000000000000000000000000000000000000000041f000e6500000000000000000000000035400000000010100000000000000000065200000000000000000000000000000000000000000000000c00005100000030200000000000000000000000000000000000023c000000000000000000e6d00000000000048500000000000000000000000000000000000000000000000000000000000000000000000000004f00000000000000000024a00000000000001c000000000000000000000000000000000000325000000000000f3b00000076e000000000000000000000ba8000000000000000000000000000000000000000000000000000000329000000000000000a3d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000086f000000000000000000000000000000000000000000000000000000000000000000657000b4be6c00006a8b698a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000105000000e48000c20000000000000000000000000000000000000000000000000000000000000000000000000760000000000000000c2e000000000000000cd1a0900095d0001170c8411000000000000000000000000000000000000000000000000000000000000000567000000000000000a9a00000000000000000000000000000000000014300000000000000000000000000000000000000090a00000000000000000001820e00000000091b0000000000007b200000000000000000000000000000000000000000000000000024d0000000000000000000000000)
def g123D9 (j : Nat) : Nat := 0xeb7313f
def g123H9 (j : Nat) : Nat := 0x30900000000000000000000994000028200000000000000000000030005212f001eb000000000000000000000000000000002d000000000000000000000001ea00128000000000000000000000038d00000d1000000000000000000000000000000000804ac0000000000891a70030500000003ce00000000000000000000ba4000000000243000000038a0000000000000000000000000f9800000000000000000000000000063c0021c000000000000000000000000000003e300000000000020b4184000000000000000000000000000000000025
def g123L : Nat → Packing
  | 5 => (41,4,4,0,0,6,0,g123D5)
  | 6 => (199,3,4,0,0,10,0,g123D6)
  | 7 => (112,2,4,0,0,12,0,g123D7)
  | 8 => (17,1,4,0,0,9,0,g123D8)
  | 9 => (1,0,4,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 11 184 5 11 6 1 g123H6
  | 7 => lookupWord 52 533 5 13 8 1 g123H7
  | 8 => lookupWord 30 1239 2 12 7 1 g123H8
  | 9 => lookupWord 5 175 2 10 5 1 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 41=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 41=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_13 : block g123 6 13 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_61 : block g123 6 61 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_109 : block g123 6 109 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_157 : block g123 6 157 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 199=true := (@block_merge g123 6 0 61 138 (@block_merge g123 6 0 13 48 g123P6_0 g123P6_13) (@block_merge g123 6 61 48 90 g123P6_61 (@block_merge g123 6 109 48 42 g123P6_109 g123P6_157)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_8 : block g123 7 8 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_56 : block g123 7 56 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_69 : block g123 7 69 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 112=true := (@block_merge g123 7 0 56 56 (@block_merge g123 7 0 8 48 g123P7_0 g123P7_8) (@block_merge g123 7 56 13 43 g123P7_56 g123P7_69))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_2 : block g123 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 17=true := (@block_merge g123 8 0 2 15 g123P8_0 g123P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : block g123 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : block g123 9 0 1=true := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=67) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffc0181f0cc7b1f091f11,0xfffffffffffffffffff8020020041947000a11),(0x0,0x0),(0xfffffffffffffffffff80e000f3281c0d7891f,0xfffffffffffffffffffc06a4b92c19c0d58915),(0x107e104f24215439e6,0x400e144922801411a6),(0x3e0801f904bc0aa52e6,0xe04906d042002a10e2),(0xfffffffffffffffffffc00ffe002042aefc469,0x69df1c8124428ebc448),(0x7ff000023903430e498,0x3190000028438006408),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(9,32,84,0,4),(80,4,41,0,4),(32,0,93,0,7),(4,0,121,0,7),(17,0,108,0,4),(41,0,84,0,4),(24,0,101,0,4),(64,0,61,0,7),(52,0,73,0,4),(16,0,109,0,7),(1,0,124,0,7),(84,0,41,0,4),(72,0,53,0,4),(44,0,81,0,4),(8,0,117,0,7)]
def g125A : List (List Nat) := [[],[96,82,67]]
def g125D5 (j : Nat) : Nat := 0x20c080000014303d25493254130cb764dc553482dae0d5254120e696354950482da6153254120f49534c950483d8dc95254110
def g125D6 (j : Nat) : Nat := 0x1810820108082302800c10008080101e204008099e20800c00264002000800210400043020028f478f0ce851e1fafd0010c8678219e1c4ce59a98f0002190d247e3c1e000782199086502810c002f0a0027ebaec0994fd73d89509fcec992a13f5cb654c2efb9aca984fd75d8930bbeea99261b7d95324c3e6a9264987db7354130df6c4a8261de549504c3ec992a0984ff7359520ddee4b2a413fdd5634827ebb2a6905f77154d20bdee6a9241bb58d52482f7baa64905ed754c920ddaca99241f354d324835fb22a2906bf644c520df2c6a8241de54d50483f5b92a0907e93254120fe6e4a8221fc5c950443f8b9260884bd75d9120ed2a4a8241dc54950443e899260887315454110
def g125H6 (j : Nat) : Nat := 0x200000002f15802a80001c98fec9485d0600010
def g125D7 (j : Nat) : Nat := 0x3120030401831400844c10c61120043010041174e20401622c10c12021430460059c30401020040441430401051841630401840010cc1412001591840c50401cc057004185ce20590070570032c00802c20010b9df30042c50850420400b20010c4c80044ab036c32f4b8acaab28e9aa529021c7f9e06f1925e95649908360c02b89c2288a0d88a1b05a1203607800ff58132ffd8950ff58950ff4c950ff54540ff59530ff58930ff54930ff54d20ff54520ff4c520bfd8132bfd8950bfd9530bfd8930f74c930fe54130bf59520bf58d20fb54920fb4c920fe54120fd54b10fd4cb10bfd8910fdd8910fd54910fd4c910afd9120ed95310ed95110ed55110fc54110fc4c110
def g125H7 (j : Nat) : Nat := 0xc000000691240000000000000154c00000000000000000000000000000000000000228001868000000014a80013400000000e2c00000000000000000003960000000000000000000000000007170000038c0000000000018f000001680000000000000000000181800000e38000000000000000000000000000432000000000000030900000000000000000000000000000000000000000000223000003a880000000000000000000000000000000000000000000000000000000003440000000000000000000000b7c000000000038380000000000000000000000000000000200000000000000000000000000000000000000000000625000000000000000000000000000000000000000000000000000000000000000000622000000000000000000000000000000000000000000000034f74f000018000000000000000000000000000000000003d4000000000000000000000020000000000000000000000000000071071400361800001c808e8000000000000000000000000437b200000000000000000000000000000000000000000000000000001f700000000000000482000000000004b2000000000000000000000000000000000000000000000000000000000000000001e2c00000c12000000000000000000011000000000000000000000000000000000000000000a3e0000000000000002e81000000000000000000000000000000000000000000000000000000000000000000b84000000000010700000000048400000000001098000000000000003005
def g125D8 (j : Nat) : Nat := 0x999c94040384013748088d084a3ce4100d72a002112a404031441cde601c4300449286b00a392820163b0d79b8d7ea5409607c1f007f4cbfa83fd31fe90ff543fa81fd30fe907f443ee21f510
def g125H8 (j : Nat) : Nat := 0x5c60012180000000000000000000c3e8a000425470000000000038c800d9c634006046120018bcc30000000000019a000005930000000000000000000420d2a000000003b0000007080000014c00000000000587001e04a600000078400000000002c60006ac000000000000000000000000147000a3a00000000d0617c002d0a040000000000186c0000000000245000000000000000000840000000174400000dc0000aaa9f93544348800000000000000010140054f00000000000001a7800000d2c00000000001506e900000172c00000a0111c0000000000000000b17f2800000d0100
def g125D9 (j : Nat) : Nat := 0xea97321bf
def g125H9 (j : Nat) : Nat := 0x4140000004cc00000000000290000000b8000000000000000e00001880000000000000680032a00a0803e463ea0000000588000000000000000000000000000000120e5000000000000ae88000000000000000084000024c000000001c0
def g125L : Nat → Packing
  | 5 => (7,4,4,0,0,5,0,g125D5)
  | 6 => (38,3,4,0,0,9,0,g125D6)
  | 7 => (34,2,4,0,0,10,0,g125D7)
  | 8 => (11,1,4,0,0,9,0,g125D8)
  | 9 => (1,0,4,0,0,0,0,g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 18 5 8 3 1 g125H6
  | 7 => lookupWord 10 415 2 11 6 1 g125H7
  | 8 => lookupWord 10 166 2 11 6 1 g125H8
  | 9 => lookupWord 3 83 3 9 4 1 g125H9
  | _ => fun _ => none
def g125 : Forest := ⟨125,9,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 7=true := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_1 : block g125 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_5 : block g125 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 38=true := (@block_merge g125 6 0 1 37 g125P6_0 (@block_merge g125 6 1 4 33 g125P6_1 g125P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_6 : block g125 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_23 : block g125 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 34=true := (@block_merge g125 7 0 6 28 g125P7_0 (@block_merge g125 7 6 17 11 g125P7_6 g125P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_2 : block g125 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 11=true := (@block_merge g125 8 0 2 9 g125P8_0 g125P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P9_0 : block g125 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B9 : block g125 9 0 1=true := g125P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=1027) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 10 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),(0xfffffffffffffffffffffe0201b0fed41e65c3,0x2244b04654162542),(0x830ec00739b1c258,0x300e21739b04210),(0x103f0ff040a2cb124,0x310f1040a0ca020),(0xfffffffffffffffffffffe7c010007ef4d9e29,0xfffffffffffffffffffffe0c01042082099829),(0x18001fff821f358a6,0x1c8890eb9a1e15884),(0x1fffe000032c22dd0,0x1f0ee08c0044205c0),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(20,0,106,0,4),(10,32,84,0,4),(72,0,54,0,4),(42,0,84,0,4),(2,0,124,0,7),(8,0,118,0,7),(4,0,122,0,7)]
def g126A : List (List Nat) := [[],[49,100]]
def g126D5 (j : Nat) : Nat := 0x4f77159653
def g126D6 (j : Nat) : Nat := 0x1002002006d60bf59653fdd8553bdd8553bd58453be58053
def g126H6 (j : Nat) : Nat := 0x800000000
def g126D7 (j : Nat) : Nat := 0xb0f44063d2c01e1db0c8406807807f94ffaa7fc53
def g126H7 (j : Nat) : Nat := 0x62000000000000000000e100000000001400d3007800006000000000
def g126D8 (j : Nat) : Nat := 0x58f117f
def g126H8 (j : Nat) : Nat := 0x138000000003a00000000184000f000000
def g126L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g126D5)
  | 6 => (5,2,3,0,0,5,0,g126D6)
  | 7 => (3,1,3,0,0,7,0,g126D7)
  | 8 => (1,0,3,0,0,0,0,g126D8)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 8 0 6 1 1 g126H6
  | 7 => lookupWord 1 31 0 8 3 1 g126H7
  | 8 => lookupWord 1 19 0 7 2 1 g126H8
  | _ => fun _ => none
def g126 : Forest := ⟨126,8,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5_0 : block g126 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B5 : block g126 5 0 1=true := g126P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_0 : block g126 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_3 : block g126 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B6 : block g126 6 0 5=true := (@block_merge g126 6 0 3 2 g126P6_0 g126P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : block g126 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B7 : block g126 7 0 3=true := g126P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8_0 : block g126 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B8 : block g126 8 0 1=true := g126P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact g126B5
  · exact g126B6
  · exact g126B7
  · exact g126B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 9 := lower_forest (g:=g126) (i:=0) (hints:=34690112) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 9 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0x64ce3fce03c39b9ffe041541d01c1c4095d20,0x6188003c01981b00000004008140004c20),(0xe0710381144fc63e0710890840043e08d34fa3,0xe573c9a8546d0f38d750090840043608434da1),(0xe081fc0218700bc078000670024e1032ed4cb1,0xe1610836786fd07e40047000461032cd4ca0),(0x18fe00041f800c007fe37180e092e038619acc,0x8f4000015800c0264640300d08670106112c4),(0x19000007e0000fff801d869f13623ec32072dc,0x1a04000001008006000492051ba0488120125c),(0x1e000007fffff0000011f8d06c4900b79ea03e,0x12081247aa02f0050081f4d3295900a79ca01a),(0xfffffff800000000001e00e380fc030d56a541,0xe50a9e77c8030021809b60820019060c12a101),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(82,4,41,0,4),(11,32,84,0,4),(52,2,73,0,4),(73,0,54,0,4),(9,0,118,0,7),(32,0,95,0,9),(4,0,123,0,10),(21,0,106,0,4),(43,0,84,0,4),(28,0,99,0,4),(66,0,61,0,7),(20,0,107,0,7),(2,0,125,0,10),(1,0,126,0,9),(8,0,119,0,9),(100,0,27,0,4),(5,0,122,0,7),(3,0,124,0,7),(46,0,81,0,4),(69,0,58,0,4),(19,0,108,0,4),(26,0,101,0,4),(37,0,90,0,4),(36,0,91,0,7),(18,0,109,0,7),(74,0,53,0,4),(10,0,117,0,7),(86,0,41,0,4),(13,0,114,0,4),(54,0,73,0,4),(34,0,93,0,7),(6,0,121,0,7)]
def g127A : List (List Nat) := [[]]
def g127D5 (j : Nat) : Nat := 0x20f5d835343f04b22a7c2c5d994645801d943cd2348d0b203b2c6a1e4a8a7e999650d40482d50d910cc2ac8a02211acee9962594350110
def g127D6 (j : Nat) : Nat := (if j<1 then 0x20c3b25f9661943482bcba36178458120af2e8d95e11604826e9a3e598458120af86878561160482bcba361584581209baea585d9160482ecba36176458120bb86878559160482eaba46156458120bb2e8d8559160482ecba36116358120bb26938358d604826e9a6e6143581209bae999850d604834e8a76594358120baae998450d60483b898460d4358120fa25918350d60483e898458d4358120af8e8595e1940482baba46558650120af2e8d9561940482be3a16558650120eaae5b94619404832eb966198550120cf8e1b91615404833e186e4585501209eaea58599140482eaba66156450120be8e8585591404832eb966198350120daae596460d40483aab8659183501209ea6939858d40482eaba66516350120d6a29d9650d404836aba66594350120be2e8d8650d40483aaba66194350120ee2e8d8650d40482f89a6e0d4350120ee261b8350d40483e8b9658d4350120af8e8183e0964442be3a064f82591108fc6a684e0163442af1a6a138058d10af8e8984e0163442bd3a35db8058d10abc69a94e0163442bd1a3a538058d10af8e8994e01634433e3a26538058d108fc6a674e0163442bd1a39d38058d108fc6a664e0163442bd1a39938058d10af8e8964e01634433e392e418650d10cf8e8b90619434422f7a96188650d10cbc61990219434423f3a06636450d109f4e8193d9143442ea5a22196450d10bac6808659143442ed1a02196350d10be46826458d4344379264e416350d10de45939058d43442f33a45956454110dd86579259150443761a5e496454110dd859792591504427e3a26536354110bd8e896454d504427e3a26594354110de8e5392619404432f3a96188650110de46919321940442be3a261b8550110cbce5a8661540442be3a26198550110af468c8661540442be1a22198550110bace998559140443ab0866156450110fa8e1b92591404437a195e496450110de864f92591404427b3a961a5450110de46199395140442fa3a26195450110eac6188655140442f91a32195450110be868886551404436b3965918350110eace196460d404427b1a4e6163501108fc6939858d40442eb1a6a516350110bace999458d40442f91a39916350110dcc61995d0d404436b396d914350110dace596450d40442fa3a259143501109ec6a69650d404436b396a594350110be468e9650d40442fa3a26594350110dace999650d404437a3a265943501109ecaa49650d40442bb2a82594350110dac6589650d40442fa1a225943501109ec6a68650d40443ab386a194350110be468e8650d40442f93a36194350110be8e898650d404427b2a92194350110be468c8650d40442fa1a22194350110be469b8350d40443b9186e0d4350110fa4e596350d40443e909658d43501108bcea58621940442ea1a22196450110 else (if j<2 then 0xa0d068a0400d068341a0d068341a0d06860300d06834200d0025e5a0e4575dc964a79e8575603725929eba05d580dc964cabe5b94603725929eba05cd80dc96497968391617725929e7a161583dc964a79e8585603725929cfa365580dc964a79e8595603725929eba065580dc964a7ae8193603725925e5a0e4964dc554a79e8964603715521eda9a1f8259153a7ae8187e096454e9eba065f8259153cd6655936006454f1ea976498019153a79e8585e097650e9eba0617825d943a7a68392e017650f8b976651801d943e365d9936007650f8f176645801d943cec651916007650e9e7a25db815d543a7968876e057550e9f1a01db815d543da668d901d96450f6b1a16407659143b2b688765d56450ecb9a01d97559143d2e5d9901d95450f699a46407658d43db4685901d96350ee99a01d95458d43b2b688765917050ecb5a11d9645c143a7968775e09745829cfa35d7825d160877ea57560c7458389d655d1831d160a73e8d75608745829d7a35d5811d160d275d5931d1645834ad756487459160da65939058d43582e99a09d16350d60aae69286601435821eda9a1f8259150a73e8d87e09645429cfa365f8259150a73e8d76e0964543359956418319150a73e8984dcf635429cfa3617825d940a79e8585e09765029e7a25db815d540a7568c76e05755029e5a21db815d540b2b688765d5645022bfa96188650d40cae6199021943502e99a02196350d40da6691931d9605036996564c8458140bac6848759160502eb3a16556458140bac6878559160502e9ba36156458140bace8575591605036a995e496458140daa64f92591605036b164e455458140ba668c7655160502cb9a69937358140f2ae8964dcd60502e99a3a516358140f265937350d605026b9a9a594358140ba668e9650d605036aba26594358140ba668c7650d605020ffa9618865d130c37e5b9361d644c31db93e418759130b2b688965d1644c2cb5a12597459130d66e4f905d1644c22dfa96188650d30cb661990219434c2e8da22196450d30ba568486591434c2e99a02196450d30d365d193d91604c34b9965d26458130e2e2a174591604c3c9ba35d16458130f2a5d392591604c36c993e496458130f265d26458d604c3c99745916358130bb2e896458d604c2ad9a8a516358130bb2e899458d604c26d9a9a116358130b3669e8458d604c2ecba26116358130d362a57458d604c38d8a85d16358130ba66929650d604c36cba26594358130ba669a8450d604c2e9ba661143581309b66a76450d604c2e99a69914358130fa2e896450d604c2f4ba25915354130b5669c6454d504c2f49a21915354130bd46846454d504c2bcba3655809d920af2e8d9560364482bcba06558319120a7ae9d64e01534829e9a71938054d20af268c64e0153482be1a11938054d else 0x2a0e8c0f8c0d16080e0b2201040102c882c2020100010000e0808060802080038001068341a28068341a0d068341a0d068341a0d068341a0d06834500d068341a0d068341a8241034500d068341a0d06834500d068341a0d068341a0d068341a0d068341a0d06834500d068341a28068341a0d1e8f41a18068341a0d06834400d068341a0d068341a0d068341a0d068341a281e8341a28068a01a0d068341a0d100341a10068341a0d068341a0d068341a0d068341a0d06934f40d068341a0d068a01a0d068343028080341a72269881a0d268341a0d350341a0d06834500d06834c40d068341a0d068341a0d068341a0d068341a0d068341a0d068341a0d068341a0d069548a0d068341a0d140601a0d140a0500d268348a3d068c01a0d068341a0d068341a0d068c01a28068401))
def g127H6 (j : Nat) : Nat := 0xd015f300000000000000000034b2000000f10000
def g127D7 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then 0x95450110fd9432a8a0221fb18655140443f610caa280885fc65b8350110df8c3706a0221fb164e0d40442fe72cc1a80886fce198350110df8c3306a0221fb26460d40443f62c8c1a80885fc6636350110bf9cc2c6a02217f19858d40442fe728b1a80887eca516350110fd8ca2c6a0221fb26458d40443f62c8b1a80887f460d6350110fd8b22a6a0221fb186d0d40442fe72ca1a80885fc6594350110fd9b2286a0221fb16450d40443fa2c6a1a80887ece594350110fd94b286a0221fb19650d40443f612ca1a80887ece194350110fd943286a0221fb18650d40443f610ca1a808847b643825da64af3c8aebb92c95e791617725933cb04c0ae032778609815c064af3c92c9b8aa91ed90e0974d8e37f30ba0e8b1c7b643825d94387fcc2ec3b2878f9766007650ed5b243b2c8a1dad6447659143b5cc80ecb228765d951d96350edb3203b2c6a1ce7a625458d438dfcc2e83a2c199d7460c74582d3b263a2c8b05ab6487459160d5cb2301a1ac10ff985d876502d5b243b2c8a05ad6447659140b3cca8ecb02816d9931d960502d7329b2ac0a053e25d6558140b9cca908b02817999321160502d732d322c0a05aee4d6458140f55c92c8b02816b99695160502f33272a2c0a072e5937358140b5cca6c6b02816b996d0d60502e732ba1ac0a05ae6594358140f4cb1a86b02819db83e01764c33b707c02e8985b664f6458130e5cba2c8b02616db9458d604c39b2e8b1ac0984f62614358130b6ccb286b0261e996450d604c37c322c00c8905ea6426450d20bf0c8f0ab02417cb9361560482dd728b2ac0905bae598458120b754c6c8b02416e993d9160483d5708b22c0905f8e455458120b75ca2c6b0241ecb8358d60482dd32ca1ac0907aa5914358120f64b1a86b02417ab94619404835d72cc3280906eae518650120bf1c8b0aa02417aa9899140482f532732280907aae196450120bf1c8aa8a02417ab9655140482f572ca1a80905ea6594350120dd5c3286a0241ba98650d40483f1706a1a80907e258d43501209f3c930d3a2213f39060f644427cf24c34c8886f864980191109f3c9309b1a213f194e0163443762c8c0686884f9e498650d109f9c830ca1a217b19099143442fa720b1a86885dce516554110db8b2f08a82217e392591504435e70d43280885ec6528650110bd9ca30ca02217e392619404435e30c43280885dc6548650110be8c990ca02217e19221940442f6329b2a80885eca626450110bd8cb4c8a02217b19399140442fc724b2280887ace196450110f58432c8a02217b39359140443f4724b2280885ec65a5450110bd8ca6c6a02213f39858d404427e130b1a80885ec65b4350110bd9cb286a02217b19650d40443f2706a1a80887e458d4350110bc4c9ca8a024172995d0d40482f23272a280885cc6574350110 else 0x905fae615458120bf4ca706b0241be984e0d60483dd2c9c1ac0906fa6118358120f74b2306b0241ee99458d60483dd308b1ac0906fae115358120f75b22a6b0241ee96454d60482fd730a1ac0905fa6614358120f74cb286b0241fa98450d60483f9306a1ac0905fa64f8650120df4caf0ca0241be993e1940483f5728c3280905fae4d8650120df5cab0ca0241be995619404837d726c3280906fa64d8650120bf4cb70aa0241be986e1540482fd72cc2a80906fae198550120df4c330aa02417eb9859540483f530b32280907eae156450120fd4c2ac8a0241fab8655140483f530caa280905fa65b8350120df4c3706a0241fa964e0d40482fd72cc1a80906fae198350120df4c3306a0241faa6460d40483f52c8c1a80905fae616350120bf4cc2c6a0241fa99458d40483f9306b1a80906fae195350120df4c32a6a0241faa6454d40483f52c8a9a80907eae594350120fd4cb286a0241fab8650d40483f530ca1a80904fde59839d110df8cb3013a221bf193602744427eb27c32e8884fd65b835d110df8cb30132221bf19360264442f6f28b2ac8885fce418359110df2c2f04b2221be583e09644437cb2bc12c8886f95978259110df2c9f04b22217d7935d963442deb2d422c6885fc6428458d10b7bcb308b1a217e79261163442fe720c22c6884fd6627458d10beac9ce8b1a217f1909d163442fab27322c6885fc6426458d10bf3c92c8b1a217f194e01634437e509c02c6886fc6138058d10df8cbf00b1a21bf176e01634437e529c02c6886fc6538058d10df93a700b1a21bf174e01634437e4c9c02c6886fc5938058d10bf3c92c8a9a21bf196603434435ef0d43286885ed6528650d10bf3c930ca1a217f390619434435ef2cc3286886f9e498650d10df9c830ca1a213f698219434435eb0c43286885f96488650d10bf8c810ca1a213f598d91434435ef0db2286885f564f6450d10bdacb4c8a1a21af78659143442fcf24b2286887ade196450d10f5a432c8a1a21fa79259143443daf0cb1a86887b52196350d10fcb322c6a1a21f956458d43443fa720b1a86885fc64f6454110fb8caac8a8221f716559150442fe726b22a0887f8e496454110bf8ca6c6a82217f39458d50443ee6c8a9aa0887dc5915354110bf9cb286a82217f19650d50443f62c8a1aa0887f458d4354110bf8c9f0ca02217f193a1940442fe728c3280887ece518650110bf9c9b0ca0221fe39261940442fe32643280885fc65b8550110df94370aa0221bf186e1540442fe72cc2a80886fce198550110df94330aa0221bf186615404437e10cc2a80885fc6636550110bf9cc2caa02217f198d9140442fe327b2280887ec61a6450110fd9c32c8a0221fb19559140443f670ab2280887ec6156450110fd8b2ac8a0221fb19359140443f630d2a280887ece1) else (if j<3 then 0xdb0fc12c89876b5d38259130de6c1f04b22619ed97e09644c33daedc12c89867b5d78259130cf6ba704b2261bcd93e09644c33baeac18c89867b5d58219130cfabab02322619f975600644c2dbb2d422c6985f66428458d30b6fcb308b1a617cf92611634c2fb720c22c6986772617458d30e6fcb2e8b1a61cdc965d1634c3bb720ba2c69857765e6458d30eceba4c8b1a61d9d74591634c2f9f24b22c6986f66138058d30becc86c8a9a617cf92591534c2bbb2e322a6985f36486454d30beac88c8a9a617d990191534c35bf0d43286985e76528650d30becc850ca1a617cf92619434c2fb720c3286986b7e598650d30de7c930ca1a61bdb90619434c27bd3043286986b76188650d30be6c910ca1a617d591219434c2fb3204328698776e417650d309eecc6c8a1a615dd97d91434c35bf0db2286985f66436450d30bcecb4c8a1a61d9d76991434c35bf0cb2286985f3e496450d30f4fc32c8a1a61e9c86591434c3b3aecb2286987e3e496450d30beccb700a1a61bd986e01434c3f32c9c0286985be65a8458130becc9d08b02616fb96611604c2fb726c22c0985fae498458130cfc4c2e8b0261cfb965d1604c39f12cba2c098776e4d7458130e7cba6c8b02615f997991604c2df32d322c09876e5d26458130becc9cc8b0261db974591604c2fd724b22c09873e5d16458130f6cc9ac8b0261eeb92591604c2fb329c1ac0987b65938358130eecba2c6b0261eda6458d604c3db2c8b1ac0987b6a516358130f6cca2c6b0261eda8458d604c3db308b1ac0987b6d915358130f6cb22a6b02617db9650d604c3db52ca1ac0985f66594358130f6ccb286b0261f9a8450d604c3f3308a1ac0987b6d914358130fcd32286b0261ed96450d604c3f32c8a1ac0985f664f6454130becc9cc8a82617eb92591504c2bf32e322a0985f664c6454130bf4c90c8a82617f191191504c2fb728b1aa0987d6d915354130fad322a6a8261f596454d504c3eb0c8a9aa0985f6e594354130beccb286a8261f9a6450d504c3f32c8a1aa0986fa655809d920df4cab013a241be993602744837d32ac06c8906fa6558099120df4c9b0132241bcd9560c644837d32ac00c8905bbe598458d20bf4c84eca9a417eb905d953482fd3213a2a6905fa6436454d20bf4c84c8a9a415ef9759153482bdb2e322a6905f364c6454d20bf2c88c8a9a417e990191534837d4edc02a6906fa5db8054d20df53a700a9a41be974e01534837d6c9c02a6906fa9938054d20df4b2700a9a41be864e01534833d92ec3286906bbe598650d20f57c32c8a1a41ecf8658d43482fd329c2ac0905fae518558120df4c2f08b0241ee965e11604837d32bc22c0907bae598458120df5c2b08b0241be98561160483dd2cac22c0905fae4d8458120f74c2ec8b0241eeb8559160483dd30ab22c else (if j<4 then 0x1163502f3b27322c6a057be497654d40d9ebb30ba1a813fb9061943502bbf26bb286a06afe1b6450d40e5fbb6c8a1a81abf865914350397eecb2286a05ebe496450d40aeecb6e6a1a81d9d64dcd435027f32dc0286a06ee5938050d40decb1f00a1a813bd98a1943502b7b2f43286a06afe1a8650d40bcec9d0ca1a817b990a1943502f5f24c3286a05eee418650d40d5fcb30ca1a81baf926194350377720c3286a04efa608650d40adf4b90ca1a81abd8621943502f5b2443286a05ed6448650d40bdcc810ca1a813bd989d943502b7b2f3b286a072fdda7650d40bcec9ceca1a817b9909d943502f3f26bb286a05ebe497650d40e5fcb2eca1a81d9f935d943503b5f24bb286a04efa607650d40adf4b8eca1a8179d931d943502f5b243b286a05ed6447650d40bcecb6e6a1a81d9d76dcd43503d3f0cb1a86a07a72196350d40ecfbb2c6a1a81d9d7658d43502f732dc0286a06ee61b8050d40fcdb9f00a1a81f9963e0143502fe32243ac0a05be64f7658140b7d4c0ecb02816f9931d960502fe323c2ac0a05eee518558140bedc9b0ab02816fb965d560502fe722baac0a05bee516558140f5dbb708b0281eb965e1160502f752e422c0a07ae5948458140b7cc9ec8b0281eb96599160502f7327322c0a07aee116458140f5dbb2c8b0281eb96559160503d710eb22c0a07ae6556458140f5dc2ac8b0281eb98559160503d76eab22c0a07ae5d56458140f5cc9ac8b0281ebb6455160503d72c8aa2c0a05fce455458140bddcb2a8b0281ebb7655160503d70ecaa2c0a07ae5938358140f5cb2306b0281eb964dcd605039f6c9b9ac0a076e9937358140e7cb26e6b0281db964dcd60502df72cb9ac0a073edd97358140e7c3b2e6b0281eb9645cd60503d74c8b1ac0a07ae5916358140b7dca2c6b0281eba9458d60503d7328b1ac0a07b6e0d6358140f6cb9ac6b0281eb96454d60502df32ca1ac0a07aed914358140f5cb2286b0281ddb7350d60503db2c6a1ac0a05eee594358140f5d4b286b02817b99650d60503d732ca1ac0a07aedd94358140f5c3b286b0281f998350d60503f36e6a1ac0a07e658d4358140a7ecb508bb2615dd93a11764c2bf321422ec9853fe59845d930aefc9b08bb2615ef92611764c2bf720c22ec98577653835d930c7fc350cba2615bd94a19744c2bbb27432e89857e642865d130aefc9b0cba2615ef92619744c2bf720c32e89863f618865d130af6c910cba2615f591219744c2bbb2dc1ae89857e65b805d130eedc1f00ba2614ff965d3644c33bae8c1ec89867e5d180d91309f7c930d322611fd985da644c337b0cba4c8986775d983991308ffcb30eb22618ff9661d644c33bf26c3ac89867be498759130cfdc830eb22614ff965d1644c397f2cba2c89872f2597459130ecfc9ae8b2261dbb905d1644c33 else 0xc11fd94a1d435825ff2cc3a86b04fe6438650d60b5eca50ca1ac13fb90619435835df24c3286b06bee418650d60aeec9ee8a1ac16bd969d143582d7f2cba286b04bf6636450d60b6ec9ec8a1ac16bd9699143582f732132286b07abe496450d60ecf3a2e6a1ac1d9d745cd43583d3ac8b9a86b07a79916350d60f4eb22c6a1ac17db9058d43583d3ce8b1a86b07a75d16350d60f6dc82c6a1ac1afa86601435835f30cc0286b07ae5918050d60f6cb1b00a1ac14fd96dd3645427df24c34c8a856f6537699150adfca2ed322a15df935da64542e7f28b2cc8a8577e4d8759150adeca6ecb22a15bf945d964542bbf26bb2c8a85cfe516559150a7ecb6e8b22a19ee87e09645433db0fc12c8a86db6178259150cf74bf04b22a19ed97e09645433deedc12c8a867b5db8259150db6caf04b22a1b6d65e09645433dee9c12c8a8677a5d8319150ceecbb06322a1b5d9560c645437b320c18c8a84fee4d8019150df4c9300322a176f9259154542bbb27326e6a8577e4d64dcd50af7c92c9b9aa15dd9319373542bdb24326e6a857d64464dcd50afcc80c9b9aa13ef92613635433bb09b9ec6a85dbe496454d50baec98c8a9aa176d9219153542eeb22322a6a85de6406454d509f7c930ca1aa1d9e64dcd43543b3ac9b9a86a857be497654f40afbc8b0bbb281baf84e0976502b7f28c2aeca0577e4d855d940afbc8b0abb2815fb906157650397f0dc22eca057ee41835d940e77c3704bb2819ef85e09765033db0bc12eca076be13825d940cf7c1f04bb2819ed83e09765023fb27438eca063fe61761d940dceca3063b2811fd989db75502bdf24bb6eaa063fe1a765d540c7fc32ecbaa815ef925d9755023fd303b2eaa057764c765d540af6c90ecbaa819f776e05755033ecedc0aeaa067d5db815d540cfa3b702baa813f990e11655023ff26c3ec8a047f66375d9140a7fcb2ebb22813bf985d6645029ff2cbaac8a067bdd78259140cf6baf04b22817b79161564502f7720c2ac8a05afe597559140e5e3b2eab22817b7915d564502f7720c1ac8a07abddb8259140dd6c2f04b2281bad83e096450277f30bb4a8a06e75d98395140bd7c92c8aa2819f776e05545033eaedc0aa8a06ed5938155140bdcc84ecaa2817af925d95450397aec3b2a8a05e764c7655140bd6c90ecaa2811fd989db73502b7b293b6e6a057be4976dcd40adeca50db9a815f990a1b735023fb31b26e6a057e64364dcd40adecb4c9b9a815ef9259373503b5f24b26e6a063fe1a765cd40adeca4ecb9a818ff865d973502bdf24bb2e6a047fa60765cd40af6c90ecb9a815f5911d97350357f0cb22e6a072fdd9645cd409deca70eb1a811fd94e1d635029fb2d43ac6a047f65a8758d40a7fcb30eb1a815dd93dd963502bbf26bb2c6a04fe6438458d40b5ecb508b1a816bf966))) else (if j<7 then (if j<6 then 0xc86edb22871fd98dd76450e9ff2cbaec8a1cf7e4183d91439dfcc2eb3228779f935966450e9fb21bb2c8a1d3fe597559143cf7baf04b22879ed75e096450e7db21c12c8a1daf6437659143b5ec80ecb228779f936156450ef6f22c2ac8a1dafe597559143e5e3b2eab22877b7915d56450ef3f26b2ac8a1fabddb8259143dd6c2f04b22877ad90e096450ef3f26c02c8a1eebe0980591439dfcc2ed2a2877af925915450f3eeedc0aa8a1e7d5db8155143ddab2702aa28779d939d95450ef5f24bb2a8a1f2f5d87655143bd6c90ecaa2877b9901d95450edbb21bb2c6a1db7a607658d43b6ec80ecb1a8779f946156350e7bd31baac6a1db7e597558d43bebc8aeab1a87e9f76e116350fd3acbc22c6a1de7a5c8458d43f4eb2908b1a87e9d659916350ef3b21322c6a1fa7dd96458d43f4eb2ac8b1a877d7915516350ef3f2caa2c6a1fa7dd95458d43f4e3b2a8b1a87b9e64e016350f73ac9c02c6a1c7f66276dc143adeca4edb82875ef925db7050eb7b29436e0a1d7764e86dc143af7c930db82879ef9261b7050e3fb31b26e0a1d7764f64dc143adecb4c9b82875ef925937050fb5f24b26e0a1f6799163dc143eceb22c7b82878ff869d97050eb7b293b2e0a1e3fe19765c143af7c92ecb82871fe981d97050ebdb243b2e0a1d7d644765c143d5fc32c8b8287cbf765917050f978ecb22e0a1eb7e19635c143e6fbb2c6b8287cdc7658d7050e9ff2ec22c7b057be497454f60c7fcbb0ca1ec15df935d774582bbf26c2ee8b047f663759d160adfca2eb3a2c15df935d6745825fb27c32e8b057d647755d160aefc9aeaba2c12fe98d95745835df0dc12e8b067bdd7825d160cf6baf04ba2c1aed65e09745823ff30ba8e8b0577e4d751d16097fcc2ca3a2c19bf985d07458397acaba0e8b06775d5831d160d6eb2b063a2c19ed75608745835dacac10e8b067d5d5811d160d7ab2b023a2c12ff985d764582dbf26baec8b047f6637599160b5fca2cb322c1af965602645827f726c04c8b067bdd78259160d76b2f04b22c16bf9461564582def22c2ac8b05bee418559160b7ac8eeab22c16bf945d564582dbf26baac8b05bee417559160e5eba8e8b22c16fb9060d645835db0bc12c8b07abdd38259160d76c1f04b22c13f990e19545833eee9c0aa8b06bdd938155160d7ab2702aa2c11fd989d373582bdf24ba6e6b057be4984dcd60cf7c9309b9ac11fd9899373582bdf24b26e6b057be49745cd6097fcc2e9b1ac16ef9259163582bbb29b9ac6b04fe6538058d60d7cb2700b1ac14fd97a1163582dbb27422c6b05be6428458d60b77c9308b1ac16fb90611635825fb313a2c6b05b764e7458d60b7cc84e8b1ac16df935d163582ddf24ba2c6b05b76537358d60b7cca700b1ac1af984e01635825fb2dc3a86b047f65b8750d60adeca50ea1a else 0x5cd64d5fc3708b9ac9daf945d772592bdf26baee4b2779e4575dc964af7c82ebb92c99ef985cf725939df2cb9ee4b257be5573dc964ed7ca2e7b92c95ef905cf725935df2cc06e4b267b5d580dc964dd7ca301b92c99ed7360372592bdf26c2ee4b2779e4585dc964af7c830bb92c95ef9359772592bdf20b2ee4b257be5583dc964cf6c2b07b92c95ef9060f72592bdf2ac06e4b267b61580dc964af7c9b01b92c99ed83603725933df2cc06e4b267be5580dc964cf6cab01b92c99ed65603725933df28c06e4b267be4d80dc964cf6c9b01b92c95f7915d57059357f0dc22e0b273be1b725c164cf7c2ee4b82c9daf84dc9705933df07b92e0b2577e41855cc64aeecaf00b98c99dd85e01731933bb0ac02e63267b615825c064afdc9b0ab80c95f995e0d701933f30bc1ae03267e615835c064ef4c2b04b80c93ed90e0964552beb27b26e2aa57d64364dc554cfbb2301b8aa99f56460371552bbf26c2ee8b1d77e4d65dd1638fecc6eb3a2c75bf945d67458e5fb21c32e8b1cbfa63655d163d77c3704ba2c79ef75e097458f3daebc12e8b1ebb597825d1639f6c8704ba2c71ff985d47458f37f30ba0e8b1f2f595741d1638fecc6eb322c76bf945966458f5bacac1cc8b1cf7e418399163cf7baf04b22c7aed65e096458e7db21c12c8b1cf764f8655163cfbba702aa2c71fd989d37058e9fb2d3a6e0b1d7be4974dc163a7ecb509b82c75dd93a137058ebdf24c26e0b1e7be4984dc1638fecc4c9b82c75dd939937058ebdf24b26e0b1d3f65a745c163af7c92e8b82c74fd96dd36454e7df24c34c8a9d6f6537699153adfca2ed322a75fb9061d6454eb7b29bb2c8a9d6fe517659153a7ecb6e8b22a79ee87e096454f3db0fc12c8a9e7ba5f8259153cf6cbf04b22a79ef76e096454f3daedc12c8a9edb5978259153cf7ba704b22a73ed90e096454e7bf20c18c8a9e7ea5d8019153cfccbb00322a7b79956006454f7b326c00c8a9efa6498019153af7c92c9b82a75fb905937054ebbb26326e0a9d7b64864dc153afac88c9b82a75f9901937054ebef22c2eeca1d3f643769d943dd7c2704bb2873ed90e097650e9fb21c32eca1d6fe51855d943aefc9b0abb2875f7916157650ebf720c2aeca1f2fe1b845d943e77c3704bb2879ef85e097650f3db0bc12eca1f6be13825d943af6c8704bb2879ef82e017650f3df25c02eca1d77e4d805d943cf7c1300bb2871fd90a1c7650f1ff30bb0eca1e3f5d9801d9439eec9b003b287bb9946007650f7b326c00eca1efc645801d9438fecc4edbaa875ef925db7550f1ff0d3b2eaa1e3fe19765d543af7c92ecbaa871fe981d97550ebdb243b2eaa1d7e640765d543cfbbb702baa879f676e057550f3eaedc0aeaa1e7d1db815d5439eec9f08b2a879df76e0d6550f3baedc1acaa1c7fe4187d9143a7e) else (if j<8 then 0x6abd564b3b3010b66c042a659d9cece766bc79cdaf1d71cd5c79254e5e48d5c4232f1d08caf54232c96736b255e3abd6a42cbaa772a56976af5a4d519d08d4466cda11908c3635e3af1d08cb25592ab99b3684657aa11a84ab255d32c9508ca955e3ae3908c846592d09564b416592ac9508d3fe57aa11827caf5592a11908c8464232f1d64a846592ac9508c846423211964a8469f7ac9564ab25592a11964a8464232c952f08464232c967c0bc76ae211a7a33b3592ac967673c26cdbb4d64ab25592ac95d58d9b592ac95b36b25592cecdb373b3592cecd08d3b3423366db36d9b57aa119ab8d5c6ae3570696b25592a119d3a8469d9ba7505c846592af1d78ebc7592a11908cb254232c95b36b2574ececd64ad9b592cece5873b3592ac955eaaf56cdac9673684657ab66d08cb256cda11a706d9b6cdcd65b36af55e3b66d78f32f982cb6e587299423211908cbc74234a0578ebc75e3af1e4d2bc74234945ab8d5c1a5b571ab88466fdb7edbc72306fdb7ec69634b5e38ef55eabc71deabd578ed5c4233c91e48f247923c91d3abc75e3af1de4920f89d483dab8dfb6fdc83e41ed9b6cdac9564afb77cfaf1d78ebc715047de3ad1ac8ca2f1c0431734234526274bc78912f1e2030d7792211908cb2585f99d614e13e655b4d55eb086837415a05900b7f0beddab8f9f69aa5e108c9784233e7d5eaf757aa0c6d5eaae64233ccd81ebf7592adb5b36b8e7923c5508c8466cdb2e95eaeeb592a5e108cb25592adb55ea846715baedda6ebb592bab1ab88464232119d3a8464c8366d78e8464233a7578ee5b73e37ed08ce5b721af1db36bc7721ac95b36b254232c9578ed9b199b8ad64ab255928085320b254232119b36b25592b571b36b25423366db36bc76fdb84dab834b6ae309dbf6dfb6f18d2db9634b6d532ad956d9b6c18d8d2f0d6b3572c95ab8d4469ab4519e6cd24232119974cab1fb1339914af5634a11987e97857a8d2d84e34b1b1af1d5eaae61b1808581ebf75b6ac957acbc709f2a5552aba65c721196daae65a62119656af5010ac9560834b57aab9958aac5556a5e12f03f61fb25e14faa9553ea995404a23522288c6c6a024f0a72535067533aa1d932031b4bc24b529c92d4860be85404ce4758e951942fa44ba1d82ac2fa3ba215508c82e32a1fecca87d13d81dd0e823f63901c20de06cf3571a34ab6675267156cca8633300177cb7c31b2ce95f0ab653118d9338a204e626712b48f406c22810e027c4171fb0e947aa3bd1d28dec4383631a58d2c66631b17d0b645822a001089fc4fe02113388f44381fb0ed06e4330177000055827c11d075030011a06c01c8084042000000577e4d855c3649dec9f08b2cc93bd90e1165992bbf26b2ae7326ede13815d5649fac8702baac93bd93e116559277b21c22cab257de4575 else (if j<9 then 0x50007c6f280e0800140207040004c88082e680800180806000fcc030086000105840005e64200c02200c02100802161004101c00101c02000c0e030087910004070180030180028180806101c0401000884038083c20000418080e000c041400068400800301644001c1002000c02030806010a060701410020014060000c104f34100600008a020081c30380c0002008a00008407000043592ac9564a846423357164ab254bc29952f0b25c1e25e1b36d9b592b66d4cad9bbfa366f048b256cda5e164ab25592e031b377b5bfa5f12f88d9b592df4d64ad9b592df112f031b6cdac95b36b25592ac9564ad5c6ae2c9564ad5c6ae3571b36b256cdac95ab8b25592b66d08cb25592b66d64ab25bdaac9564b66e592ac9564ad5c592ac95ab8b256ae2c952f0b25592ac9564ab256ae25e164ab254232c9564ab25592ac967c0846423211964b794592ddf164ab257562c9564ab25592ac96b80d5c5e3ac9508cb25592ac9508cb25592b66d64ab254232119ab93e0532b66d64b59f6cddd92eaad5c4232bd564aa65532af1cceabc76cdac96dccb25423366d2f1746ba32c9564ad5c1a5b66d64a8464bc2c9564ab25592b57164ab2542335712f0b259d9dc9564a846592dc3508cb25592bab1b36b25b7aa119ab8b254bc2119ab96e6592db9adcd3b36cda996dae021592b57178ebc76cda118696d9b6cddad9b36d5c423211964ab254bc2c9564ab25592ac95ab8978592ac9564ab25592ac9564a846ab02c9508cb25592ac96766b25592cecd08cb25592da9d64ab25592ac9564ab256ae58a5b36d9b6cdbab2b0ebc7b430086cdcd9b5e3aa5578ea955e3aa5564ab25592b66de48b254bc561ecacd9bb2b211ac8e846b23d8e0ceb5876cdd61d08cd9b6cdb66d2f0b25592b5712f0b25592b66ea90d9b6cdaf1c042d9b592d521b360216cdac95b363a56cd99d578e8464bc21192f0846423366db3754833aa119b36b25010b66db36b256cdb66d78ed9b6cdb66d64ad9b010af1db373b39d9c94564ad5c592ac9564ad5c9f0211908d629592a11964b608af82c96bb0b2575629f5b36d5c592ac96b80d5c6ae3571ab88464232c9508cb25592ac95d3ab2574ed702b815c0ae02c9564a846592ac95b368469f0357004231b6cdb66d64b59f6cdac96766b2518d99d564ab25592a119b369786cdb66d64ab256ae0d2d08cb25592ac95ab88466ae0ef52f03bd6ae3570696a656cdd61eb0ed9b4bc0ef5b369784bc2c96aded9b33a99d564ab25592ac9564ab25592ac9564ab25592a11aac0b254232c9564b3b3592a1192f0846592a11908c846423366d64ad9b592a5e1b368466cdb66d4cad9baa42c9564ad9b9d9ac940420216cdb66d64b5486cda996a90a656cdb66db366755b6adb4042021592b66d64ab251d2ac9564a3a56cdb66ccea6755b else 0x741049902320082011c423239400199017282120134430134426212c27302150404090006020a85440005a506ca083c04000c360e2a6e010c5600081e00081e0c281d302160136830131020136820180826200800180188169400152c1006102c5020f00840ff30092000141e840442800282004000fcc0901a4000280802000c120082060404000909560f98195821c0412081c02121000179908030008e68200c00202410030088e6048000620240613980e000088030485040484010484e604004328020021d1800121000570e8c0000b94403a10242020001c100e13000813058c030920030006c60380208212c0014100617180e000c06840b8ce50908e5e30004e300d081a100600e3080701806ca2020001594000101080701c10345800021820109020b018020820498813440413101c202e60380c30400c021b980617980612440410200210042410042c102004010c00084c0e12100e100810400820a02000080830080800180004010d200009080a4400020c040800068401f9800200404101c06100208100800030c060c1006000c02070806020006030001c38200800180030024030383040406020086ed0004000184c4000409000409010003f282400180c12000c13650186000984070980030001c2010002f280c0007100600008603b280434200002182000010fcd040180400280608000c0e090186010412010bcc840480400281c12010008090080c3f3024060000c106f30240600008a070100030084c2c800420004c02180c02070c02030386030004000080c301804001c1003e50180050080c0018040e030f8c030007900080830080006180802070008000380438201c0200100200080fe))))
def g127H7 (j : Nat) : Nat := (if j<1 then 0x486000000000020320000000000000000000000001cb30000000000000000000000000000000000000000000001821923c02000024b533d0000000306fd1740410002c8e00034d80000000000088570c400000000000003c26000185ac40c0000003c4ef2480000000000401000013c800052424d10002cd700000000000000000000000000000000000f15146300000000002494302ccf601e8802000000000000000000000000000040698a3000000051ec000000000011b0000c162484c1c84730001c400000caa000343900000008158000000000000000000000000000283b235440fd19800042ff080000201d0000000000000000000000000000f2c40001263ca00002c5e00020d442780000000000611648d00028f70003c4a00000000000000000000043268b2000000030ab496000000000024300001011f3c000000019011040000b244000e39800000030dd000106873ac00000038d0a1350c60000000000000000000000000c09000000000028fca08c000000000000000000000000f348000000207900000000000000000282b0002ca6000000002ec0000001cad0000000c154000000000000014f50000000000281f03ec0000001cbed335483000349353a005c0000000000000000014e10000000b1b7835c2d00000000000000000062dcc62000346100000000000000000000000000000000c5f000000073380000000000000000000000000000000105b43e000000022e10ecf37000072e80001166874d39cc8700000000000076f209c1e0000000326c00000000000000000e1480000000000336ac6b0000000000000040b8000000000030ea09900000000000000000000000004a98204847b0cc000000000000000000000000f10c0000000425e018000b023071f12c00000028a20000000000000000000000000000a394c515051460000249df0340000000cc400000000000000000000000000007229c1c0000000000000000000000000000000000000000003030000000000000000000000000000346500000000000000000000032b3ce00000ced000000023140000000000000000000000007402c1800000000001838000000000020cb000000000000000000c50000000000000004270000100242400034dbf108cd30002c010000cbd00038e362f000000000000000000000000000034d90000000e1d54150002c340003504000000000000000000000000000000000000000000d3fc00000038ea00000000000000a1f000072200000003cf300004c0000000000010c7000000002694df00000000000000b32800000000000000000e0a000031f400000018670001ccf00020fe000044f12b800000000000000000000000042213030100010731050a2000600600211010143091000001001 else 0x2be80ef0f007800000000003c4c0028000b3580000000c36000000000000001294000000000000008198306405a226cab00000000000000000082f00000000000000000000000000000001c95000000000000000003c3d13300000002022000006e00030ef000000000008f8c01e0de000000000dc000000147f00024f9000000050fc069127c00000020fdf00c0000003064000000000024537048000f12000000000000000000d30c000000000092a0000000000000b4000000000000000000002070000088b00034fa0000000428501b000106a0003813000000000038c20000000532000033a4000000000000000000000000000000062c2046000000092d8c7700034290002497f124000515c0a4000248c30b00000000000000000000000000000000000000000014e20002ce4116c000000000000000000000000000000000000000002417d29f0f11112d02000207e00000000000000000000000000000000000000000000000000000000e09c000b2e4000000000043b8000000000)
def g127D8 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then 0xb805d1309fd87d9130bdd83d9130bf980d91309fd8799130dbd7499130bdd83991309fd8759130dbd7459130bef82591309fd8719130bdd8319130bed8219130bf58119130bf98019130bdf8458d30ddd7458d30fdb8058d30bdf8650d30bdd8650d30ddd7650d30f9e6450d30f9d6450d30fdb8050d30df97458130efb6458130ef96458130fdb8358130fd96358130fd95358130fd94358130fd96354130fd94354130bed839d920bef835d920bef8459520bed839d120bef835d120bed83d9120bed8399120bed8319120bef8655120bef8458d20bef8650d20bed8650d20fae6450d20fad6450d20fcd6350d20feb8558120fe98558120fe96558120feb8458120fe98458120fe95458120feb8358120fe98358120fe96358120fe95358120fe94358120feb8650120fe98650120feb8550120fe98550120fe96550120fe95450120feb8350120fe98350120fe96350120fe95350120fe94350120bf5839d910bf7835d910bf584d9510bf78459510bf5869d110bf5839d110bf7865d110bf7835d110bf583d9110bf58699110bf58399110bf78359110fe78259110bf58319110bf58695110bf584d8d10bf78458d10ff38058d10bf586d0d10fb564d0d10bf78650d10bf58650d10fb66450d10fb56450d10fd56350d10ff36454110ff16454110ff36354110ff16354110ff14354110ff38650110ff28650110ff18650110ff08650110ff38550110ff18550110ff36550110ff16550110ff36450110ff16450110ff38350110ff18350110ff36350110ff16350110ff15350110ff143501109ef825da649f7815d6649ed80dc964de9825c064df1815c0649ef825d9549f7815d9549f580dc5549ef825d3639ef825d9439f7815d5439ef825d3609f581dd5609df835d9509ef825db409f7815d7409ef825d9409f7815d540b9d8395140b3d85d0d40eb96458140ed96358130f595354130be9809d920beb805d920be581d9520be980d9520be9809d120be980d9120be980991209ef87591209ed8719120b6d8519120bcd8319120be58119120be98019120bcd8395120be98095120be78155120beb805cd20be980d8d20beb8054d20b6d85d0d20be980d0d20eeb6558120ee96558120beb8458120eeb6458120ee96458120eeb6358120ee96358120beb8650120be98650120faa6450120fa96450120faa5450120fa95450120fab4350120fa94350120b75859d910bf1809d9109f587d9510bf1809d110bf18099110be782591109f58719110b758519110bd58319110be58219110bf18019110bd58395110bf180951109f78755110b77855cd10bf38058d10b7585d0d10bf180d0d10f716554110bf38454110f715454110f715354110bf38550110bf18550110fb26450110fb16450110fb25450110fb15450110fb34350110fb14350110 else 0x759543bdf83595439fd87d9143cff76d9143bdd83d9143bbe8799143bbd8699143bbd8099143cff7659143bef8259143ebf7659143ebc7659143faf8259143bbf8059143bbd8695143bf78155143bbf8655143edf7658d43edc7658d43edf6558d43edd6558d43f9f8458d43f9c8458d43f9e6458d43f9d6458d43f9e5458d43f9d5458d43bdf8058d439fd86dc143dbe64dc143dbd64dc143ddd63dc1439ff845d760aff8459760bf781553609ff845cf60aff8458f609ff8750f609fd8750f60afd8650f60dbd7450f60ebd6450f60ddd7350f60edd6350f60bf581dd5609fd84dd560bdf835d560afd84d9560bfb8059560aff84595609fd83dd160afd869d160dbf749d160aff865d160bef825d160b7d851d160dbd741d160bdd831d160bed821d160bf5811d160afe87d9160afd83d9160afd8699160dbf7499160bf98099160dbf7459160bef8259160ebf7459160ebc7459160aff8359160eef82591609fe87951609fd8795160afd8695160bdd8395160bf98095160bf781551609fd84dcd60afd84d8d60ddf7358d60bfb8058d60aff8458d60edf7358d60efb8058d609fe87d0d609fd87d0d60afd86d0d60b7d85d0d60ebd64d0d60bf980d0d609ff8750d609fe8750d609fc8750d60afd8650d60ebd6450d60edd6350d609fd84dd9509ff845d950b7f84595509fd86dd150d7d65dd150bef8259150bdd8319150bed8219150bf58119150bf98019150b7f8655150d7f7655150ddf73d8d50ddf7350d509ff87597409ff865cf40dbd645cf409ff8758f409fd8758f40ddd7358f40bbf8650f40bbd8650f40dbd7650f40f9d6350f409fd83dd940cff769d940bbd849d940bbf845d940bef825d940cff865d9409ff845d940dbf845d9409ff835d940def825d9409fe871d940cfd761d940b7d851d940bdd831d940bed821d940bf5811d9409fd86dd540bf7815d5409ff865d5409fe87d95409fd87d9540bbd84d9540bf581d9540bf980d95409ff87595409fc87595409fd87d9140cff76d9140bf980d9140bbe8799140bbd8699140bbd8399140cff7659140bef8259140ebf7659140ebc7659140bbf8359140faf8259140bbd8695140bf78155140bbf86551409fd86dcd40dbe64dcd40dbd64dcd409fe87d8d409fd87d8d40bbd84d8d40bf980d8d409ff8758d409fe8758d409fc8758d40bbd86d0d40dbf76d0d40dbd76d0d40ddf7350d40bfb8050d40bbf8650d40bbd8650d40dbf7650d40dbd7650d40f9f7350d40f9d6350d40fbb8050d40efb7658140ef87658140efb6558140ef96558140fbb8458140fb88458140efb6458140fba6458140ef96458140fb96458140fba5458140fb95458140dfb7358140efb6358140ef96358140fbb4358140fb943581409ff845d930ddf835d930dfb805d9309ff865d130ddf835d130df) else (if j<3 then 0x8d40dff7654d40dfd7654d40fbe6454d40fbd6454d40fbd76d0d40bff8650d40bfd8650d40dff7650d40dfd7650d40fbf6450d40fbd6450d40fdd6350d40fbf8650d40fbe8650d40fbd8650d40fbc8650d40fbf7650d40fbe7650d40fbd7650d40fbc7650d40ff88758140ffb7658140ffb8558140ff98558140ffb7558140ff97558140ff96558140ffb8458140ff98458140ff95458140ffb8358140ff98358140ffb7358140ff97358140ff96358140ff95358140ff94358140dfe845d930dfd845d930dff865d130dfe865d130dfd865d130dfc865d130dfd75d9130dfd74d9130bfd8699130dfd7699130dfd7599130dfd8759130dfd7659130dfd7559130dfd7459130fdd8359130fef8259130dfd7519130fde8458d30fdd8458d30fde6458d30fdd6458d30fdf6454d30fde6454d30fdd6454d30fdc6454d30fdf8650d30fde8650d30fdd8650d30fdc8650d30fdf6450d30fdd6450d30ffa8458130ff98458130ffa6458130ff96458130ffb6454130ffa6454130ff96454130ff86454130fed8458d20fee7654d20fed7654d20fee7454d20fed7454d20fef6454d20fee6454d20fed6454d20fec6454d20fef8650d20fed8650d20ff58559110ff56559110ff58359110ff574d8d10ff58758d10ff57658d10ff68458d10ff58458d10ff67458d10ff57458d10ff66458d10ff56458d10ff76454d10ff56454d10ff78650d10ff68650d10ff58650d10ff48650d10ff76450d10ff56450d109fd83dd1659fd80dd1659ff805cf649ff835c364bbf84596649ff805ce649ff835c264bf7815d564bbf84595649fd80dcd64ded75dc964ded73dc964bed80dc964ded85dc964ded65dc964ded83dc964ded80dc9649fd83dc164def725c1649ff805cc64ddf855cc64ddd855cc64ddf805cc64ddd805cc649ff835c064ded825c064df5815c064dfb855c064df9855c064dfb835c064df9835c064ddd865ce549fd83dd9549fd80dd9549ff845d954bef8259154df764dc554df564dc5549ff845d763bf781553639ff845c3639fd84dd563bdf83595639fd80dd163afd869d163b7d859d163dbf749d163aff865d163bef825d163dbd741d163dbf7499163bdd8399163dbf7459163bef82591639fe87951639fd8795163bdd8395163bf781551639fd84dc1639fd84dd9539ff845d9539fd86dd153d7d65dd153bef8259153bdd8319153bed8219153bf58119153bf980191539ff87597439ff865c343dbd645c3439fd80dd943cff769d943bbd849d943bbf845d943bef825d943cff865d9439ff845d943dbf845d943def825d9439ff805d9439fe871d943cfd761d943b7d851d943bed821d943bf5811d943bf9801d9439fd86dd543bf7815d5439ff865d5439fe87d95439fd87d9543bbd84d9543bdd83d9543bf581d95439ff87595439fc8 else (if j<4 then 0x60efd8650f60bfd84dd560bff845d560bff8459560dfd75dd160efd65dd160dfd85dd160dfd65dd160dff759d160dfd759d160efd659d160bfd839d160bff865d160eff865d160dff755d160dfd755d160eff655d160efd655d160bff835d160fef825d160dfd751d160efd651d160efd75d9160efd74d9160bfd8799160dff7599160efd6599160bfd8399160dff7559160efd6559160efd8559160eff7559160efd7559160eff7459160efd8359160bfd8795160bff8755160bff8655160dff7455160eff6455160efd6455160bfd84dcd60dfe74dcd60dfd74dcd60efd64dcd60dfe84dcd60dfd84dcd60dfe64dcd60dfd64dcd60dfe745cd60dfd745cd60efd645cd60efd74d8d60efe6458d60efd6458d60efe8458d60efd8458d60efe7458d60efd7458d60dff7454d60eff6454d60efd6454d60bfd87d0d60fbd74d0d60bff8750d60dfe8750d60bfd8750d60dfd8750d60bff8650d60efe8650d60bfd8650d60efd8650d60dff7450d60fbe7450d60fbd7450d60eff6450d60fbe6450d60efd6450d60fbd6450d60fdd7350d60fdd6350d60ff98050d60dff74d9150bfd83d9150bfd8699150dff7699150dfd7699150f7d6599150bfd8399150dfe8759150dfd8759150dff7659150dfd7659150f7d8559150f7d6559150dff7459150bff8359150fef8259150bfd8319150f7f6455150f7d6455150dff64dcd50dfe64dcd50dfd64dcd50dfc64dcd50bfd84d8d50bff8458d50f7f6454d50f7e6454d50f7d6454d50f7c6454d50bfd86d0d50fbd64d0d50bff8650d50bfd8650d50fbe6450d50fbd6450d50fdd6350d50dfd865cf40dfd8758f40fbd8458f40dfd7654f40fbd6454f40fbd8650f40bfd83dd940dfd85dd940dfd83dd940bfd839d940bff845d940fbf845d940bff835d940fef825d940dff865d940dff855d940dfd855d940dff845d940dff835d940dfd835d940bfd831d940bfd86dd540dfe76dd540dfd76dd540bff865d540dff765d540dfe765d540dfd765d540dfc765d540bfd87d9540bff8759540dff7659540dfd7659540bff8459540bfd87d9140dff75d9140dfd75d9140bfd83d9140fbd7699140fbd7599140fbd6599140dff7559140dfd7559140fbf7659140fbd8559140fbf7559140fbd7559140fbd6559140fbd8359140fbd7695140dff7655140dfd7655140fbf6455140fbd6455140fbf7655140fbe7655140fbd7655140fbc7655140bfd86dcd40dfe76dcd40dfd76dcd40fbd64dcd40dfe86dcd40dfd86dcd40dff64dcd40dfd64dcd40bff865cd40dff765cd40dfe765cd40dfd765cd40dfc765cd40fbe645cd40fbd645cd40ffb805cd40bfd87d8d40bff8758d40dfe8758d40bfd8758d40dfd8758d40dff7658d40dfd7658d40bff8458d40fbe8458d40fbd8458d40fbe6458d40fbd6458d40fdd735 else 0x4a028904ec099c12e0249032405fc11d0227034208400f881de039606d00d0819202fe05b00a88026028c00980998120021203e801300e701ce036001300cd004c009805b00260026028c04c0026010a009803b0063008800c401300130000dfd83dd165dfd80dd165dfd855cf64dfd845cf64dfd855c364dfd845c364bff8359664bff8059664dfd865ce64dfd855ce64dfd655ce64dfd805ce64dfd865c264dfd855c264dfd655c264dfd835c264fbf845d564bff835d564ff7815d564bff805d564bff8359564bff8059564eff865cd64bff855cd64dfd755cd64fbf845cd64bff805cd64eff865c164bff855c164dfd755c164fbf845c164bff835c164dfd735c164dfd855cc64dfd855c064bfd83d9154bfd80d9154dfd845c363bfd84dd563bff845d563bff8459563dfd75dd163efd65dd163dfd85dd163dfd65dd163dff759d163dfd759d163efd659d163bfd809d163bff865d163eff865d163dff755d163dfd755d163eff655d163efd655d163fef825d163bff805d163dfd751d163efd651d163bfd8799163dff7599163efd6599163bfd8099163dff7559163efd6559163bfd8795163bff8755163bff8655163dff7455163bfd84dc163dfe74dc163dfd74dc163dfe84dc163dfd84dc163dfe64dc163dfd64dc163dfe745c163dfd745c163dff74d9153bfd80d9153bfd8699153dff7699153dfd7699153f7d6599153bfd8099153dfe8759153dfd8759153dff7659153dfd7659153f7d6559153dff7459153fef8259153bff8059153bfd8019153dff64dc153dfe64dc153dfd64dc153dfc64dc153dfd865c343bfd80dd943dfd85dd943dfd80dd943bfd809d943bff845d943fbf845d943fef825d943bff805d943dff865d943dff855d943dfd855d943dff845d943dff805d943dfd805d943bfd801d943bfd86dd543dfe76dd543dfd76dd543bff865d543dff765d543dfe765d543dfd765d543dfc765d543bfd87d9543bff8759543dff7659543dfd7659543bff8459543bfd87d9143dff75d9143dfd75d9143bfd80d9143fbd7699143fbd7599143fbd6599143dff7559143dfd7559143fbf7659143fbd8559143fbf7559143fbd7559143fbd6559143fbd8059143fbd7695143dff7655143dfd7655143fbf6455143fbd6455143fbf7655143fbe7655143fbd7655143fbc7655143fdc8758d43fdf7658d43fdf8558d43fdd8558d43fdf7558d43fdd7558d43fdd6558d43fdf8458d43fdd8458d43fdd5458d43fdf8058d43fdd8058d43bfd86dc143dfe76dc143dfd76dc143fbd64dc143fdd63dc143dfe86dc143dfd86dc143dff64dc143dfd64dc143bff865c143dff765c143dfe765c143dfd765c143dfc765c143fbe645c143fbd645c143fdf835c143fdd635c143dfd845cf60efd8458f60dfd7454f60efd6454f60dfd8750f))) else (if j<7 then (if j<6 then 0x5d27ab0f4a9e823c562070f339e583c8a78d8f159e140e647824eff1df33bc04ed80131dd13b8473cced79ae23b4876444bd9d823aee4f044bd9d683aaa7454ea31d333a487454e811cf3278273801ef9cd138527308e5b9cb0393a7228e3f9c7038ca71589e09c4307be70e0e149c16370e701cdfe1be937b46f2cdde1ba9372c0a8cdc39b78019a6d94dab1b4305286cc0d8e94360d066c48d7f897b35e86ba4d711ad30d426b102f99aad35346a0cd341a59348c68ccc561a28342a6808cf599d8339266e8cd3999432fa6598ca7994431f064b4c67191627dc641cc8398f831c2633812e0026004c0970c5d98ac3158097012e107931323eb05ae188204b84f04c35838f30b04f04c2093b6305c097012e025c0528602c910169524405ff0bf091c52f765f38bdd825c1d4c39f0587960c2f405e14bb9176312125d50b9e97162e065bd012e16e12d9c5aecb5200262d2a097012e025c04b809707db8fac052859e8b20966316b859305a096412c5c586cb0615fd2bd4576c3508ef32b9056d4a97959e2b0e55e0aae95462a5e30b8a8814f1228e5358a5f825c04b80970484933023183a2ca5408b129222268a3d146728a85114a1b0fac28462d709e613c128200b4099813fd27dc4fb89f713df26604f309e09021276c0db49d193901e1a3c0812e025c04b80970151829426d24bcc9a9133f26604c7498e8909260c39f012e12f325c04b34959129724f8496492112201f8448cc910121123f4479c8f391d4238a00980c911b6234609708c61115121245c48ad11472258445487d10e321b04314857109b212041e48351047206025088108cf5201c3fec7f40fd5004c3f0812e025c05461cc83990fb71f583e447a68f8212123dcc7ac0f4d1e743cac78e0f0d1e040d783508ef31db0380875e8ea61d1639f07348e521c7e38a070a8e021bce37506e08da61b1635b06a68d3a1a2e341067a8cda188a330c6580c99190c31cc62e0c5c188a30b860b8c0017d22f485d78b5c17382e345bd0b6f13e82d704e909d216822c985878af415b22b2855b8a8d15482a9054689d214f426c05338a50147228784ff89f413c227484dd89b0133225ec4c3097b07be25a04aa825c125e2508484892f1238097048488f611b62310458889a110e21b042e884a105e20703fe87da0f8e1b683d807990efc1dac3aa07410e641c6c38006e90db41b0c350802604b8009835806a10d241a0c30a86700cca194831d814604b818a030a86020be617cc2f005c50b6c167c2c405710ab4150c296051d0a1413bc26804b10944122c23a046500c6113821b842008120fb81ef8013079809701d882ae01b0097012e03a2071e0e3c01302d0004c0e001b6825c05a000981af035e066e0c60184823a05ec0a8c15182e304740b8c16802bd05460af415e82ae04b80a8c1 else 0xa0e0608040002301040087dbdc040025336f672b2000dcc04021e772e2000955cc021e2016680080e00021858500c6f2f37642001201d8100807cc0238473008636881e002220381000989cb9a00201816680080406001808004040002189000410060200204280086000210201008009ca0600180f281800808100602002f60402480180800f080fca002634272800803080e0400280f2c200081000021c8328000880408020027648728082000c0604103800081080e008804268e26681000b9a06041e6850181081406041808104081007cc022f3250100881004173040100881404021c203800108031bcd0922000438403800088040210380020109cc08040221f583eb125f262e497c85987db8fb72de8aba556b2ac02042ab2d1792ac05562aa89055aa8b1f6ea9f0b20a14c54caa8c15270f4d4298a8ed5182a21542405194ff86a10d42a7d14f0a9ce5376a6d04e91944534a25ed4cb298b416c4ed8b7a1c2952f094914bc24f352caa5794a7a93c0324a4b505b291a4a5e0a8c013002640286160ee129033b8473cc9e09c4351e06c75179097b35e8a375467230507be8b8d16628ac5158a2ed4562032513aa2084bd897b50eea1dc7a6a86850ba8d2505b1641509480c941ba18f429884d50cf28204226a0353fd27f34fc8835d3eca01431589f2812e1f384f769ea0f9c16f40e649e5505b218f41569e093b99e452c829d713a8a73e4e569c61384a6fa404603353759ebf4dc09b3535f26ab4d409a4533d26674ca89904d71262e40467824eff239f4c1a987d2f9a6144c1a980930125f34bc89754d749fab3f389718d74a5bb4b5096652cc9af43e707dcd0c7a5824ae69580ca209d232881a8501925514a7c82d89db10214a5e9435292250d49fc93cd27024c9497c92bcd698732493882d9244a47648c64f0522a13b6487a0a8cf9c025c40280a50c56242a4812907d1c0a40937f84f0520813c1363a90251ff239035fe54bd1f3a39047a825ecf9c1f381e9a3e08fb81f70478a4fb8d74a39047648e7cd74a3904702863d0c7a37246c677f91aa2349466c25ed193a314460a8bc90fe22e345988af5151228f44f87915136a25e448e88e1011a22912f6887910f220f12f66f2d0fe21ed43ac0f7c013097b439686f10d683df2c8286790c79af43e705bd10c0217516de82d87a6a16642b680c87c1214c426a7d850932113420883c4fb820e641ae833039918ac0d420a8cf9c201440460a50810a0c13c8a82d87c120ab41308214f228f4d40dc7f9d02fa050407a80c82852023404662b067aa01440027fb8f891f701f047f9cff3909021207f60fe49fba35d27eacfce1f8d35d27e08fb99f703ee04fb8fb09ae93e9c6ba44e913c1276c7cfc5b7897b35e80098f9c10213e4a7c48f7f9eec35d27b74f671ebf35d27ab0f4a8cf53) else (if j<8 then 0x381800804000618083818606039a002000184060017601800988140600262767303f281808001421211140002062c5000081880200061f3008001880e0403080028180c200080e02080020100c20489d9ca000204063728a800081018dcc120602010837372848180f600421012000206082800400860402001020080040788058a019a2e6819501099a540604201950107cd54021f35504008804020108122a584808142000c120402080028000c204891612060201083048100c2000a120604020800303800081220a002810380e68009d80e0200062e6f2e20008000e101810080098a0600261f603f28180008122119b89cacc00281838007ca06000e272818380080e06040025289800088102c000220087841e021458380e689000c0e0600180e68006120e0002048830380059a058800276000386160e00180a200079a00101810086060e000205083760380f300420c040308000e2f301808142000c03080018180820009d8000204062c201008388040002280628380c200090800020e245838180c2000c1204020e20381008489d8120602010837673018080420dd80fca060201083f67372818080420fd804020e2760583818100800211cbd8021220000838609ca0602000e303850032808bd8020006202038080018a0e031a0020180c680091bca030800283840180008a060400ca02283818000820a0e06020800283800081820a0e06080200285f28481f600800211d8100206276008187cc02050820083840002040620384800081220c0e1202065688304800081220bcc06020088043761580f300220c0401881810095818800045606200008115818a0e0200082048000c209cc06000308280018081020a1206020457083007615808173420e12021048200008800020618000f301c20a0602104730095018a12060002204008404020600200f28009880402000e20081220008020406002010080018804030800208018100c2000c06040308002f280c2000806040208002b280098088081000cb2002332808007ca0200062630180f2c2000cca0600022027672800980818f21d80810018c0206404008180080807ca02002c2728080038b8c0e03cb0800332800380881000cb2002283b2800088040200180010200838b200804000e02302038100800b20100218380f282000a02012204200010086020428180010a06039a0400222010404028800268e20166800a020508002010000818811cc02062014200060002050827301808001420c070804180f30100420a06020400082840180a5010b08109402042f3040125008a9405cc10022a501008604000228248838100c2000d1bcc0e0322040038881808200010a0e000e021a6040001008a220e0004022838100871a0f0800042810000820a0a0e00080402283820100800 else (if j<9 then 0x2cc00133048042018acc0e010821584800656120108242018004881200061c2000186130800181c20006080600180848410000402201008b06540010022040084860400100220000f307cc881004002808b00074c8810540200373220100094c548a002220400878a04001e6840181008a1002041b50400862c02142008b0612100402242008906cc060410022808b041204021c2628086961200184818006120e881810a040e2600181a205cc02ca1a200f332800bcc06881a20073018800880e1838180d2881e041040100061e2810166840088100010404001e02201002203881fcc04a000281040006021e001f301a80008040010000810600034a1d2800081080600040220382000f081848042060e07081a58042061096021848183860e08101810006025838006960e010824201800602084818042090806000e2038180420806040108205804206080e0018000848616060108204018005808a0e06200020782044500800cca0402184008100081e02001c680051a960e060028201840206102038516120800202048006100206183848042085606104001580885600881800e0401cc061d3220001888856001f3018022085788001d304008610060308233000186cc0601082040100860424021c20485080958180420810065602215c204005708181c204cc02001b3420180094a02101008906cc04100222804008600261280400838804000e1818400860e10021a842040088a0061002228018006a200041a27301800828040018c840100880e100206233420001880e0613301c200080224100420400081a80006040108187e28900008a10001e02245000081018bcb140002040630100078604024812212010083881e0010100920008ca04c800209373201000ac9cada00232b20006c8ca001b701320008dbcac800273008112000a615b4804002b68100c5818a0406136800104818adc000204062800101860714041b7038001018a00051606277620001080204001d2848000899c560602002f6018000848a56120006215818481000b9c05880027673048180800142100002101f66762e200010d9c54060426701950109cc13ca039c0037604f28080018d9d89ca00276000487cc00061e76225f2800bd9cc13ca060200048848100800488061200181f284800806120400201f2800488074a040002289000086139d16040200345848181000a1604039c0028480059d88040027280760489ca12001f2e70007ca028800204800087d802001220180800488121400ca022f6728080018a0212061a581808147000dcd08040200284840180008bd81206000204083f30184808001420fd803cc120108304818000820bcc06020108284f280c2000a1206020800281730081894a0e0002265730086060002187818000880600020e2158 else 0xa81041204100220a01040e12101730007cc1edc187f30081000a00021e192258000810a120601cc4829800810009cc00173019207cc00481c5018081082600104808001881e00034a2078180d288040810081860002ca180b2854c0002ca21584802209140853280865612060020100840688000224233420381800a10000206204150080081002001d3221500080224001a20089079c105406020430900840e12881810a85cc120600201810022081207cc0088281220004881206034a252821e054a1878a842a040218480d28708000204204010080081e0412022000167061e05cc88002b28484ca0410002223287808807cc880024201000604022a180800106034a1010000d2894a0402184818080091c00101b280861ecb1410002b281000088100200042078081000896120600201c2048608121048200121004204860e010818481c2060e06121848204960e08002330180060f4a00020628784000606001f4a20480b2860e0002ca2530100074c00153220000b28a0e0088195800514066e02205001b81808a1e061098380060e00ca02201098066894c88ca00273012800088800101f30481a8000b080e002620489840108261818))))
def g127H8 (j : Nat) : Nat := (if j<7 then (if j<3 then (if j<1 then 0xbdc00000000000000038cf400000000000000000000000142a000000000000000000000000000000000000000000000000000000000000000028cd800000002cf948572c490000000000000000000034e0c00000000000000000000000000000000000000000000000000014d7c00000000000000000001c1280000000000000000000000008e24000000028a3800014798000000031198000000000000000000000000c8ec0000000000000000c5f0000000000000000000000003c254000000034370000000030d14000000000000000000014f8800000000000000000000000000000000000000000000000000000000000000000000000290640000000000000000000000000000000386fc000000000000899e8a5000000000000205df8c940000000000000000000000000000000208f00bf542bc0000000000034da0000000000000000000000000000000000000000000000001417c00000000000000000000000000000002cdf80000000206d400000000000000000000000187fc0000000000031160000000024c200000000000030404000000000001d1868a7c000000000002cb88000000000000000000000000000000000000000000000002c0bc000000000000009800000000000000000000471c00000000901ec6b800000000000000000000000384c40000000000000000000289bc000000000000000000000001c364000000000000000210d3071400004c7c00000000000000000003887000000000000000024d1c0002c460000000000003d098000000000000000000000000806800000000000000000000000000000000000000000ad000000000000000000000000000000000000000000000000191a0000000000000000000000000000000038ee400014194000000000000000000000000000183d400000000000000000000000000000002491408d0000000000000000000000000000000000000000000014f6301d8c4500000000000000000000000000000000046c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010a7800000000000000000000000000000000000000000000000000000000000000000003111c0000000000000000000000000ee0000000000003406c48b800000000000000000002c9fc0000000000000000000000000000000000000002cbb0000000000000000000000000000000000000000000000000000000000000000000010cc800000000000000000000000000000000000000000000094800001120024124004500000000000001040040224005220800100000804160100008088020114018920000000008001025104b08021200000824020b088039001400240080008440200008202000001048000 else (if j<2 then 0x2cb300000000000000000000005c2c96800000000000000000000000000000000000000000000000000000003c8380000000000000000000000000000000000000000000000000001c854000000000001c5bc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011132cc5ac7978534000000000000000000000000c1a2cac8000000004268000000000000000000000000000000000003cba80000000287800000000000008144000000000000000000000000000000000000000000000000000341b80001015800000000000000000000000000000000000282480000000000000000000000000000000000000000000390cf0992c4540000000000000000000000000000000000000000000000000000000000000000000000000002cc4800000003c9b00000000000030d0c00000000000000000000000000000000000000000000000201400000000000000000000000000000000000000030000107ac0000000000000000000000000000000000000000000000000a200000000000028ae4000000000003cb48000000000000000000000000000000014770073000020db00001912800014eafc708000000000000000146680c34000000000000000310b4000000000000000000000000cdc1005000000000000000000000000000000000805400000000000311580000000000000000000000000000000000000000000000010adc000000000000000000000002c1a8c6c10af08cf0000000020b9c00005151c3ac0001cd000000000000004a0c0000000000000000000109b4000000000003cf580000000000000000000000038f5c0000000000000000000000000000000000004390000000000000000000000000cd2c000205000000000000000000000000000001c8290a340003c6ac00000000000000000000000000000003407800000003c290d0a40000000000000000000000004e0000000000000000000000000000000000000000000000000000000000000000000000000000000002c7dc00000000000000008a0506dc0000000000000000000000014f08000301b40001c8e4000000000000000000014984000008bc00000000000000000000000000000003c5ec0000000000000000000000000000000000000000000000000000000000000000c9f000000000000000000000000000000000000000000e5800000000000000000000000000000000000000000000000000000000000000000905c178000240e8000000020fe2036e4b70000000000000000000030d7400028c64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c else 0x14c540000000000000000000000000000000000000000c31000000000000185e00000000000000000000000000000000000000000503c0000000000000000000000000000000200d4000000000000000000000000000000000000000000000000000000000001838c00000000000000004e9c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003401c00000000000000030a54000000000000000000000000000000000000000040dc0000000000000000000187a8000349a40003cf3090e40908000000000000000000004fdd001800000000000000000000000000000000000000014784000000034468000000024d56082c0003012c0000000000000000000000000003cb340000000000000000000000034b6bc7100000000000000000000000000000000000000000000000000000000000000000000000020671844c0003c8180000ce1c000000000000000000004d40000000000000000000000000000000004d84000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000282e40000000000000000000000000000c594000302f08dce05500000476c000000000000000000000000000000000000000000000002c20089a800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010df400038c2400000000000000000000000000000000874c0000000047bc00000001c522486c00000002822f104645d4000000d80000000000034ec40000000000000002d04800000000000000000000000000000000861c0000000000000000000000000000000000000000000000000000000000004c440000000000000000000000000002042000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038a334a8000000000000000000de800000000000000000000000000000000000000014d30000000000000000381d400000000000000024b780000000000000003cc4000000000000000000003099800000002c47c000000000000000000000000000000000000000000000002cff400000000000000000000000000000000000000000000000000000000000000000000000000000003cd0400000000000000038cde0e4000000001cea8000390d68134000041a4000000000000000000000000000000000000000000000000000289c4080c00000000000000000000000000000003456d844000000000000000000000000000000000000000000000000000000002084000014fa60557004800000000000000000000000000000)) else (if j<5 then (if j<4 then 0x110ec000000000000000000000000000000000000000000000003002400000000000000000000000000000000000307d0000000000000d0140000000203d00000000000000003456400000000000000004ad800000000000000000000000000000000000000000000000000000000912c000000000000000000000000000000000000000000024b2c00000000000108d58bc400014fb800000000000000000000000387b400000000000000000001895000000000000000001180000000000000000000028e16808800000002433680a00002034400000000000000000000000000000000000000000000000000000001c5cc000000010ca800000ec80000000000000000000000000002ccea40c4000000000000000000000001cf84000000000002c3800000000000000000000202340c600000000000000000000000000000000000000000000000000000000000c000000000000006340000000000000000000000000000000000000000000090c400000000000000000003c66c0000000000000000000000000003430c000000000868000000000000000000008c9c00000000000000000003c4f800000000000000028bd24ce0000000028298000246a90398ca58000000000000c644903400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000291a40000000000000000000000000000000000000000000182b400010964000000000003cc9800000000000000000000000000004db8000000000000000000000000000000028180000000000000000149d5c4280000000342e800000000000000000000000000000000000000018a8800000001081589240000000000000000000000000002cf37cc30000000000000000000030b1c00024cac000000000000000000000000000000000000000000000000000000018434000302180000000000000000000305f4000000009104000000000000000000000000000000005040000105f84bd400000000000000000000000000000000000000000000000000000000000000000001c5d0000000000002059b8138000000000000000000000000000000000000000000000000000000000000000000018f0c0000000000000000000041fc00000000000000000000000000000000000106f0000000000000000000000000000000000000000000000000000000000000000000000000000000010b0c000000000000000000000002cbf80000820c000000000000000000000000000000000000000000000003cb6c00000000000000000000000286140000000043380000000000000000000000030fd8000000000002cf000002cc6800000000000000034e70000000004acc00000e55cae80000000000000 else 0x14fc0000000038020457744e8000000000000000000018a4c8748000000000000000003ec00000000000000000001885c000000000001c5a103a00000000000000000000000000000000000000000000000000000000000000000000386d8000000000000000000000000000183f8000000000000000391700000000004dc00000000000000000000000046f40003ced70bda455c00000000000000000a5c00014b1800014fb4000000000000000000024ffccd3c00000000000000000001ce38000000000000000000000000000000000000000000000000000000000003cea40000000000030dcac9e400000000000247b800029008000000000000000000000000000000000000000110b00000000000000000000000000000000000000000000000018ea00000cb14000181200000000000000000000145380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009800000d11848940000000000000002809c000000000000000000000000000000018f908f5444ccc75400000000000000000000000186f8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002106c000000000000000000000000000000000003c63e0aff4778000000000000000000000000000000000000000000000000c3b40000000000020790000080e4000000030930000000000000000000000001cb7c00000000000000000000000000000000000000000000000000000000000000000000000000014d9a82880000000000000000000000000002465c000000000002cd4c0000000000000000000000000000864c000000034e780000000000000000000000000000000000000001c8d88e3c00020ddc000000000000000000000003cf4946c40000ccb00000000250fc000000000003850c000000020e52cf18000000000003cb4c00000000000000000001918800000000000000000000000000000000000000000000000340ec000000000000000000000000000000000000000144f48f140000000000000000000000000000000000000000000000000000000040a800000000000000000000000000000000872c00000000000000000000000000000000000103bc0001c66000000000000000000000000000000000000000031024000281cc0000000000000000000191200000000000000000000210bc00010e5c000000018b840000000000000000000000000000000000000000000000000000000045d80000000000000000000342a40002cc800000000000025194000000000000000000020a3c000000000000000183fc00000000000000000000000000000000000000000000000000000000000341000) else (if j<6 then 0x282c60a74000000000000000000000000000000000003c6e9c474000209480000d09c00018410000203164084000081f40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c11000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e7c000246940000000085a8000000000000000185e94d1800010a68000000000000000000000000000188640000000000000002d00c00000001cf380000000000024af8000000000000000000000000000000000000000000000000000000000002caac000000000000000000000000000000000002c740000000000000000000000000000000000000000106ec000000000000000000000ecc000000000000000000000000000000000000000000000000000000000000c24400038f2c00000000000000000000000000000000000000000000000000000000000000000000000000000001082400000000000000000000000204e0000000000000000000014f248b740000000000000000d08c00000000000000000000000000000000000000000000000000000003c7a400000000000000000000000000000002895c0000000000000000000000000000000000000000000000024fd7894445480000000349e0000000000000000000000003416d0c18000000000000000000000002ca1c00020ef00000000000000000000000000002432dca24000000000000000000000000000000000000000000000000c7e00000000000028834000000000000000000000000000386e000000000000000000000000000000000000000000000000000000000000011b0000185ac00000000000047d400000002c7ed0a10000000000000000000000001407c000000000000000000000003c1180000000000000000000000000000000000000000000000000000000004a800000000000383f400000000000000000000000000024d500001c2b000000000000000038f47474400034ca4000000000000000000000000000000000000000000028226105c000000000002861800000000000000000000000000000000000000038c91cfa80002489147cc000000000000000000000000000000000000000000000003cb41484800004220000000010c398a8c4611830000014d600000000000000000000000000000000000000000cc100000000000000000000000000000000000000000000000000001434c0000000000000000000000000002c27b07d80001814e0cc00000113c000000000000000000000000000388a000034bf0000000000001852c0000000000000000000000000000000000000003ce60000000000 else 0x1095400000000000000000000c368000000000000000000000001c8b40000000000000000000000000000000000000000000000000000000182d00000000000000000000000018fed0d900bb6835800000000000000000000000000000000000209368524000000000000000184968a2c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010a44000000028240000000018920000303b846a610100000000004ec000145b000000000000000000000000000008630000000000000000000000000000000000000000000000000000000000000000000034bb8000000000000000000000000000000000000000000000000000000034f3c00000000000005c400000000000000000000000000000001119000000000000000000000000243b000014f8c00000000000000000000000000000000000000000002cfe40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002caa80000000000000000000283880000000000000002c85000000000c3c08c890c780000000000000000000000000000000000000000000000000000000000000000000000000001cb20000000000000000000000000000149cc0000000000000000000000020b500000000000000000000000000000000000000000000000000000000000000000000000000000000151380000000000004ba00000000000000000000284a7caf6411400000000000000000002ca280002401400000000000000028a1800000000000000000000000000000000000202cb8d5c00000000000310c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014f7c00000001831fc52800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001034800000000000000000000000000000000000000000000000000000000000000000000457ecb014abc00000000000000034df0000000034e1800000000000188a8000000000000000000000000c18c000000000003cbbc000284f00000000000000000000000000000000000000001c15c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000283c80000000083cc00000000000000000000000000000002070c0000000000000002c1e400020fac0000000000000000c330000000028384000000000000000000000000000000000))) else (if j<10 then (if j<8 then 0x82a800028c1c00000000000000000000000000000000000000000002ce8c000206a000000000000000000000000249e9c91c000000030e100000000000000000000000000000000000000000000387b0000000000000000000000000000000000001107e0f23c7f0000000000000000000000000000151af4d8c000000000003c51000000000849c000000018a700003c93b89de025a09f44f1c00000000000384e4000000000000000000000000000000000000000000001004000000000000000000000002467f41f347180000000000000000000385580000000000000000000000000000000000000000000000000000000000000000000000000000000000020940000181c7c9c000034f7400024c0800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000386980000000000000000000000000000117c000000000000000000000000000000000000000000000000000000000000000000000002489c00000003d1540000000000000000000000000000000000000000000000000000428c000000000000000000000001cdfc000000000003819dca940000000000004e84000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004174000000000000000000000001c8740000000000000002c8200000000284c80000000000000000000000000000000000000000c84400000000000000000000000000000000000000000000000000000000000351000000000000000000000000000000000000018e4c000000004d2000000001c5a6408c000000000000000000000000000000000003ce880000000281eb87c800000000000000000002840800000000000000000000000000000000000140b5ce8000000001cb800000000000010b080001c6d000000000000000000001049800000000000341300000000000000000000000000000000000000000000000000000d0c800000000000000000000000000000000000000000000cfc400000000000000008d48000000000000000000000000000000000000000000000000000000000000c8b000000000000000000000000000000000000000010ac400000000000000020c1400000000000000000000000000018f8000000000000281bc000000000001cf780000000000000000000000000000000000038090000000004eb40000000000000003058c0000000208f80002c5b80000000000000000000000000000000000000000000000000000000208000002d178000000000003073400000000000000024aba0b2800028da8000000000000000000000000000340640000000000000000000000000 else (if j<9 then 0xc1dc000242bacc2c0002062c0000000000000003c1c800000000cb64000000000000000144b8000000000000000050e80002ced18f7000000000000000024ec00000000000000000000000000000000000000000000100cc80040000901800000000000000000000000000000000000000000000000000000000000000000002c62000028c5c0001c2524d9c000000000000000000000000000000000000000000000000000000000000000000018e2800000000000000000003854c000000000000000000018d08000000000000000000019134000000000000000000000000000000000000000000000003cebcc8c40000000000000000000000000000000000000000000000030ca1c805045800000000000000000000000000000000000000024ac000008107421000000001c0340000000209a000000000000000000003c6b000000001c958000000000002888400000000000000000000000000000000000000000000000000000000000000000001020800000003c9c800000000000000030b38000000028c6c00000000478d8758870000000003060fcda40000000107c3041c0000000000000000000040740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002425c000000000001490c00000000000000014c3cd07400000000000000000000000000000000000081724b8e82f40dd9cbe3102c0000000000000000000000000000000000000000000000000000000000000003ca000000000000020eec000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014de68394000000000000000000000000000188dc00038fbc00000000000000000000000000000000000000000000000000000000000000000000000000000001cb580000000000000003494c00000001c974000000000000001083e0464800000000000000000000000000000000000000000000000000000000000000028ad4000000000001859c000000000000000000000000000006400000000000010a1400000000000000034cff0e200000000000000000000000000000000000000000000000000000023000000000000000000000000000000000000000000000000383a400000000000000008ed800000000514a03e80000492c000000000000000000000000000000000003cb1000000000000000000003c3a80000000341640000000000035030000000000000000000000000000000000000000000000000000000000000000000000000000343f00000000300e00000000000000000000000000002013c000000000000000000000000000000000000000000000000000000000 else 0x198000302e010e000000002862a8ce70ef5cf9c000306bc00000000000000000000000000004a8400000000000000000000000000000000000290a8000000000000000000010a6c0000000000000003044951240000000000000000000000000000000000000000000000000001448c00000000000000000003d0880000000000000000000000000000000000000001c76800000000000000000000000000000001458280280000000000000000000000000000000000000000000000000001421f800c0000000000000000000000000000000000000003477c097000000000000000000000000000008fb00000000346000000000000000001876000000002c2280000000000000000000108ac0000000000000000000000000000000000000001c340000000000000000000000003cbcc00000000058800000000000000000000000000000000000000000000000000000000000000000000000000020d78000000000002d0d80000000000000000000000000000000186080003c9024b9703600000000244a10880000000000000000348a40002443000018a600000000000000000000000008cc400000000100000000000000000000000000000000000000000000000000210dc0000000000000000000000000000042c000000015108000000000002c26fcd2540b9810c00000001451d0688000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008ff000000000000000000000000000014dac0003804400000000000000000001445c00018ef8000000000000000000000000028000000000000000000003818b40600000000000028808000000000000000000000000000000000000000000000000402c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014cec00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c3238bc3073fcb631084000240f8000104840aec0000000000000000000000004678000300b000000000000000000000000000000002c04000000000000191640000000000000000000000000000000000000000000148f4c4d4000000000000000000000000000000018d88000000000000000000000000000000000000000000000003ca40000000000000000000030444000000000000000000000003c4bd80aec7240000000000000000000000000003c4185090035e8160cefc0657c40000000000000000000000000000000000023f8a480000000000000000091800000000000000000)) else (if j<12 then (if j<11 then 0x110a00000000000000000000000000001d0f908cc41ec000000000000000000000000000000000000000000000003102304c000000000000000000003010800014059c2078dc400000000000000000000470400000000000390b8000000000910000000000000000204b40000000000000000000000000000000108780000000000000000000000008c740000000000000000000000000000c56800000002ccfac9bb47c400000000000283dc0000000000000000000000000000000000018ee84308000000000000000000000000000000000000000000000000000000000f4000020094000391740000000000000d470ff8000000000000000000000000000000010ab5498c0002cf68000000000003c9600002c04c00000000000000000000000000000000000042380000000000028dd40000000000000000000000000000000000000001898b42140002463800004d380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c53c000000000000000000000000000000019140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000181900000000000000000000207280000000000000000000000000000000000000003851b4658000000000000cc840001c46c811c0000000000000000000000014650ce9accbb107000000000000000000000000000000000000000000000000000000000000000000000000202fc0000000000000000000000000000000000000000000000000001915c00000d800000000000000000000000000003c43800000000000000000001466545fc0000000000000003c2fb0478000343180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042d8000000028154000000008e48000000000000000000000000000000000000000000000000000000000000000000000002cc28000000000002cd340000000000000000000347f6c0f00002c5080001c284000000000000000000000000000000000000000000000be80000000000000cbc000000000000000000008e69840c00000000000000000000000000010c0c00000000000000000001c530000000000000cfcc0001519e869c0002cfc800000000000000000001c0d0000000000001827c0ba4000000014c8c00000000000002ec00000000000000000000000000000000000345c80000000000000000000000000000000000038fd00000000000020929c else 0x10764000000000000000342958e740000000000000000000000000000000000000002c0080000000000004f04433c0000000000000000000000000002cf6c00000000000000000000000000028d2800000000000348c80000000000004d580000000208e00000000188990267412400030a98000286e5d080000000000000c0700000000002700000000282de8685cb980000000000024738000000000000000000000000000000000003c7fb86740000000000000002462446cc00000000000105e400000000000000000000000000000000000000000000000000000000000000000002cb0400000000000000000003cedc000000000000000000000000000000000000000290adcded85900000000000010d7000000003c32a4dd0000000000b3c000000000001c514000000000002cbe700380000000000000001416800000000000000000000000184d80000000000000000000000000000000000000dbc000000034d1000000000000000000003c30400038c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029c0000000007200000000000000003881c0000000000000000000000000003037400000000097acf51c1840000000000000000000000038b5c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014690000000000002c9f80000000141fac4140000000000014607c88acb4540c80000000000018d680003904c00000000000000000001c88c000000018ccc00000000000000000000000000000000000001c000000000000000000000000000000000c2cc000000024bfc000000000000000000000000509400000000000008e8000108c0000000000000000000000000000000000000000000000000499400000000000000000000000000000000000000034e9400034aa0000000000001d0f00000000000000000000000000000000000000000000000000000000000000000000109ec000000010b5400000000000000000000000000000000000000000003d16c00000000000000000001ccb411680000000000000000000000018544000344adc0a40000000000000000000000000000000000000000000000000000000000000003cae0000000000000000000000000000000000000000000000000000000034c7000000000000000000002c6b60f640000000082ac0000000000004e6c00010504000000000001c8fc000389d8000000034e3641b000000000000000035115cf4c0000000000000000000091a8000201e3c0000000000000000000000000000000000000000000000384d000000000000000000000000000000000000000000000043c000000000000000000000) else (if j<13 then 0x2c3e400000000000000000003837c000000008b9000000002878b4d6c00000000000000000000000000000000000000000001ca640000000185600000000000018eb800000001096c0000000000000003ce0800000000000000000000000000000000000000000000000000000002448000000000000000000000000000000000000000000000000000000000000000000000000150f4000247a1c4ff8260000000008e2dc2740002514c00000000000000024150000000000000000303c4000000000000000000000003114400000464000000000000ce440000000000000000000000000000000000030472cfeb0db584b00000000000000000000000000000000000021050000000000000000000000000000343540000000000000000000000000000000090780003cd6400000001824c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000147e8000000000000000000000000000000000000000000000000000000000002005d457800000000803c00018810000181d00000000000004aa4000000000000000000014e300000000008300003518c000000000000000000000000000147740000000000000000000000000003ca080000000000000000000000000000000080fc000051100000000000000000000000000000000000000000000000000000000000000000000000038bc80003c858000000000000000000000000000000000eb2054000000000000000000000000000000000c9d00000000000000000000000000002468c0000000000000003c8600000000000000000039c0000000000000000000000008a9c00000001c584000000000000000000004424000000025054000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000390580000000000000000000000000000000000000000000000000000000000000000000000011028000000028bec000000000000000000000000000000010f980000000000000000000000000000000282d4000000000000000000000000000000000000000000000001432400000001879c00000000000000000000000000000000000000020e0690380000000000000000000000000000000000000001093c0000000000000002c14800000000000000000000000000000fa000000000000000000000000000000000000000014e9000000000000000000000000000000000000000000000000103500000000000000000000000000000000000000000000000000000000000000003cde00000000000018c0400000000000000000000000000000000000000f400000000000000038488000000000000000000000000000087e400000 else 0x484e83d800000000000045b4000000000000000000000000000000000000000000008f28c6800000000000000000000000000000000382c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000049ac0000000243780000000000010f100000000000000000000000000000000000000000000000000e640000000000000000000000000000000000030cd40000000000000000000000000002008000000000000000024750000000000000000000000000000000000001c83c000000000003110c0000000000030a92cc4c000290680002497d4d9601ac00000000000000018c50000000000003c75c00019060000000000000000000000000000000000000000000000000000000000000000000000000000000000003cb2400000000000000000002c87c000000000000000000028bac00000000000000028cd000000000000000000000000000000000000000008ab0000000000000000000000))))
def g127D9 (j : Nat) : Nat := (if j<1 then 0x84dd13064a99246476116a44d10c63fe0fb44198ff83ed0f623948f2c3bd8ea43948df23680d4e33b8c6430b8bce2e28b8a2c38abc29e0a0a26e097424c08d021f882c1f6876c1ca06ac18f85fa171058014484a4118041c0ef036a0c602e20a4023008c01de063015603d80a402900440007ff74597fe3a2cbff59664ffaeab27fd65593feb9ac9ff5c164ffec8aa7fd64553feaa6c7ffdd563ffaeab1ffd6558fffba2c7ff9d163ffae8b1ffc7458fff322c7ff59163ffca8b1ffd5458fffb82c7ff5c163ffec8a9ffe6454ffeb22a7ff19153ffacba1fff7650fff3b287ff5d943ff8eca1fff7550ffebaa87ffd9543ffacaa1fff6450ffeb2287ff55143ffee0a1ffd7050ffeaa6c1ff54f60ffa87b07ff75583febaac1ff59560ffee8b07fe74583feba2c1ff1d160ffcc8b07fd64583ff2a2c1ff55160ffee6b07fd73583feb1ac1ff54d60ffe86b07fd43583ffb22a1ff99150ffac8a87fc64543ffb1aa1ff58d50ffe86a87fd43543feb2e81ff58f40ffaa7a07ff76503ff3b281ff5d940ff8eca07ff75503febaa81ffd9540ffacaa07ff64503feb2281ff55140ffee6a07fd73503ffb1a81ff58d40ffaa6a07fd43503ffb2261ff99130ffac8987fc644c2feba6cb7f5cf65bfae1b2dff74596ffb9acb7fdc165bfaebb25fd73d92feb86c97f5da64bfaeb325fd73992feb84c97fdd564bfee6b27ef72592ffb82c97f5d464bfae6325fd70192febb4a97f5ce54bfae12a5ff76552febb2a9df59554bfee6aa7f771552ffb82a97f5d763dfacbb1dfd74d8efeb86c77fdd563dfecab1efd6558effba2c77fdc163bfeeca9dfd7654fbeb2aa77fdd153bfee0a9dfd76d0efebae87ef59343f7aa9a1dfd70d0effbb2877f5d943bfeeaa1dfd7550fdf32287ef59143f7ca8a1fbd5450feeb1a877fdc143bfaebb06fd65d82feba6c1bf59360bfae7b06fd63d82ffbaac1bfd9560dfacab05ff745837fb22c1bf59160bfee6b06ff635837eb1ac17fdd950bfaeca877d65542ffba2a1df55150bfee6a877d53542febb6817f5d740f7ac9a07bd54d02feb9e81ef50f40bfeeca05fd76502ffbaa817f5d540f7cc8a07bd64503df2a281ef55140bfee6a07bf43503dea1a81fe58140bfaec985fd754c2feba261f758d30fbaa6987dd434c3fcb0261fe54130fdcec907ed76483f6baa41fbd9520fdaca907ee74483f6ba241fbd9120fdcc8907ed64483f632241fb95120fdaa8907ed73483f7b1a41fb58d20fdaa6907ef43483f6a1a41fd9d910feaec887f575443fbb2a21fd59510fece8887f574443fbb2221fd99110feac8887f464443fb2a221fd55110feae6887f763443fab1a21fd54d10fee86887f543442fab8ecb7bdc964afaea325dd73192f6b90c97d5c464bf2e0325dd73952fbb8aa95f5d743fd2c0907e940483f8a8221fc50110 else (if j<2 then 0x2f2ad140c00e045eddc0800db0481169170004407022d22d0400700042cc057654800617b7765002a416072ad0036d16045035c08011b80825a0c58a1c58202004002c087b0001042023e00088145000222e0404389980e59c006000d2e6022832400088292e602201d99b2ce06007d820119cc0420e2002acc04510115660229202144160414e00305040430e2c08200106039b644ca26700200ced99734400380cc941011760113105ce040081606265d99a70020208120008a2c566d9942001c06c1198481083a504000889450002203cc2840100107cc28c88020020e612cacc045104c0011020a4b9808a0762bcb341801c0abcb345030038a03132eccd34010001eccb980841c40a26040041856c100f3010838002ab3081424510015660238814ab30114001059840a2c4660404508233011220b020a68018502021c4020a680141010858902002021848b020010418101d9132879a0080337665cd1000e012e6040454a20502cc046021e20b9a0800e2c0c4cbb334d004080e00088092e602200d823307021070e0010416046179766602106162a5ecca1000fb040206133011c466021ab01b0404cc04757b32e60210601b0403cc0420e1446602203039480014b8100191000432119280022c403948001620b039668018181cb3400b100e59a00521100e59a00620b022506072cd004840004320b012500046100420012303a1b0401001088c12808022a502100082e86cca040041d281064410a280910421e10080884730a040008c9456604045140009104298140488216881cd12682143c4153410804551899804d044114c9420a9a0871410101108820219a4a0410820002cc1008a1c508040f301083e61008088945040424c15980820836614080011766ddd9400a285810f68b140800bb770b140800db858a04005d80800b022e604043d93810016046d81329000291cc21281043660844109425b74540dcfd73da4f173b14e733884237373cd6f0194d013214c092ea4b2d2afca7b283499ef09c92322d481d1ef37451d3c6e119945db165c529135c477102439b0d5c2e909b4237079418504cc0c50193ff6fe5bf1afa7be30f6d3d62f40bc94f09bbb8c0fbb4aeacba36e75b94ce37b87ee0b37e8ddeb744dbcb6aed9035e0d55b4ccd22341acf23376cc2329ac95b1f6c5eb11ac24303ebf0af54bb9ae6ab7f2db8b5d2d74b41acc2b1c2c2caefab50abc17bca9d2a06a77a97ea4b28cc5d0a8509f8a79e9da27689c926e09a726665ef17bc7ba1ea49819e3696d257094b24be91419fa8ffa3ac63a23848c917428c922ee8a3a2128692152539a0d6816a0084dd1f9a7cb1ee87a90df23539e367721d7674c9ce071c9c046e21b1a6ae9a4c67e998c64e98e8625913461497f25ef176a5d096e25a09606566154653994784ff13b else 0x2801e0441e092014a0064a07324040061e2b301489400ebb2e648005cc932ad002ee060400217744020010a012e6060450096508cc046080762bca0018ead283033b2c40044e03941eccd1001010501ca0018cac50303132ce00403039a2659c007080c0011158a06941000238801b0266020c78b38401cd1012a236080339544043ec8914008553b3010454e240d501043449d94001d8247cc240ce899400f10481cbb334e0042c4a0c08bca10009240251204458004664a0808e104980004508241250004612045c4053800e2408b89967001d6000208401b3282021048f2c480d9973010840200043cc0844a0228b13940840030a00949811420011292e60238414012e602301d8af2cd000c706062659a0068807665cc0e68021302029420a000c8140c0c4cb3400e9818115132cd0040a0610001145134a080011806c09973010638401b0466020c70020084cc2818e9450310042001c58a13b329304040042a28311980829aa8812215019a086880228855980cd044a606226aa02087cc1012a10046540b308022aa1008088122aa05984011c280021831004200165080404489372ec020038e1c0cdcb1000d132eccc1c0829a00959941814a2c2000e4804a1c088b00084b981011c587220008a1d28200045161c0c4053400e1c08b89966801cc00020840023604021c6961c008d9980842058710042001858707b0902020021328166100450e24001cbb058421588040732a063ec100412a57107039406c56ab3442130210a80ab063e60404008085000226ccc3e28004047052b30112282959808a09280022015d9730a0600703))
def g127H9 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x3024fa868d9bb53040000e810cf400000000ca80d9700000000000201fa0770000836b9e90000b2320000000000025ee0000000485a00000000000000000000000000706d0000e0ac000000023fe000000000000000000000000000000000000049e10000867a8588000000000001ae800061456bb800000000000000000078caa68b46051c0800085a600000b78000b288000000000000000000396a9853000000000000000f29000000000000000000000000000000009388b480000000000000003b6000000000000000a61600034e132350154000000000000001e90800000000001449c000000000000000000019516e5e9600000000276aa4cc00062050000000000000000001cd800006118942200014f49b1200004040000000095a00000000784a0000000294d91860001ef7c877000000006c8c00012f500006dd400000000000a4ac00000000001a6300000000000049900004130000000000001a79d6940000000000000000000000000000000001c35094d000000000000000b4ea00000000000000000000006252000000000000000a63c00000000000802c00000000000f3fc04d4000000000000000000000001efcf58000614c0000000045fb9ecf0de00000000000707800000000000000000000000000f72204740007218c30800005a38000853e00000001074000045600000000000000031e28361900800000000000000000000000000000000000007b1ba546ebe9da959a5000000000000000013e000000000000000000000048fe00000000000000000004a5591971142532409400000000000000000000000000000000000000000ab900000000255000029ad502300000000000000084e20000000000000000001832a1f7e1562e32196ca6000000000000000000000000000000023a600000000000000000020b342a4915c0003c6c800000000000000126d27d000039cb800000000000000000024fc8e7c000000000012c2000052683198000180e0000000000000000000000000000002acc000000000000000000000000000000000000000000000d52400000000000e368000094e8000000087cc000000000008b8dd6e80000000000000000000001402000052941212654b5ea80003356000000059b00001eb28000000071c1893c00000000440000217c10550000000000000000000000000000000000000000049b1000000035bfd0b2000000000001246000000000005203e771a8ac0003ad8f1f466fc000788b000000024db8000303eab6812ab0817105100200190301044510041001106240591102407071149111003100003010220000010000005837000011070323705000010210900421020040010710021030130019001040631001300110001001000001000200250130003600110744ec400041004 else (if j<2 then 0xa720000000000018d20000000181c683a0001aaab16e0000000000000001a2900006a6800010bb00000000000000000000000000000000000000000689e0001aa894db7a8e0000ae6f16262e9000000019768000000000000000000000000010ec80004612000000000000000c4ec0006a27000000000000000704400011d3b0e60000c3180000000000000000001a8b000000031ed80000001250c00000000000000048a8000000001100000000000000035645223e3f200000000000000000000000000000005d40000000419c000000053aff58e000000000001560e99c000000000000000000000000000000000000000000000000000025960000000198d000008a800000000000000000000000000000000008560000000000000000000000000000000001a38400022d7848e0000000000072e6a60000000000000ea34000000000018200000580ed52e00000000000000000000000b4057886cd000000000000acfc000000000000000000000000000003818904d0000000000013530000ed98000000096b20000000000082bc00000003a0222ee0002d83710a00000458000000000000001df65b0700000000143000000006950000000000000000000112f4666000095780000000a79b0870000000000000000000000000000003a0c06c6000000023ce0000ef8e8c18000129200031e080000000000000000000000000000000000000000000000000000000000000000000000105c80000001865c0000000243e63230228afd547e00000004ab800000000000691b866decd40000000000000000000000000023b55980000000107c9d5f800000018f70000308300000000991504ca2c8000040e8000000000000000000000000004ea8000000000000000b1800000000000431900012e4c0001a87000000000003a8c000000000000a248211c0a5001e86742ba000099f000050288eec0004b6d00000000862226a0000000297508590000cd600000000e46e00021a1000000000000000600d977200000000000000000000000000000000000000000000000000000000812328f40000000c65e0000000000000008dc147480000001cae80006b5400000000000000096bc000000001980000000000008e20000000053d8000b1e868ec00009e0000143601d1fa76139185e74ad8000d38e00000007b3a00000003483ba0b00000000000000041e60001d208000000000000002207843400000000000e42c0000000402d0000450a5398000000000021cd000000000000000125912fc84700000000825c00000000000000000000000000000000028e000000000000249a000022c6a1c8000000000000000447800000014b9400000000000000000000000000e099d4f000000014974000697a000145d000032 else 0x2d2b800000010d040000000e316000090a00000000000000000000000000000049de0000000000000000001c1c40001155471f692c00022179784000000000000000458797e02ac00000000000000000000000000726c000000000000000000000000000000000000000000000f6e823ac00022d90001426c00022be00002a04000000000000000000000072e08c0cd3f80002697224c00000000000000398a800000000001d6180000000000158b729c815800000001b0d5394216000059fd00000003461a3bd12be000000023e5000000000004b5c0000000117600000000000298620a9000168d000000000000a6a40000000000000000000000c56a0000000000000000002d0f0000000105db4b40000000045b40000000000026880007188000040840000000000000000000000000183f183980000001894c00071900001e21c0002bd0000000000000000000000000000000000000028170000000184a0000000032e34714000706c000000000000000270400000000000b4b400000000000000000000000000a4f44e79d240000472c6ae400000000001a31400000000001cdea4ed2b9400000000000203dc49400025cc000000000002cf80000000000039d580000000c2d0000000000016aec00000000000acb14613806000000000000000366e0000000607a00000000dbc8000a6152e9400000000000a5b2460800000014a240000000e620ac6800022b400000002d7dfb11000000039e6000000012a429778000f55600018330000000000000000000314200008e7000000000000000000035c2000000063250001ae1b05f0000000000000000000000000034e60000000000000000000000000000000000a3320001cbe0000000000000000000535a00018a5418e6016000243f0000000000000000000000000001b138880000000000031ba00000000000000000000000000000000000000000594b0001caccd9043a00000083c0000000000000000006249941a00008e6800000000000000000000004650000000024be000184e00003761e150d590000778620b000000000001a2c00000000000000000000000000000000000000020800000000000000000010c480000000a4a40000000479201fcd7a609500000000000000090640000000000087d2e72c00000000000000000000000001a002d6f00000000000000000000000000000000000000000193c5106000000009498000a76e000000000000000000000013be30b909d0000000000000000000000000010888000628300000000000000000000000000000000008c7c00011b5000000000000000000000000000000000000024b28000d1ec000102580000000e74400011b900014144804800000000000963000036f60)) else (if j<4 then 0x48b3a37600000005a910001e05747600000001c5ff52f0000b6ad4a000003884000000000000000000000000000000000061e40003b0e000000000000000b7a600000000000000128bc000000000000000000000000000001c7d80000000abc00003bb273c6000000000002027e4f79be000000000003d1c00000001ef5000000007670000191f0000000000000002849469166cc000000000000000000000000000002ded0000000000010bd800032a6000000000000000a4e6880dba482228240cf380000000000359880000000000000012a6000188e80003923000000000000000451f08840000000000000000000000f578000000013430001a64a9ce80000001a7400000000212ce1e000000000000000000000000000497000003ad714dc10c0000000000000000000000000000018088000000000000000b460000000000020f802b8000000000008382070c000717863d4000000000000000000000000000000000000000000000000201f0000516acdad532a8f0b38cce2000000000000e402899585793ec00000006802c3c800000006a63000167d018a3acf00000003d54800000004f9b45e83cf908c0f2c00000000001847c0000000000000014d60000000000000000000000047ec0000000c29c00000000000000147940000000d341ccf4000219bb03def8800038190204000182e80000000000000000000001eb17030000026ae23c800000000000000000000000000000000000003744000000000000000000112b0000669e635dc72000000000000000603995aca0db03a8000225808a00000000270b4354000000000010378000439c000000000004812000000000000000000000009ca800034de00000000000000000000005377000000000000000d2b20000000000086e783f400052c1000000030b5e244000000000000000000000034b3800000f800000006863000000000005956000000000000000000000000000000000142a046b591a57000000000702a0000e1b800021fc000000000000000000000025648000d27e00000000000775800000000000d77fc77c00000000001e53fc27800000018ea7d3b8000000000000002bb386a0a8b78ce8000a40243240000000000000000006bb10001e14800000000001cba303da85b1124000198b80000001c77000000000000e2dc0007be43498000000033e10000000000000000000000347c800000000000000100a269800000000000324a00000000000000186bb5710000d6df865b8740000210aa187995b34d0001e4780000000439e00000000000000000000000000000000004ea00000000000000000000000000000032a1000000000000000000000000000000f1bb67d40000000350a000000000000001c0a00005a43000000000000000000000038120 else (if j<5 then 0x48f5b040e0680000000513400000005ac203920001d130000000000034b100000000e870000000000000ca4000000000000000d9c8000000000000000000730a0e8400000000000000000000000001860800013890000e580000283b0001a49ad52800000000000000520000000000000208a2750000150a80007370e788000000000000002573b37e956e0000000000000000003d34800000000000000000000000000000000091ce000000022b6333e000000063d100000000000000031b80998000000000002b441b3a8efc3236848000005034c2000000051db00000000ca2abae00004901c1a00000000000000000000000000000000000000000000000000000000119380000000651800000000000000000053c700000001cd380000000a8414c51bcd0000eb80000000000000003056f0a5f6f162395ef0000f224000000000000001e8180000000000000034be80000000000000000000001e8f1112800000000000000289de5be000044b800000000000000299a0000abf905b0000000021c000072a7968800000006bd96133864c00000000000000389d0000000000000000000000000015790000019e0000000421300008568000000026d00002c02931c61d4000000018890001c9448e20000000000000d50000a6920000000000000002bd800018e5000000000000000000000020f880000000ced0caa60d4a5040000000000000004dc40000000000000035c38000000062340006ba6241200000003ae623d60000000690b00000000000000006d20000000000000006e36c5c2af90000000000000000000000000000000000000000060df000000000000000d706000046d8000f0c400000000000000000000000000000000030038000000184c40000000b4d600000000000000000000006b8b0000000159400000000000000063ddb1478caac9500000001c9b800000006130000000000000000000058100000000606000060a00000000000000000001c6bc00051bd0000000000013920001e108980aa3920d200010008000c0822f5c00000000000000042f293c23f00000000000096b684b780780000000000000000000000000000000000000a44c000038e508e0000000000000004344000000000000000000000000010877d16000000000000000000000000000000000000000002507000000000000000390ca036000000000000000000396dd9dd000000019d5628481960003c460000e3ac00000004957b6aa4bac0000ab1022ecee8000000023dc00028698000000000009b562980000e9140000000000000000000000000000000000000000124d8000000000000000000337d000005440000000b41000019f0000000000000000610546c80000000482fe2420002df580000001a50685e7a360000ecf000028860000 else 0x3989dad47643076309c000000000000000735f000000000000000000000000007324000000000000000000000000000acd0001ee1000062bd0000000000000000000000000022ff00004f20000796e000000000002903460000010de0000000160c00000000000002bc000731d0000e74800000000000a63c000481700000001441084e671400000000000a26f44839e3000015a4000311980000000000000060ff404e00024f68000000000000000000000000000003b05e55a0000000336c33ae88280006a8a0000000219300000000000000000000000000000000000000496c0005b9900000000000486800000000000000000000000000000000000000000327050fa0002187a93e0001c6840000000008000000000000d06e00038d320c70000069149170c00000000000000000000000000000000000000000008a466ca00000000000000000000002af300000000000000006dceb380000000e2d4000000000000000000000078e300000000000480c0001212001a800000000000000000000000000978890d000047e80001ac077cfe940000000043decf020538000000188c40000000167600000007b4e62e400000000000000000000001288c0bf28b8000521b20c8000000000000000000000049be000000000000000f28e00000000000000000000000000000000029e50000877800000000000000000000000000000142e80000000255c0000000000011e2000000022190001e50000011a80000000000000000000c33694b00000000c671035800000014988d990187000080cd44a090f0000e1d800071500000a6c800073eaf7b00000000000000010d44000000000000000000000004f80002126d91000000000000000000010e40000612400000003068)))
def g127D10 (j : Nat) : Nat := 0xc2c40059812882c4b052a6047b6e2e598a1adba52ac2c62cab6e96c98020d306385b6e94b28a38a10014b05822e2ca12c98508124b00e94498a1cb3a5b042a61c42ca20eb059812452803a512c2c828b125b263872c012598d2872ca125b2634710b288b05366049280125b0d2c728b125b263472ca065b26107190125b0d18c444966346fc3c0e5b6ccdaf4afa8294a22799b060150480e42d0841502a003ff65ff597ff64ff993fd64ff193fe54ff553ff63ff58ffd53ffd0ffd43ffd83fd60ff543ff40ff503fd30fb483f510
def g127H10 (j : Nat) : Nat := (if j<1 then 0x1cfc00046230c80000000000000000000000000000000055ca1a0d9e00091b80000002e80000000000000000000350e0009390000000685000000000000000000000012740000000001cb702f83e304c000000000080c0000000003dee00074500000000004012118000000a600000000000000000000000000000000000000000000001a4a000000000000007a000000000000000020fa00000000000000000000000d3364d91280000000002075a8800000000051900012bc00000000000006688000000000c4e0000001a9a0000000000000000000000000001f8000845a04000524c0000000000000cf4000d71623c000000000000315da0a0000000000000000000000000000000000000000000001c50000d1d8000001c1c0003aac0000000000000000000c68032800000000000000004c600000000000000000000000000000000000000074168ac001ca8a6ba853d30638000000000000000000000008da00050e952000000000000000000000001c66000c1f000000045700000000000000000b50000000000000000000000000005180000000000000000000000000000046080000016e41208000000000b32d92c00000035b58408188a300000000000008445b720bb80dd2380000000000006ab400000033fa19c001c8e0000000000000721e9240000001738000000000000000000085b000518c00000000000000000000001b240000000000000000000a34800000000000000000000000003ba686a000000000000000000000000000000000000000000000000000000000000000018090000000000e21f1e11be40bc86000000000000074fe364ca200034580000000000000003122aa147c8000000000000000000000000072980018a9000185c0000000000000000000000000000000010c8000000000a550000000000000413c0000000000000000000169318953d22ec610003daa62f33b80000000b10006afc000000c4b8000000000d6b000000007b0000000000216000211400087300008f40000000000ad4001ca4a13a844000853000000098b8ea72d00000000000000001862000830d875158000935800000000000000039bc00016180000016f600000000000000000000000000000431c000000c0d800000000076c3a760ec000000000000000000000000000000000000000000d58008c9e400000000024b000086dbb3800000000003cc426000000000000006c72cc01c00000000001c000000045da257966c7c42001e0000000d770000016000000000083f8f5000000097a00000000000000000000000001e7100000014896830000000502e66e4b00000010e10004a9c0008e6000595400000000041e59a6cef96eb38d424000e52800046c05c10103111000210401102200001142100083031100221040004 else 0x500c57400000000000000000000002d080000000000000ab8000000000000000001ab5d60000000000001a0f0000000000c2d5701bc000146086438ab5ca46e926694800000000000000002be0002200000a2c00020780000000000000000415000000000000031000000018a0000000000027547d28e5ca88500004a6c00000034a2bb40000000000000000000104000145200080c58d00000000006178c35092176000000000091200000004cd00000000016af56580035980000000001c03e30000000000068900051215be000378aac80014561213ad00000000005a34000000a27000000046d0000)
def g127D11 (j : Nat) : Nat := 0x1ae2b0c2ff
def g127H11 (j : Nat) : Nat := 0x8140000000000000000000000748000000000000000000000000053a340000308001875040000000040000000000000000000014430000b0a5162c00139c6002ca00149000cc00000000000000045000002830030f02c
def g127L : Nat → Packing
  | 5 => (6,6,5,0,0,0,0,g127D5)
  | 6 => (261,5,5,0,0,9,0,g127D6)
  | 7 => (1133,4,5,0,0,13,0,g127D7)
  | 8 => (1005,3,5,0,0,15,0,g127D8)
  | 9 => (251,2,5,0,0,14,0,g127D9)
  | 10 => (21,1,5,0,0,10,0,g127D10)
  | 11 => (1,0,5,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 25 0 8 3 1 g127H6
  | 7 => lookupWord 52 790 4 14 9 1 g127H7
  | 8 => lookupWord 226 6805 3 16 11 1 g127H8
  | 9 => lookupWord 201 3022 4 15 10 1 g127H9
  | 10 => lookupWord 50 760 4 13 8 1 g127H10
  | 11 => lookupWord 4 70 3 10 5 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 6=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_2 : block g127 6 2 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_50 : block g127 6 50 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_98 : block g127 6 98 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_146 : block g127 6 146 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_194 : block g127 6 194 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_242 : block g127 6 242 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 261=true := (@block_merge g127 6 0 98 163 (@block_merge g127 6 0 2 96 g127P6_0 (@block_merge g127 6 2 48 48 g127P6_2 g127P6_50)) (@block_merge g127 6 98 96 67 (@block_merge g127 6 98 48 48 g127P6_98 g127P6_146) (@block_merge g127 6 194 48 19 g127P6_194 g127P6_242)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_4 : block g127 7 4 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_52 : block g127 7 52 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_100 : block g127 7 100 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_125 : block g127 7 125 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_173 : block g127 7 173 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_221 : block g127 7 221 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_269 : block g127 7 269 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_317 : block g127 7 317 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_365 : block g127 7 365 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_413 : block g127 7 413 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_461 : block g127 7 461 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_509 : block g127 7 509 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_557 : block g127 7 557 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_605 : block g127 7 605 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_653 : block g127 7 653 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_701 : block g127 7 701 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_749 : block g127 7 749 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_797 : block g127 7 797 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_845 : block g127 7 845 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_893 : block g127 7 893 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_941 : block g127 7 941 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_989 : block g127 7 989 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1037 : block g127 7 1037 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1085 : block g127 7 1085 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 1133=true := (@block_merge g127 7 0 509 624 (@block_merge g127 7 0 221 288 (@block_merge g127 7 0 100 121 (@block_merge g127 7 0 4 96 g127P7_0 (@block_merge g127 7 4 48 48 g127P7_4 g127P7_52)) (@block_merge g127 7 100 25 96 g127P7_100 (@block_merge g127 7 125 48 48 g127P7_125 g127P7_173))) (@block_merge g127 7 221 144 144 (@block_merge g127 7 221 48 96 g127P7_221 (@block_merge g127 7 269 48 48 g127P7_269 g127P7_317)) (@block_merge g127 7 365 48 96 g127P7_365 (@block_merge g127 7 413 48 48 g127P7_413 g127P7_461)))) (@block_merge g127 7 509 288 336 (@block_merge g127 7 509 144 144 (@block_merge g127 7 509 48 96 g127P7_509 (@block_merge g127 7 557 48 48 g127P7_557 g127P7_605)) (@block_merge g127 7 653 48 96 g127P7_653 (@block_merge g127 7 701 48 48 g127P7_701 g127P7_749))) (@block_merge g127 7 797 144 192 (@block_merge g127 7 797 48 96 g127P7_797 (@block_merge g127 7 845 48 48 g127P7_845 g127P7_893)) (@block_merge g127 7 941 96 96 (@block_merge g127 7 941 48 48 g127P7_941 g127P7_989) (@block_merge g127 7 1037 48 48 g127P7_1037 g127P7_1085)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_48 : block g127 8 48 41=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_89 : block g127 8 89 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_137 : block g127 8 137 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_185 : block g127 8 185 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_233 : block g127 8 233 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_281 : block g127 8 281 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_329 : block g127 8 329 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_377 : block g127 8 377 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_425 : block g127 8 425 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_473 : block g127 8 473 33=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_506 : block g127 8 506 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_554 : block g127 8 554 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_602 : block g127 8 602 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_650 : block g127 8 650 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_698 : block g127 8 698 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_746 : block g127 8 746 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_794 : block g127 8 794 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_842 : block g127 8 842 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_890 : block g127 8 890 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_938 : block g127 8 938 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_986 : block g127 8 986 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 1005=true := (@block_merge g127 8 0 506 499 (@block_merge g127 8 0 233 273 (@block_merge g127 8 0 89 144 (@block_merge g127 8 0 48 41 g127P8_0 g127P8_48) (@block_merge g127 8 89 48 96 g127P8_89 (@block_merge g127 8 137 48 48 g127P8_137 g127P8_185))) (@block_merge g127 8 233 144 129 (@block_merge g127 8 233 48 96 g127P8_233 (@block_merge g127 8 281 48 48 g127P8_281 g127P8_329)) (@block_merge g127 8 377 48 81 g127P8_377 (@block_merge g127 8 425 48 33 g127P8_425 g127P8_473)))) (@block_merge g127 8 506 240 259 (@block_merge g127 8 506 96 144 (@block_merge g127 8 506 48 48 g127P8_506 g127P8_554) (@block_merge g127 8 602 48 96 g127P8_602 (@block_merge g127 8 650 48 48 g127P8_650 g127P8_698))) (@block_merge g127 8 746 144 115 (@block_merge g127 8 746 48 96 g127P8_746 (@block_merge g127 8 794 48 48 g127P8_794 g127P8_842)) (@block_merge g127 8 890 48 67 g127P8_890 (@block_merge g127 8 938 48 19 g127P8_938 g127P8_986)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_14 : block g127 9 14 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_62 : block g127 9 62 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_110 : block g127 9 110 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_158 : block g127 9 158 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_206 : block g127 9 206 45=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 251=true := (@block_merge g127 9 0 110 141 (@block_merge g127 9 0 14 96 g127P9_0 (@block_merge g127 9 14 48 48 g127P9_14 g127P9_62)) (@block_merge g127 9 110 48 93 g127P9_110 (@block_merge g127 9 158 48 45 g127P9_158 g127P9_206)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_2 : block g127 10 2 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 21=true := (@block_merge g127 10 0 2 19 g127P10_0 g127P10_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B11 : block g127 11 0 1=true := g127P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127R : Impossible true graph 11 nineInputs.toFinset := by
  rw [show graph = targetOf g127 by decide +kernel]
  exact root_index (g:=g127) (top:=11) (i:=0) (before_sound K126 V126) g127G g127T (by decide) (by decide +kernel)

def flatValue (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem flat_correct : ∀ x : Fin 7 → Bool, nineEdge x = flatValue x := by decide +kernel


end PEqualNP.Outside.L_meta_30218.Core7

namespace PEqualNP.Outside.L_meta_30218
namespace Paid


def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF := (Fin 8 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 8) : BF := fun x => x i

def zF : BF := fun _ => false

def rst (p : Fin 8) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 8 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 8} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 8} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 8) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 8} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 8} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 8 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 8) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 8) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 8) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 8) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 8) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 8 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 8 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def graphTable (a : ℕ) (x : Fin 8 → Bool) : Bool := a.testBit (tableIndex x)

def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [if_neg (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 8)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

theorem remove_var (F : BF) (p : Fin 8) (xs : Finset (Fin 8)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : rst p F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ t, t + 1 ≤ s ∧ UC gF (fun _ => True) t (sourceVars (xs.erase p)) (rst p F) := by
  have hf : F ≠ zF := fun e => hn (by rw [e]; rfl)
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun e => hmiss (e ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  have hc : 1 ≤ dcount p ws := by
    apply Nat.succ_le_of_lt
    unfold dcount
    exact List.countP_pos_iff.2 ⟨var p, hp, by simp [rst_var_self]⟩
  have dr := pot_dead p hn (TR.monoC (fun _ _ _ _ => trivial) run)
  refine ⟨k - dcount p ws, by omega, dr.2 (sourceVars (xs.erase p)) ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun e => hz (e ▸ rst_var_self p)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rst_var_ne hne⟩


end Paid

namespace SignedLift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev zeroGate := Paid.zeroGate
abbrev UC {α : Type} := @Paid.UC α
abbrev BF (n : Nat) := (Fin n → Bool) → Bool

def signed {n : Nat} (k : Fin 4) (a b : BF n) : BF n := fun x => zeroGate k (a x) (b x)

def binary (g : Gate) : Bool := match g.op with | .not => false | _ => true

def ready {n : Nat} (gs : List Gate) (j : Nat) (f : BF n) : Prop :=
  j < n + gs.length ∧ ∀ x : Fin n → Bool, Circuit.eval ⟨gs,j⟩ (List.ofFn x) = f x

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def addWire (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem wireLength {n : Nat} (gs : List Gate) (x : Fin n → Bool) :
    (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).length = n + gs.length := by
  have aux (v : List Bool) (ls : List Gate) : (ls.foldl addWire v).length = v.length + ls.length := by
    induction ls generalizing v with
    | nil => simp
    | cons g ls ih => simp [List.foldl_cons,ih,addWire]; omega
  exact (aux _ _).trans (by simp)

theorem stepW (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g],0⟩ x = addWire (Circuit.wires ⟨gs,0⟩ x) g := by
  simp [Circuit.wires, addWire, List.foldl_append]

theorem keep {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) (g : Gate) :
    ready (gs ++ [g]) j f := by
  refine ⟨by have := h.1; simp; omega, ?_⟩
  intro x
  change (Circuit.wires ⟨gs ++ [g],0⟩ _).getD j false = _
  rw [stepW]
  exact (List.getD_append _ _ _ _ (by rw [wireLength];exact h.1)).trans (h.2 x)

theorem nextWire {n} (gs : List Gate) (g : Gate) (f : BF n)
    (eval : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map (fun j =>
      (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false)) = f x) :
    ready (gs ++ [g]) (n + gs.length) f := by
  refine ⟨by simp, ?_⟩
  intro x
  change (Circuit.wires ⟨gs ++ [g],0⟩ _).getD (n + gs.length) false = _
  rw [stepW,← wireLength gs x]
  simpa [addWire] using eval x

theorem negative {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) :
    ready (gs ++ [⟨.not,[j]⟩]) (n+gs.length) (fun x => !f x) := by
  apply nextWire
  intro x
  have hx : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = f x := h.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,hx]

theorem conjWire {n i j} {gs : List Gate} {a b : BF n} (ha : ready gs i a) (hb : ready gs j b) :
    ready (gs ++ [⟨.and,[i,j]⟩]) (n+gs.length) (fun x => a x && b x) := by
  apply nextWire
  intro x
  have h1 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD i false = a x := ha.2 x
  have h2 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = b x := hb.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,h1,h2,Bool.and_true]

theorem disjWire {n i j} {gs : List Gate} {a b : BF n} (ha : ready gs i a) (hb : ready gs j b) :
    ready (gs ++ [⟨.or,[i,j]⟩]) (n+gs.length) (fun x => a x || b x) := by
  apply nextWire
  intro x
  have h1 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD i false = a x := ha.2 x
  have h2 : (Circuit.wires ⟨gs,0⟩ (List.ofFn x)).getD j false = b x := hb.2 x
  simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,h1,h2,Bool.or_false]

theorem shift {n j} {gs : List Gate} {f : BF n} (h : ready gs j f) (tail : List Gate) :
    ready (gs ++ tail) j f := by
  induction tail using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton _ g ih => simpa [List.append_assoc] using keep ih g

theorem produce {n i j} {gs : List Gate} {a b : BF n} (k : Fin 4)
    (ha : ready gs i a) (hb : ready gs j b) :
    ∃ (tail : List Gate) (r : Nat), (∀ g ∈ tail, legal g) ∧ tail.countP binary = 1 ∧
      ready (gs ++ tail) r (signed k a b) := by
  fin_cases k
  · exact ⟨[⟨.and,[i,j]⟩],_,by simp [legal],rfl,conjWire ha hb⟩
  · exact ⟨[⟨.or,[i,j]⟩],_,by simp [legal],rfl,disjWire ha hb⟩
  · let v : Gate := ⟨.not,[j]⟩
    refine ⟨[v,⟨.and,[i,n+gs.length]⟩],n+(gs++[v]).length,by simp [legal,v],rfl,?_⟩
    change ready _ _ (fun x => a x && !(b x))
    simpa only [List.append_assoc,List.singleton_append] using conjWire (keep ha v) (negative hb)
  · let v : Gate := ⟨.not,[i]⟩
    refine ⟨[v,⟨.and,[n+gs.length,j]⟩],n+(gs++[v]).length,by simp [legal,v],rfl,?_⟩
    change ready _ _ (fun x => !(a x) && b x)
    simpa only [List.append_assoc,List.singleton_append] using conjWire (negative ha) (keep hb v)

theorem realizeAux {n t} (S : BF n → Prop) (f : BF n)
    (h : UC signed (fun _ => True) t S f) (gs : List Gate)
    (fan : ∀ g ∈ gs, legal g) (pool : ∀ w, S w → ∃ i, ready gs i w) :
    ∃ C : Circuit, FanInTwo C ∧ C.gates.countP binary ≤ gs.countP binary + t ∧ circuitFun n C = f := by
  induction t generalizing gs S with
  | zero =>
    obtain ⟨i,e⟩ := pool f h
    exact ⟨⟨gs,i⟩,fan,by simp,funext e.2⟩
  | succ t ih =>
    rcases h with skip | ⟨k,a,b,_,ha,hb,more⟩
    · obtain ⟨C,fanC,lo,eq⟩ := ih S skip gs fan pool
      exact ⟨C,fanC,by omega,eq⟩
    obtain ⟨i,hi⟩ := pool a ha
    obtain ⟨j,hj⟩ := pool b hb
    obtain ⟨tail,r,ok,cost,new⟩ := produce k hi hj
    obtain ⟨C,fanC,lo,eq⟩ := ih _ more (gs++tail)
      (fun g hg => (List.mem_append.mp hg).elim (fan g) (ok g)) (by
        rintro w (rfl | hw)
        · exact ⟨r,new⟩
        · obtain ⟨v,ev⟩ := pool w hw
          exact ⟨v,shift ev tail⟩)
    rw [List.countP_append,cost] at lo
    exact ⟨C,fanC,by omega,eq⟩

theorem realize {n t} (f : BF n)
    (h : UC signed (fun _ => True) t (fun w => ∃ i : Fin n, w = fun x => x i) f) :
    ∃ C : Circuit, FanInTwo C ∧ C.gates.countP binary ≤ t ∧ circuitFun n C = f := by
  have p : ∀ w : BF n, (∃ i : Fin n, w = fun x => x i) → ∃ j, ready [] j w := by
    rintro w ⟨i,rfl⟩
    exact ⟨i.val,by simp [ready,i.isLt,Circuit.eval,Circuit.wires]⟩
  simpa using realizeAux _ f h [] (by simp) p


end SignedLift
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target8 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 7) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def witness : List Gate := [⟨.or, [5, 7]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 12]⟩, ⟨.and, [13, 9]⟩, ⟨.and, [14, 8]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩]
theorem witnessBasis : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = target8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, target8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
open Paid in
theorem lower_using_binary
    (coreLow : ∀ C : Circuit, FanInTwo C → circuitFun 7 C = Core7.flatValue →
        12 ≤ C.gates.countP SignedLift.binary)
    (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = target8 x)
    (hasNot : ∃ g ∈ gates, g.op = GateOp.not) : 14 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = target8 := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (show target8 (fun _ => false) = false by decide)] at start
  rcases start with e | run
  · exact False.elim ((by decide : target8 (fun i : Fin 8 => (129 : ℕ).testBit i.val) ≠ zF (fun i : Fin 8 => (129 : ℕ).testBit i.val)) (congrFun e _))
  have inf : ∃ x, rst 2 target8 x ≠ target8 x := ⟨(fun i : Fin 8 => (132 : ℕ).testBit i.val), by decide⟩
  have nz : rst 2 target8 ≠ zF := fun e => (by decide : rst 2 target8 (fun i : Fin 8 => (129 : ℕ).testBit i.val) ≠ zF (fun i : Fin 8 => (129 : ℕ).testBit i.val)) (congrFun e _)
  obtain ⟨k, paid, small⟩ := remove_var target8 2 Finset.univ _ inf nz run
  let π : Fin 8 → Fin 7 := ![6, 5, 0, 2, 1, 3, 4, 0]
  let lift (w : BF) : SignedLift.BF 7 := fun y => w (y ∘ π)
  have sources : ∀ w, sourceVars (Finset.univ.erase 2) w →
      ∃ i : Fin 7, lift w = fun y => y i := by
    rintro w ⟨i,_hi,rfl⟩
    exact ⟨π i,rfl⟩
  have hom : ∀ op a b, lift (gF op a b) = SignedLift.signed op (lift a) (lift b) := by intros; rfl
  have mapped := UC_map (G := gF) (G' := SignedLift.signed) (A := fun _ => True) lift hom k
    (sourceVars (Finset.univ.erase 2)) (fun w => ∃ i : Fin 7, w = fun y => y i) (rst 2 target8) sources small
  obtain ⟨C,fan,ct,hc⟩ := SignedLift.realize _ mapped
  have eqn : lift (rst 2 target8) = Core7.flatValue := by
    funext y
    exact (by decide +kernel : ∀ z : Fin 7 → Bool, lift (rst 2 target8) z = Core7.flatValue z) y
  have bound := coreLow C fan (hc.trans eqn)
  have hneg := countBinary_lt gates hasNot
  omega
theorem coreLower (C : Circuit) (fan : FanInTwo C) (hc : circuitFun 7 C = Core7.flatValue) : 12 ≤ C.gates.countP SignedLift.binary := by
  have he : Core7.nineEdge = Core7.flatValue := funext Core7.flat_correct
  have bound := Core7.binaryLower C fan (hc.trans he.symm) Core7.g127R
  have e : (fun g : Gate => !Core7.isNot g) = SignedLift.binary := by
    funext g
    cases g with
    | mk op ins => cases op <;> rfl
  rw [e] at bound
  exact bound
end PEqualNP.Outside.L_meta_30218
open PEqualNP.Outside.L_meta_30218 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_30218 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have comp : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target8 x := fun x => (computes x).trans (graph_correct x).symm
    have large := lower_using_binary coreLower gates o legal comp hnot
    have hw : witness.length ≤ 14 := by decide
    exact ⟨witness, 21, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g,hg,h⟩)

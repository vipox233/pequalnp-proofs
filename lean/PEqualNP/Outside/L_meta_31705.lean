import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31705
open PEqualNP.CircuitLowerBounds
def natLimbs (xs : List Nat) : Nat := xs.foldl (fun a n => (a <<< 80) + n) 0
def bitLimbs {n : Nat} (xs : List Nat) : BitVec n := BitVec.ofNat n (natLimbs xs)
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

def Live (u : Bool) (donorTarget : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={donorTarget} ∧ proper donorTarget
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u donorTarget k (insert (bin d a b) U)
theorem Live.stop {u} {donorTarget : Sig} (hp : proper donorTarget) : Live u donorTarget 0 {donorTarget} := ⟨rfl,hp⟩
theorem Live.binary {u} {donorTarget : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u donorTarget k (insert (bin d a b) U)) :
    Live u donorTarget (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {donorTarget : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u donorTarget k S → Prop}
    (stop : ∀ (hp : proper donorTarget), motive 0 {donorTarget} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u donorTarget k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u donorTarget k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u donorTarget k S} (h : Live u donorTarget k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u donorTarget k S} (h : Live u donorTarget k S) : S.card ≤ k+1 := by
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

private lemma pull_gate {u donorTarget} {w : List Sig} {z : Sig} {k S c} (h : Live u donorTarget k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u donorTarget k' S' ∧ ∀ a ∈ S', a ∈ w := by
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
        have ht : Live u donorTarget k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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

private lemma extract {u donorTarget} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper donorTarget) (hout : donorTarget ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u donorTarget k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{donorTarget},by simp,Live.stop hp,by simpa [execute] using hout⟩
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

def inputs : List Sig := [(bitLimbs [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa]),(bitLimbs [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc]),(bitLimbs [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0]),(bitLimbs [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00]),(bitLimbs [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000]),(bitLimbs [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000]),(bitLimbs [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,65535,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000]),(bitLimbs [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,65535,0xffffffffffffffffffff,0xffffffff000000000000,0]),(bitLimbs [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0])]
def graph : Sig := (bitLimbs [0xfffffffe,0xfffffffefffffffeffff,0xfffefffffefeffffeeee,0xfefefafaeeee0000ffff,0xfffefffffffefffffffe,0xfffffffefffffefeffff,0xeeeefefefafaeeee0000])
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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
  | 0 => (natLimbs [0x1000000000000,0x10000000000000001,65536,4294967296,0x1000000000000,0x10000000000000001])
  | 1 => (natLimbs [0x10000000000000000,65536,0,0x1000000000000,1])
  | 2 => (natLimbs [1,65536,0,0,0x10000000000000001])
  | 3 => (natLimbs [65536,0,0,1])
  | 4 => (natLimbs [4294967296,0x1000000000000,0x10000000000000001])
  | 5 => (natLimbs [0x1000000000000,1])
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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

def g81Y : Array (Bits × Bits) := #[((bitLimbs [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f]),(bitLimbs [0x492049204920492049,0x20492049204920492049])),(0x0,0x0),(0x0,0x0),(0x0,0x0),((bitLimbs [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7]),(bitLimbs [0x924092409240924092,0x40924092409240924092])),(0x0,0x0),((bitLimbs [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8]),(bitLimbs [0x248124812481248124,0x81248124812481248124])),(0x0,0x0),(0x0,0x0)]
def g81C : List ColumnInfo := []
def g81A : List (List Nat) := [[],[100],[64],[64,96],[96,64],[96]]
def g81D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g81L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g81D3)
  | _ => emptyPacking
def g81I (_ _ : Nat) : Option (Nat × Nat) := none
def g81 : Forest := ⟨81,3,fun i => g81Y[i]?.getD (0,0),g81C,g81A,g81L,g81I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81P3_0 : block g81 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g81B3 : block g81 3 0 1=true := g81P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81T : checkedTables g81 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g81 0 0 0 = true)
  · exact (rfl : block g81 1 0 0 = true)
  · exact (rfl : block g81 2 0 0 = true)
  · exact g81B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81G : graphValid g81 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low81 : Lower true (varsX 81) (graphGoal 81) 4 := lower_forest (g:=g81) (i:=0) (hints:=4) (before_sound [] baseKnown) g81G g81T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K81 := extendKnown [] 4 [(81,[]),(82,[16]),(146,[16,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V81 : Known true K81 := extend_ok (m:=81) baseKnown low81 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((bitLimbs [0xf71fc7ff03fffff8f7,0x1fc7ff03fffff8f71fc7]),(bitLimbs [0x710490a2850401207,0x10490a28504012071049])),((bitLimbs [0xbe838fffc07e3ff0b,0xe838fffc07e3ff0be838]),(bitLimbs [0x4368db4c3260892043,0x68db4c326089204368db])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xeee63ffffff803ffee,0xe63ffffff803ffeee63f]),(bitLimbs [0x88724904085124008,0x87249040851240088724])),((bitLimbs [0x193dc0fffffffc0019,0x3dc0fffffffc00193dc0]),(bitLimbs [0x982db6e08306038498,0x2db6e083060384982db6])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := []
def g51A : List (List Nat) := [[],[64,81]]
def g51D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g51L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g51D3)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,3,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P3_0 : block g51 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B3 : block g51 3 0 1=true := g51P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact g51B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K81) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K81 V81) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K81 4 [(51,[]),(53,[33,84]),(99,[100]),(101,[33,84,100]),(166,[32,116,100]),(169,[49,33,116,100]),(172,[32,49,116,100]),(180,[32,65,49,115,99]),(197,[33,116,101,84]),(202,[16,48,32,116,101,84]),(212,[64,33,16,49,115,101,83]),(216,[64,49,32,114,101,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V81 low51 (by decide +kernel)
def g83Y : Array (Bits × Bits) := #[((bitLimbs [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7]),(bitLimbs [0x51d124928a290a051,0xd124928a290a051d1249])),((bitLimbs [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38]),(bitLimbs [0x884b924930c3210884,0xb924930c3210884b9249])),(0x0,0x0),(0x0,0x0),((bitLimbs [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f]),(bitLimbs [0x100024924104020100,0x2492410402010002492])),(0x0,0x0),((bitLimbs [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0]),(bitLimbs [0x200049248208040200,0x4924820804020004924])),(0x0,0x0),(0x0,0x0)]
def g83C : List ColumnInfo := [(1,0,82,0,4)]
def g83A : List (List Nat) := [[],[100],[16],[16,100]]
def g83D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g83L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g83D4)
  | _ => emptyPacking
def g83I (_ _ : Nat) : Option (Nat × Nat) := none
def g83 : Forest := ⟨83,4,fun i => g83Y[i]?.getD (0,0),g83C,g83A,g83L,g83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83P4_0 : block g83 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g83B4 : block g83 4 0 1=true := g83P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83T : checkedTables g83 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g83 0 0 0 = true)
  · exact (rfl : block g83 1 0 0 = true)
  · exact (rfl : block g83 2 0 0 = true)
  · exact (rfl : block g83 3 0 0 = true)
  · exact g83B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 5 := lower_forest (g:=g83) (i:=0) (hints:=68) (before_sound K51 V51) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K51 5 [(83,[]),(209,[96,113,33,50,64,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V51 low83 (by decide +kernel)
def g113Y : Array (Bits × Bits) := #[((bitLimbs [0xfdb07fff83ffe7fffb,0x60ffff07ffcffff6c1ff]),(bitLimbs [0x92410820400800,0x1248210408010000249])),(0x0,0x0),(0x0,0x0),(0x0,0x0),((bitLimbs [0x3bcf81fffc0ff8fc77,0x9f03fff81ff1f8ef3e07]),(bitLimbs [0x81c5248a1142821103,0x8a491422850422071492])),((bitLimbs [0xc6940e3ffff000ff8d,0x281c7fffe001ff1a5038]),(bitLimbs [0x16976dac218b14a02d,0x2edb58431629405a5db6])),((bitLimbs [0x66ff03fffffff000c,0xdfe07ffffffe0019bfc0]),(bitLimbs [0x262a4930420c00c24c,0x5492608418018498a924])),(0x0,0x0),(0x0,0x0)]
def g113C : List ColumnInfo := [(32,0,81,0,4)]
def g113A : List (List Nat) := [[],[100]]
def g113D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g113L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g113D4)
  | _ => emptyPacking
def g113I (_ _ : Nat) : Option (Nat × Nat) := none
def g113 : Forest := ⟨113,4,fun i => g113Y[i]?.getD (0,0),g113C,g113A,g113L,g113I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P4_0 : block g113 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g113B4 : block g113 4 0 1=true := g113P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113T : checkedTables g113 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g113 0 0 0 = true)
  · exact (rfl : block g113 1 0 0 = true)
  · exact (rfl : block g113 2 0 0 = true)
  · exact (rfl : block g113 3 0 0 = true)
  · exact g113B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113G : graphValid g113 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low113 : Lower true (varsX 113) (graphGoal 113) 5 := lower_forest (g:=g113) (i:=0) (hints:=4) (before_sound K83 V83) g113G g113T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K113 := extendKnown K83 5 [(113,[]),(149,[112,50,82,64,100]),(150,[112,16,50,82,65,100]),(153,[112,83,64,100]),(177,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V113 : Known true K113 := extend_ok (m:=113) V83 low113 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((bitLimbs [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f]),(bitLimbs [0x41a8128d052280541a,0x82502916291304a21111])),((bitLimbs [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0]),(bitLimbs [0x81311b160644c89893,0x136232244d835c485555])),((bitLimbs [0xffffffff80001fffff,0xfff80000003f407df000]),(bitLimbs [0x5c05c18178702e01c,0x380bc38703340753333])),(0x0,0x0),((bitLimbs [2097151,0xfffffffffe663f7600ff]),(bitLimbs [0x160260205808130120,0x2404c00000642314aaaa])),((bitLimbs [0xffffffffffffe00000,0x19dd38dff00]),(bitLimbs [0x1803800060001c01c0,0x38070040808c9308cccc])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[33,84]]
def g55D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : block g55 4 0 1=true := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K113) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K113 V113) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K113 5 [(55,[]),(230,[112,81,98,48,66,67]),(244,[112,81,98,48,66,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V113 low55 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((bitLimbs [0xfe007fe1ff0fffc03f,0xffffff0ff9621a00ff0f]),(bitLimbs [0x140501440220028281,0x4040022088420a111111])),((bitLimbs [0xffff8001fff0ffffc0,0x1fe1fff01c1fa90f00f0]),(bitLimbs [0x982609882402130309,0x80842402180f09333333])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xfffffffe0000ffffff,0xe001ffff239766f000ff]),(bitLimbs [0x204812004844240402,0x5084800211064444444])),((bitLimbs [0xffffff,0xfffe00001369f8000f00]),(bitLimbs [0xc1705c117088b8282c,0x160170441329f0eeeeee])),((bitLimbs [0xffffffffffff000000,0xcea8c5fff000]),(bitLimbs [0x18060018000c03030,0x1811808846a080888888])),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,32,82,1,5),(2,0,113,0,5),(32,0,83,0,5),(1,32,82,0,4),(16,0,99,0,4),(64,0,51,0,4)]
def g115A : List (List Nat) := [[],[100]]
def g115D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5dd4542
def g115D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x108404fd42
def g115H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50
def g115D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2c458bf
def g115H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x90
def g115L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g115D4)
  | 5 => (1,1,3,0,0,0,0,g115D5)
  | 6 => (1,0,3,0,0,0,0,g115D6)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g115H5
  | 6 => lookupWord 1 2 0 4 0 0 g115H6
  | _ => fun _ => none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : block g115 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B4 : block g115 4 0 1=true := g115P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 1=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : block g115 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B6 : block g115 6 0 1=true := g115P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact g115B4
  · exact g115B5
  · exact g115B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := lower_forest (g:=g115) (i:=0) (hints:=68) (before_sound K55 V55) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K55 7 [(179,[118]),(213,[112,97,33,64,82,84]),(217,[112,97,33,50,64,83,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V55 low115 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((bitLimbs [0xf007ff0ffffff007ff,0xff87ffffd45c460f83ff]),(bitLimbs [0xa0500a201000a05014,0x1100082401806108421])),(0x0,0x0),((bitLimbs [0xfff8000ff87ffff801,0xfff87fc05373b2007c00]),(bitLimbs [0xc0622c40a122c46258,0x8a012108527132b5ad6b])),(0x0,0x0),((bitLimbs [0xfffffff0007ffffffe,0x7ffcafd11df0001f]),(bitLimbs [0x280b002c20b008060,0x2c220a00a541186318c6])),((bitLimbs [0x7fffffff,0xffff80004d2fe8007fe0]),(bitLimbs [0xb04c08b044c090481,0x30004c100d06c94a5294])),((bitLimbs [0xffffffffff80000000,0x33aa61bff8000]),(bitLimbs [0xc07000c00700e0701,0xc04470211aa6018c6318])),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(0,4,81,32,5),(4,0,113,0,5),(16,0,101,0,4),(32,4,81,0,4),(64,0,53,0,4)]
def g117A : List (List Nat) := [[],[100]]
def g117D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fd5120
def g117D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [16520,0x480e140fd42fe20fd20])
def g117H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2
def g117D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g117H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x7000000000000a0,0,0x4a000000000014000,0x28800000000])
def g117L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g117D4)
  | 5 => (3,1,3,0,0,5,0,g117D5)
  | 6 => (1,0,3,0,0,0,0,g117D6)
  | _ => emptyPacking
def g117I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g117H5
  | 6 => lookupWord 1 43 0 7 2 1 g117H6
  | _ => fun _ => none
def g117 : Forest := ⟨117,6,fun i => g117Y[i]?.getD (0,0),g117C,g117A,g117L,g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P4_0 : block g117 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B4 : block g117 4 0 1=true := g117P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P5_0 : block g117 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B5 : block g117 5 0 3=true := g117P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P6_0 : block g117 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B6 : block g117 6 0 1=true := g117P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g117 0 0 0 = true)
  · exact (rfl : block g117 1 0 0 = true)
  · exact (rfl : block g117 2 0 0 = true)
  · exact (rfl : block g117 3 0 0 = true)
  · exact g117B4
  · exact g117B5
  · exact g117B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 7 := lower_forest (g:=g117) (i:=0) (hints:=1284) (before_sound K115 V115) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K115 7 [(117,[]),(182,[112,16,82,65,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V115 low117 (by decide +kernel)
def g151Y : Array (Bits × Bits) := #[((bitLimbs [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7]),(bitLimbs [0xa0a86a128d0a458a05,0x46a250a4b29029d49249])),((bitLimbs [0xfffff00007fffc07f,0xfff007fff813a68c0e38]),(bitLimbs [0xc1304c1b160c891309,0x84c360c924d1a28c9249])),((bitLimbs [0xfffffffff8000007f,0xfffff800000bc8b47000]),(bitLimbs [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db])),(0x0,0x0),((bitLimbs [0xf0000000000000007f,0xffffffffffe6fe67803f]),(bitLimbs [0x60180602030102030,0x8040300000654212492])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xffffffffffffffff80,0x1911bbffc0]),(bitLimbs [0x80200800040000040,0x10080400000000024924])),(0x0,0x0)]
def g151C : List ColumnInfo := [(1,0,150,0,5)]
def g151A : List (List Nat) := [[],[16]]
def g151D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g151L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g151D5)
  | _ => emptyPacking
def g151I (_ _ : Nat) : Option (Nat × Nat) := none
def g151 : Forest := ⟨151,5,fun i => g151Y[i]?.getD (0,0),g151C,g151A,g151L,g151I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151P5_0 : block g151 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151B5 : block g151 5 0 1=true := g151P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151T : checkedTables g151 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g151 0 0 0 = true)
  · exact (rfl : block g151 1 0 0 = true)
  · exact (rfl : block g151 2 0 0 = true)
  · exact (rfl : block g151 3 0 0 = true)
  · exact (rfl : block g151 4 0 0 = true)
  · exact g151B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=1860) (before_sound K117 V117) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K117 6 [(151,[]),(241,[96,113,82,49,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V117 low151 (by decide +kernel)
def g157Y : Array (Bits × Bits) := #[((bitLimbs [0x3ffc003ffc01ffe00f,0xfffffffffffeddea003f]),(bitLimbs [0x80a81a8128340a4160,0xa02a094148524c6a1249])),(0x0,0x0),((bitLimbs [0x3fffffc00001fffff0,0x7ff001ffc0118f681c0]),(bitLimbs [0x15315315b158ac8a45,0x314c6d89919918f6b6db])),((bitLimbs [0x3ffffffffffe000000,0x7ffffe000031f070e00]),(bitLimbs [0x19c19c19c260cf1389,0xc2704e0de2e31f0736db])),((bitLimbs [0xc00000000000000000,0x7fffffffffcbfdc7007]),(bitLimbs [0x1e01e01e0380f01c0e,0x380700e0300b3942492])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xffffffffffffffffff,0xf800000000036237fff8]),(bitLimbs [0x200200200001000000,0x4008010000000004924])),(0x0,0x0)]
def g157C : List ColumnInfo := [(4,0,153,0,5)]
def g157A : List (List Nat) := [[],[50],[64],[64,50]]
def g157D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g157L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g157D5)
  | _ => emptyPacking
def g157I (_ _ : Nat) : Option (Nat × Nat) := none
def g157 : Forest := ⟨157,5,fun i => g157Y[i]?.getD (0,0),g157C,g157A,g157L,g157I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157P5_0 : block g157 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g157B5 : block g157 5 0 1=true := g157P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157T : checkedTables g157 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g157 0 0 0 = true)
  · exact (rfl : block g157 1 0 0 = true)
  · exact (rfl : block g157 2 0 0 = true)
  · exact (rfl : block g157 3 0 0 = true)
  · exact (rfl : block g157 4 0 0 = true)
  · exact g157B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157G : graphValid g157 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low157 : Lower true (varsX 157) (graphGoal 157) 6 := lower_forest (g:=g157) (i:=0) (hints:=30468) (before_sound K151 V151) g157G g157T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K157 := extendKnown K151 6 [(157,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V157 : Known true K157 := extend_ok (m:=157) V151 low157 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((bitLimbs [0xe003ff80ffe03ffff0,0x3ff80ffff909e9b81c7]),(bitLimbs [0x41a8251a0a458a02a1,0xa8251a148a00928b9249])),((bitLimbs [0xfffc0000ffffc07fff,0xfc0000ffc068da648e00]),(bitLimbs [0x8530b62c2c891314c1,0x30b62c191348da44b6db])),((bitLimbs [0xffffffff0000007fff,0xffffff00000ff10e7038]),(bitLimbs [0x1c038300f0e1c0701,0xc038301e1c02d10e1249])),(0x0,0x0),(0x0,0x0),((bitLimbs [32767,0xffffffffff99af6d003f]),(bitLimbs [0x1602c040b01020580a,0x2c000a000192c606db6])),(0x0,0x0),((bitLimbs [0xffffffffffffff8000,0x6754f2ffc0]),(bitLimbs [0x18030000c00000600c,0x30040c0202504304924])),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,4)]
def g167A : List (List Nat) := [[],[32]]
def g167D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g167L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g167D4)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,4,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P4_0 : block g167 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B4 : block g167 4 0 1=true := g167P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact g167B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K157) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 5 := lower_forest (g:=g167) (i:=0) (hints:=1397) (before_sound K157 V157) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K157 5 [(167,[]),(173,[49]),(203,[49,33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V157 low167 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((bitLimbs [0xf8003ffe00fff803ff,0xfffffffffffb5d61e03f]),(bitLimbs [0x501a80941a02905828,0x540940a414940616249])),((bitLimbs [0xffffc00000fffffc01,0xffe001ffe008a3d3c1c0]),(bitLimbs [0x61530ad8ac2b22914c,0x2986d84c8668a351c6db])),(0x0,0x0),((bitLimbs [0xffffffffff00000001,0xfffffe000004e42dde00]),(bitLimbs [0x819c0ce13033c4e270,0x4e04e06f0b84e429c6db])),(0x0,0x0),((bitLimbs [1,0xfffffffffff22feda007]),(bitLimbs [0x5e02f01c0bc070381,0x701701700c022f8c8db6])),(0x0,0x0),((bitLimbs [0xfffffffffffffffffe,0xdfa9e5ff8]),(bitLimbs [0x600300000c0000001,0x80180180100018861924])),(0x0,0x0)]
def g171C : List ColumnInfo := [(2,0,169,0,4)]
def g171A : List (List Nat) := [[],[49]]
def g171D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g171L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g171D4)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,4,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 1=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 5 := lower_forest (g:=g171) (i:=0) (hints:=28789) (before_sound K167 V167) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K167 5 [(174,[32]),(188,[32,49,65]),(205,[33,101]),(206,[16,32,101]),(220,[64,33,16,101]),(233,[112,81,33,99,66,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V167 low171 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((bitLimbs [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff]),(bitLimbs [0xa0501440220028281,0x40220020980602111111])),(0x0,0x0),((bitLimbs [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00]),(bitLimbs [0x2c06058814020b0305,0x81402042183511333333])),(0x0,0x0),((bitLimbs [0xfffffffe0000ffffff,0xe0000fff23b566f0000f]),(bitLimbs [0xb028160058442c0406,0x5844280213164666666])),((bitLimbs [0xffffff,0xfffff000134bf8000ff0]),(bitLimbs [0xc0b058116088b02828,0x16000b040348e8cccccc])),(0x0,0x0),((bitLimbs [0xffffffffffff000000,0xcea8c5fff000]),(bitLimbs [0xc060018000c03030,0x18088c08468880888888])),(0x0,0x0)]
def g181C : List ColumnInfo := [(4,0,177,0,5)]
def g181A : List (List Nat) := [[],[112,82]]
def g181D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g181L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g181D5)
  | _ => emptyPacking
def g181I (_ _ : Nat) : Option (Nat × Nat) := none
def g181 : Forest := ⟨181,5,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : block g181 5 0 1=true := g181P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact (rfl : block g181 3 0 0 = true)
  · exact (rfl : block g181 4 0 0 = true)
  · exact g181B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 6 := lower_forest (g:=g181) (i:=0) (hints:=1284) (before_sound K171 V171) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K171 6 [(181,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V171 low181 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[((bitLimbs [0xc007ff80ffe03fffff,0xffffffffff98eb9d81ff]),(bitLimbs [0x8050050200408000a0,0x14010000800003899249])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xfff80000ffffc07ff0,0x1ff80ffc0619e0e8e00]),(bitLimbs [0xa61562c2a8a150ac3,0x584a1a290b419a0eb6db])),((bitLimbs [0xffffffff0000007fff,0xfe0000ffff9f8a637007]),(bitLimbs [0xc8198483313261302,0x606c2c32121b88422492])),((bitLimbs [32767,0xffffff000009f56c0038]),(bitLimbs [0x2f05e070bc1c385c0b,0x817030bc1c09f4646db6])),(0x0,0x0),((bitLimbs [0xffffffffffffff8000,0x6754f2ffc0]),(bitLimbs [0x30060000c00000600c,0x18040c0202444304924])),(0x0,0x0)]
def g185C : List ColumnInfo := [(8,0,177,0,5)]
def g185A : List (List Nat) := [[],[112,83]]
def g185D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g185L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g185D5)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,5,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P5_0 : block g185 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B5 : block g185 5 0 1=true := g185P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact (rfl : block g185 4 0 0 = true)
  · exact g185B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 6 := lower_forest (g:=g185) (i:=0) (hints:=28676) (before_sound K181 V181) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K181 6 [(185,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V181 low185 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((bitLimbs [0xfff0007ffffff00ff5,0xb261513c2a0001f07c1f]),(bitLimbs [0x2a035012805216141,0xb0605114080842108421])),((bitLimbs [0xffffff8003fffff002,0x17e8d44785003e0003e0]),(bitLimbs [0x44c12609b046424262,0x1360d40781294a5294a5])),((bitLimbs [0xfffffffffc00000009,0xd8c2c299d107c00f8000]),(bitLimbs [0x17003801c017838381,0x98c2c018d118c6318c63])),(0x0,0x0),((bitLimbs [0xfffffffffffffffffa,0x4fe283ab8f8000003ff]),(bitLimbs [0x980240120098000008,0x48a2828305294a5294a])),((bitLimbs [9,0x1711a3877600000ffc00]),(bitLimbs [0xe00b805c02e0040408,0x711228326e739ce739c])),(0x0,0x0),((bitLimbs [4,0xe9177e4005fffff00000]),(bitLimbs [0xc00600300080804,0x40150240048421084210])),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(4,0,179,0,7),(0,32,146,5,6),(2,0,181,0,6),(32,0,151,0,6),(16,0,167,0,5),(34,0,149,0,5),(128,0,55,0,5),(17,0,166,0,4),(130,0,53,0,4)]
def g183A : List (List Nat) := [[]]
def g183D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [6203,0xe35cafb299a06b654d85,0x53d6aa9b0aa77c5c0615,0x4f3ab2ea398dd573d473,0x1eaaa7a8e633ddc5654c,0x71fb2aa898f555354531])
def g183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [1581954,0x38204608f18400608000,0x60860800060800003820,0x608e08a3e01e008f804,0x2e0386390149a350e843,0xf1d4e46c34998c05a2b9,0x509c4b241147e3c1b0c0,0x481e0a82400bf59653ef,0x95253ef55253bf58653e,0xf95153ef55153bfd8553,0xfdd8553fd18553bf58f5,0x1df54f51df54d51bf597,0x31ef55331f754f31fdd4,0x731bfd9531bf59531ef5,0x5131f794d31f754d31fd,0x54531d7d4e53bdd8553b,0xb58853bd58453be58053])
def g183H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x98d10026,0x90006700e423822500])
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0xa41460918e41,0x8a3028e410ce58c07194,0x828c1239451818e314d1,0x82453c60628a72c60614,0x478c0c291228c059d445,0xd0bf4d9f0ba3e0f803fe,0xa7fe53fea9ff14ffea3f,0xd51ff98ff4c77ca9bd54])
def g183H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [4,0xad700298000058400009,0x78e350702d636c1f1496,0x132c00fa80000f39beae,0xd200d3800014242803b2,0x45187661c0340880])
def g183D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3421017f
def g183H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x4a7000000000000,0x1100000000a500000000,0x330068000086f00089a2])
def g183L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g183D5)
  | 6 => (27,2,4,0,0,9,0,g183D6)
  | 7 => (10,1,4,0,0,9,0,g183D7)
  | 8 => (1,0,4,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 0 8 4 0 g183H6
  | 7 => lookupWord 6 41 6 9 5 0 g183H7
  | 8 => lookupWord 2 29 0 8 4 0 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B5 : block g183 5 0 9=true := g183P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_5 : block g183 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 27=true := (@block_merge g183 6 0 5 22 g183P6_0 g183P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_2 : block g183 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 10=true := (@block_merge g183 7 0 2 8 g183P7_0 g183P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : block g183 8 0 1=true := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact g183B5
  · exact g183B6
  · exact g183B7
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1348) (before_sound K185 V185) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K185 9 [(245,[112,97,82,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V185 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((bitLimbs [0xf80007fffffffc003f,0xfe58982e6f0e9000ff0f]),(bitLimbs [0x500350025001480580,0x5250080e420c81111111])),((bitLimbs [0xfffff80007ffffffc0,0x1e5abae1059200f00f0]),(bitLimbs [0x605260536051904904,0x99e5892e005803333333])),(0x0,0x0),((bitLimbs [0xfffffffff800000000,0x736c73275500f00000]),(bitLimbs [0x816381638165e09e09,0xe0712c73275507777777])),((bitLimbs [0xffffffffffffffffff,0xfc85361697b1df0000ff]),(bitLimbs [0x18401840186011011,0x3610958114444444])),(0x45d5e0f96f00000f00,(bitLimbs [0x5f805f805f801e01e,0x5d5e0b9630eeeeeee])),(0x0,0x0),(0x33a4dd980e26ffff000,(bitLimbs [0x60006000600020020,0xa4080002268888888])),(0x0,0x0)]
def g187C : List ColumnInfo := [(8,0,179,0,7)]
def g187A : List (List Nat) := [[]]
def g187D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g187L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g187D7)
  | _ => emptyPacking
def g187I (_ _ : Nat) : Option (Nat × Nat) := none
def g187 : Forest := ⟨187,7,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 1=true := g187P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact (rfl : block g187 5 0 0 = true)
  · exact (rfl : block g187 6 0 0 = true)
  · exact g187B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 8 := lower_forest (g:=g187) (i:=0) (hints:=28740) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 8 [(249,[112,97,33,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((bitLimbs [0x3ffffffffffffffff,0xfe98baae071c9000f0ff]),(bitLimbs [0x5805000a8012801480,0x5290a82c040881111111])),(0x0,0x0),((bitLimbs [0xfc003fffc0003fffc0,0x1e50b787c19200f0f00]),(bitLimbs [0x9029805300db009901,0x99a50b38641803333333])),((bitLimbs [0x3fffffffc00000,0x73cd25275700f00000]),(bitLimbs [0xe0ce0a9c0a9c0ade0a,0xe071cd25271707777777])),((bitLimbs [0x3fffffffffffff,0xfc85171497b3df00000f]),(bitLimbs [0x1700ce00ce00ce013,0x51710939316666666])),((bitLimbs [0xffffc0000000000000,0x45f4e2f96d00000ff0]),(bitLimbs [0x1802f002f002f001c,0x4054c299650ccccccc])),(0x0,0x0),(0x33a4dd980e26ffff000,(bitLimbs [0x20030003000300020,0xa00c0006068888888])),(0x0,0x0)]
def g189C : List ColumnInfo := [(4,0,185,0,6),(8,0,181,0,6),(32,0,157,0,6),(12,0,177,0,5),(16,0,173,0,5),(9,0,180,0,4),(17,0,172,0,4),(128,0,53,0,4),(128,8,53,0,4)]
def g189A : List (List Nat) := [[]]
def g189D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [37644,0x99ee6b06a52d1d95444,0x2f0b86a4887315454110])
def g189D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [8208,0x3c820140674884d9,0x82a4848600edd8554bb5,0x8f52bb58352cf55150b7,0xd8d50edd9110ed55110f,0x958910f9d4910fc54110])
def g189H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x835ebf000000
def g189D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x28088140628c10240e14,0xa08308540408c8c241b7,0x2a22150d007f54ffaa1b,0xd54f7a97b4cbda41f510])
def g189H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0xe0940067009972,0xf398c600e1f500])
def g189D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8620117f
def g189H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [29952,0x3c000002e0000000002,0x74800002780000000000])
def g189L : Nat → Packing
  | 4 => (4,3,4,0,0,5,0,g189D4)
  | 5 => (10,2,4,0,0,7,0,g189D5)
  | 6 => (7,1,4,0,0,8,0,g189D6)
  | 7 => (1,0,4,0,0,0,0,g189D7)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 6 2 0 g189H5
  | 6 => lookupWord 2 17 0 8 4 0 g189H6
  | 7 => lookupWord 1 29 0 7 3 0 g189H7
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P4_0 : block g189 4 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B4 : block g189 4 0 4=true := g189P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P5_0 : block g189 5 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B5 : block g189 5 0 10=true := g189P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_5 : block g189 6 5 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 7=true := (@block_merge g189 6 0 5 2 g189P6_0 g189P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 1=true := g189P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact g189B4
  · exact g189B5
  · exact g189B6
  · exact g189B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 8 := lower_forest (g:=g189) (i:=0) (hints:=29956) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 8 [(189,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((bitLimbs [0xffffffffffffffffff,0xfe98aa8e6e1c9000f0ff]),(bitLimbs [0x4805000a8012801480,0x5290280c440c81111111])),(0x0,0x0),((bitLimbs [0xfc003fffc0003fffc0,0x1a55b586c35200f0000]),(bitLimbs [0x90a98a530adb0a9909,0x99a51b586c3507777777])),((bitLimbs [0x3fffffffc00000,0x338905b77f00f00000]),(bitLimbs [0xe14e0c9c0c9c0cde12,0xe0318905377f07777777])),((bitLimbs [0x3fffffffffffff,0xfcc517341793df000f0f]),(bitLimbs [0x7000e000e000e003,0x411310129212222222])),(0x0,0x0),((bitLimbs [0xffffc0000000000000,0x45f4e2f96d00000ff0]),(bitLimbs [0x1802f002f002f001c,0x4c4e2a9610ccccccc])),(0x33a4dd980e26ffff000,(bitLimbs [0x20030003000300020,0xa4480800068888888])),(0x0,0x0)]
def g221C : List ColumnInfo := [(4,0,217,0,7)]
def g221A : List (List Nat) := [[],[50],[64],[64,50]]
def g221D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g221L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g221D7)
  | _ => emptyPacking
def g221I (_ _ : Nat) : Option (Nat × Nat) := none
def g221 : Forest := ⟨221,7,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 1=true := g221P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact (rfl : block g221 5 0 0 = true)
  · exact (rfl : block g221 6 0 0 = true)
  · exact g221B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 8 := lower_forest (g:=g221) (i:=0) (hints:=30468) (before_sound K189 V189) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K189 8 [(221,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V189 low221 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((bitLimbs [0xffffffffffffffffff,0xffa617c8e127cb00f0ff]),(bitLimbs [0x14000a8004a001480,0x14a4148880028a111111])),((bitLimbs [0xffffc0000ffffc0,0x7940b93e83b60f0f00]),(bitLimbs [0xa600530036c009900,0x666940992c0382333333])),(0x0,0x0),((bitLimbs [0xfffffffff000000,0x1cf88f857962f00000]),(bitLimbs [0x3380a9c02a700ade02,0xb81c708b857162777777])),(0x0,0x0),((bitLimbs [0xfffffffffffffff,0xff216395b13d3d00000f]),(bitLimbs [0x5c0ace02b380ace014,0xc0016315313d35eeeeee])),((bitLimbs [0xfff000000000000000,0x115e685ddcf0000ff0]),(bitLimbs [0x600cf0033c00cf0027,0x100a6051dc70cccccc])),(0xcea977125e06fff000,(bitLimbs [0x800f0003c000f00038,0x28964120c04888888])),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,5),(32,0,203,0,5),(1,32,202,0,4),(128,8,99,0,4)]
def g235A : List (List Nat) := [[],[112,97,83]]
def g235D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e13f
def g235L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g235D6)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,6,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 1=true := g235P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact g235B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 7 := lower_forest (g:=g235) (i:=0) (hints:=28773) (before_sound K221 V221) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K221 7 [(237,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V221 low235 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xfffffc00003ffffc00,0x4d85663fa3c58007fe0]),(bitLimbs [0x4a800da80094802,0xb4d01221203c58318c63])),((bitLimbs [0x3fffffffffffffffff,0xf9a50b1d368fbc0f801f]),(bitLimbs [0x80a1300a1300a19011,0x21a10b0c3208985294a5])),((bitLimbs [0x3fffffffffc0000000,0x233e3a455ec53f00000]),(bitLimbs [0x2c9c02c9c02cde025,0xc231c3a454ac52f7bdef])),(0x0,0x0),((bitLimbs [0x3fffffffffffffffff,0xfac58e65c5f6a400001f]),(bitLimbs [0x2b0e02b0e02b0e0146,0x2448461c5f625ad6b5a])),((bitLimbs [0xc00000000000000000,0x245795afe62520003e0]),(bitLimbs [0x33f0033f0033f00278,0x205695ade4203ce739c])),(0x73aa5b8895b2bfffc00,(bitLimbs [0x3c0003c0003c000380,0xa2410894321084210])),(0x0,0x0)]
def g238C : List ColumnInfo := [(8,0,230,0,5),(32,0,206,0,5),(64,0,174,0,5),(2,64,172,0,4),(4,32,202,0,4)]
def g238A : List (List Nat) := [[],[33,101]]
def g238D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ef52
def g238D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x222317f
def g238H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g238L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g238D5)
  | 6 => (1,0,3,0,0,0,0,g238D6)
  | _ => emptyPacking
def g238I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g238H6
  | _ => fun _ => none
def g238 : Forest := ⟨238,6,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P5_0 : block g238 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B5 : block g238 5 0 1=true := g238P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P6_0 : block g238 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B6 : block g238 6 0 1=true := g238P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g238 0 0 0 = true)
  · exact (rfl : block g238 1 0 0 = true)
  · exact (rfl : block g238 2 0 0 = true)
  · exact (rfl : block g238 3 0 0 = true)
  · exact (rfl : block g238 4 0 0 = true)
  · exact g238B5
  · exact g238B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 7 := lower_forest (g:=g238) (i:=0) (hints:=287339872) (before_sound K235 V235) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K235 7 [(252,[65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V235 low238 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((bitLimbs [0xfffca8a53f472559c0,0x80196240000fc0fc0fff]),(bitLimbs [0x5000241941210900,0x80190201041041041041])),(0x0,0x0),((bitLimbs [0x115e489f85c3c18,0xb4a3b10003f00003f000]),(bitLimbs [0x419814e489f0441c18,0xa481310b2cb2cb2cb2cb])),((bitLimbs [0x28578d761689f55,0xf246880fc0000000000]),(bitLimbs [0x8ae285789761689d55,0x724681f7df7df7df7df])),((bitLimbs [0xfffed65b82e887012e,0xc2e02c7f00003f00003f]),(bitLimbs [0x1300945b022804000e,0x2e02446186186186186])),((bitLimbs [0x2212d662f1aa667,0x64aa850000000003ffc0]),(bitLimbs [0x1c022109660e1aa267,0x40228434d34d34d34d34])),((bitLimbs [0x245928596b2f29c,0x5d014f0000003ffc0000]),(bitLimbs [0xe0024180849692f290,0x5d004938e38e38e38e38])),((bitLimbs [0x13a485814d28ab3,0x1b5610bfffffc0000000]),(bitLimbs [0x12a0040049202a0,0x180200a0820820820820])),(0x0,0x0)]
def g253C : List ColumnInfo := [(8,0,245,0,9),(0,8,117,128,8),(4,0,249,0,8),(32,0,221,0,8),(64,0,189,0,8),(1,0,252,0,7),(16,0,237,0,7),(36,0,217,0,7),(40,0,213,0,7),(128,0,117,0,7),(128,8,117,0,7),(0,4,81,160,6),(0,32,216,5,6),(0,64,172,17,6),(4,8,113,128,6),(8,4,81,160,6),(12,0,241,0,6),(68,0,185,0,6),(72,0,181,0,6),(96,0,157,0,6),(1,32,216,4,5),(1,64,172,16,5),(4,32,216,1,5),(9,0,244,0,5),(16,8,101,128,5),(16,64,172,1,5),(20,0,233,0,5),(32,4,81,128,5),(32,8,81,128,5),(33,0,220,0,5),(40,4,81,128,5),(44,0,209,0,5),(48,0,205,0,5),(64,8,53,128,5),(65,0,188,0,5),(76,0,177,0,5),(80,0,173,0,5),(128,4,81,32,5),(132,0,113,0,5),(132,8,113,0,5),(136,4,81,32,5),(5,0,216,0,4),(5,32,216,0,4),(17,0,172,0,4),(17,64,172,0,4),(41,0,212,0,4),(56,0,197,0,4),(73,0,180,0,4),(81,0,172,0,4),(84,0,169,0,4),(144,0,101,0,4),(144,8,101,0,4),(160,0,81,0,4),(160,4,81,0,4),(160,8,81,0,4),(164,0,81,0,4),(164,8,81,0,4),(168,4,81,0,4),(192,8,53,0,4)]
def g253A : List (List Nat) := [[]]
def g253D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0xc16aa4e9109e3660a921,0xe30486060144ced58364,0x719c164a62766c2b204,0xac929d04fb361d961d7,0x624c320cd3d48cb10a98,0x6190669da4658854c03,0xc83353522ec42a60186,0x419a969176215300c320,0xd5a34c4c2ea980619066,0xd1a6261754c03098336c,0x542eb32260184c19b62a,0x175591300c30534c34c3,0xa4a6b92215286d874e41,0x535c91098616ed2130b2,0xac0885485b61d3935cb3,0x443412d370a3a2e4982,0x215216d874e4d724c110])
def g253D5 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (natLimbs [0x5880800000000,0,0x1b132085a141000000,0xc820e410400000,0xe88081fc8210000184,0x382f44c8220000000000,0xc4103e0d42dfb6dd47,0x4bd173fce733cb71cc5b,0x10c2b04bfaf8bcaecb9a,0xd5ae6b3ab69ca5a90a2a,0x849fa789ca6c99a6096a,0x5493a4890a3c8da308aa,0x2487a1884a0c81a007e9,0xf478ddd75dd172dc56fd,0xb96cdad69da166d9563d,0x8960d7d5dd715ad65525,0x384c92c4992046914439,0x83dce6380da350ce320,0xb726c9523c8915c5112c,0x450fc390cc2d07000a56,0xe9173600735969b3a35d,0x5801c564cac659936007,0x1592b33a564d801c564a,0x6ce957360071592937a5,0x60c719c164c6c615901c,0x6705931b183640719c16,0x4ac5e8d852056494f331,0x856408159253873ea583,0x20d70d8ac1ca36557659,0x250e0e5d964602539429,0x4ca365587d8a50c53661,0x7394f629431698764253,0xd8a5085b6a3955cf6290,0x2a4da3e49861d530a9a6,0x8392618754c323994641,0x861d530c9664d9061875,0x4c305c98e4d7659530d4,0xcdd590205644c2c4da61,0xd5435c930a1b69875e05,0x724c314c95e4d87d8930,0x85b6a2971d7624c216fa,0x961c75d8930a53e8d871,0xd7624c306d8765875d89,0x30a936987560f624c2a6,0x9a61d580d8930ad26949,0x3603624c2b89a424d80d,0x8930a0f69875e11714c3,0x619955908358130c9665,0x98694e504c3a19865925,0x3941309d26a653d8a504,0xc33499894f6294130956,0xe9d96e15300c315b8765,0xb854c030d166a576e153,0xc3c1aa45db854c030f,0x669176e15300c345996,0x5db854c030d1669d9621,0x5300c361aa4658854c03,0xd8669196215300c3459,0xa95d8854c030f06a9176,0x215300c3c19a45d8854c,0x30d1665976215300c25,0x59a6a61754c030956698,0x985d5300c391b87e1664,0x4c030f065db85991300c,0x2e19a6216644c030f065,0xd885991300c2d1aa85d6,0x644c030b462a17599130,0xc391b87e15644c030f0,0x65db85591300c2e19a62,0x15644c030f065d885591,0x300c2d1aa85d5644c030,0xb462a175591300c394b8,0x7e15214c030f125db854,0x85300c2d4aa85d5214c0,0x308d96a785d8930c42ab,0x1a61d38054d10a6c29d6,0x4e01534431a6981d2535,0xc910b296987494d72442,0xca5a61d1535c910d681d,0x39054d72442bc3a36558,0xd8910af028d95603624,0x42b63a564d80d8910a78,0xa9c9360362442b61a524,0xd80d8910ae8690936036,0x24433c19324d80d8910b,0x2969874dcd32442aa5a6,0x1d3804c910b8c6909859,0x560442e93a3615645811,0xba428d8559160443633,0x955918358110d8c65564,0x20d60442ca5a61d17254,0x110b29698745cb304435,0x8474e4d72cc110c8d65b,0x851d13044313497e1564,0x4c110b29698745c93044,0x3927851d1724c110d611,0xd3935c930442365a9e17,0x624c110cd8e1590d8930,0x442cb0a7591604c110e8,0xce15645813044336385e,0x41214c110916698985d5,0x300c28a5a61d3835c910]) else (natLimbs [416,0x20aae0840000000000d0,0x1000000000000001d020,0xe8c304001a1410000000,0]))
def g253H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [75,0xd2000000000,0,0x3a000140018,0x30f00000000000000000,0x79c00000000000000,609,0x8000000038c000000000,0,0xa10000065c4a380000,0xb57340000f3000000080])
def g253D6 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (natLimbs [0x6644c030,0xecdc3ac898061f1b8559,0x1300c3e310ab22601876,0x65d5644c030aedcbb029,0x80619db87605300c39b2,0xecc0a60187565d5814c0,0x30e6cbb2c298061d5975,0x585300c3b970e90a6018,0x7d2e15214c030cb7c2ee,0x2982413e79060f62c427,0xcb3129ec5884f9e4d80d,0x8b109f2cc6c5986217c5,0x93d8b30c426eb2dc2a61,0x886cde15644c3109f2cc,0x6c498621b6785d8930c4,0x2f8b27b1261885f86436,0x24c310f58b22c098621e,0xd16358130c42d6b2c3a4,0xa68856d25d6494d10b5a,0xcb0e8a9a215b49759153,0x443766e9c02a6886ec1d,0x38054d10dd932700a9a2,0x1bb164e01534427cd312,0x9ae4887691d2535c910e,0xd23a2a6b92217e39054d,0x724427cf20c1ec4884f9,0x66253d8910bf1c82a7b1,0x221be395603624437c32,0xac06c4886f8e4d80d891,0xdf149b01b1221be1936,0x3624437c126c06c4886,0xf894d80d8910df0a9b01,0xb12213e79360362443b4,0x8e9b9a64886e9dd3804c,0x910dd23a700992217d39,0x361560442fa126c2ac08,0x879c2616558110f59c2a,0xc8b0221eb18559160443,0xce2cbc1ac0887ac59383,0x58110f58b2506b022177,0x39560d60443ce2cac1ac,0x887ac5918358110af94,0xb906b02217719520d604,0x42f632841ac0887ac590,0x8358110de8c1906b0221,0xed38358d60443da106b1,0xac0885bc65a5358110f5,0x8b24a6b0221eb16454d6,0x442d6b2c3a2a08856d2,0x5d6454110ed23a2e4a82,0x217e190d8950443d62c8,0xb02a0887e850d3250110,0xbf1c8264a02216b5961d,0x330442b692eb26608876,0x91d172cc110be3c9ae59,0x82213e598d8b30442f8b,0x27b1660885f864362cc1,0x10d78c32c198221eb164,0x58330443da2c6b066088,0x4dd65b854c110d9bc2ee,0x8982216b5961d1304436,0x6f0a3a260886cde16644,0xc110ada4bac898221b37,0x85591304436cf0ab9260,0x887691d1724c110be3c9,0xae4982213e598d893044,0x36cf0bb1260885f164f6,0x24c110bf0c86c498221b,0x738558130443d62c8b02,0x60887b458d604c110db9,0xc2a8098221ba774e0d20,0x44335ee9c0264884f964,0x383485109f2c9f0090a2,0x17e3904873044327f0bb,0xa260886d9e15214c110b,0xf1c8242982219af74e0d,0x204422bf30b98e6b2e56,0x5cd801cd658bdcc2e038,0x2cb959835c0705975632,0xcc00e2b266c5d5801c56,0x4cd8b9b0038ac95b1901,0xc670592cb32041acab1d,0x9664c8059560b58c8102,0xb22c145c97595634c22d,0xd303aae49851b658755c,0x9308b6cc6ebb1261c5a9,0x55d9300c38b32abb2601,0x8726a51764c030e4cca2,0xec9806195b87e15300c3,0x8b2edc2a601859665885,0x4c030e2cbb10a9806155,0xa985d5300c2ab130baa6,0x18556e59754c030aacc,0xbcca98061c5976995300,0xc2ab32eb2a60187165d9,0x654c030e4cbb4c898061,0xd1975991300c3932ecb2,0x260187465d5644c030e6,0x4bb24298061d49754853,0xc296b2c3a6e6886691,0xd3835c910b52cb0e8992,0x214b49759160442d4b2c,0x3a24088529658745c910]) else (natLimbs [0x72870f5d,0x96494e50caec32e729ca,0x1d1e645ce53943a3ac8b,0x9ca72865e5d98094e50d,0x9d3230129ca1b3964602,0x539432db2ac3ec52847b,0xe4d87d8a508f6cc2e7b1,0x4a19cd835cf629426db3,0x129ec52865b61e53d8a5,0xea6b9ca7b14a1769909,0x4f62943a9ae729a43285,0xda6425348650bd8c8102,0xb22a19cf73e053254387,0xb28bb2cb2045f65b855c,0xe40c9fc2ac8b9c819ad9,0x461f629023df26c3ec52,0x47b66173d8a40ab7caa,0xe7b14819cd835cf62902,0xf632040ac9984f3e4d80,0xd8b309e6c9f0090e611e,0xd985cf628c339b06b9ec,0x51867a5cd80d8a30e5cb,0x22e6b0461cd97358d608,0xc32b90bc1aec9855be45,0x82dd530a9fca303baa61,0x17d96a1c754c347d28c3,0xea9868f651861d530d2,0xec9b0c3aa61a6f926187,0x54c34f320c30ea9845fe,0x61761d530aafc9aec3aa,0x6187c985d9654c38bf26,0xbb2ca9845f65b855d130,0x8bf4c4caba26117e981d,0x5744c28fb2c3aae89854,0xfa5c7599130b1ecb0eb3,0x226153e971d5644c2c7b,0x2c3aac89874ddd781591,0x30e9bba902b22617b190,0x205644c32eeebc0ac898,0x5976587558d30b2ecb0e,0xaa1a6155c97595434c3a,0x98eaa1ae49865bdd7815,0xc930cb63af02b926196f,0x9561f624c32d92ac3ec4,0x9847be4d87d8930ce7c9,0xb0fb126196d98dd7624c,0x23db31baec4984db6637,0x5d8930cb6c3eebb12613,0x6d981d7624c2add2e3ae,0xc49865b61c75d8930b36,0xcb0ebb12611ed98dd362,0x4c2adf2aba6c4986d3dd,0x583d8930da63ab07b126,0x196f7560f624c279b312,0x9ec4984f366243d8930c,0xb7bab03b1261b6b75603,0x624c36d0eac06c4986f2,0xe4d80d8930de449b01b1,0x261bca53603624c3792a,0x6c06c4986f290d80d893,0xde4a1b01b126196f756,0x3624c279f26c06c4986,0x5bdd7814c9308bf4c0ea,0xb8a6147d961d5714c327,0xeebc22e29864f1d7845c,0x530cd7c22e4b8a61c3f7,0x5591614c32dd31baa429,0x865be1f7548530ab74b8,0xea90a6166d961d5214c3,0x2deebc1a429865bdd780,0x485309e6c9f0090a6167,0x9961d5604c3c76eab22c,0x9878e1d56458130f59c,0x8ac8b0261eb091591604,0xc3cb2cbc1ac0987a6593,0x8358130bacca906b0261,0x7999420d604c3d32c841,0xac098796dd56358130f2,0xc3aac6b02616d99694d6,0x4c3d32c929ac0987a65,0x915358130b6ccb486b02,0x61e596550d604c387eea,0xb22c0986ae6196494130,0xd6cc32c7282617599694,0xe504c36b30d29ca0987c,0x69925394130f8cb24a72,0x82613e998d8a504c2f93,0x27b14a0987d294f62941,0x30fa529a4328261f1a64,0x54d504c3e32c8a9aa098,0x5f264f6254130fa4a9ec,0x4a8261f4953485504c29,0xdb23c12ec1863b5d981d,0x8830cb6bab03b10619ad,0x74607620c2bb32dc3a60,0x18576e5d864c030cedc3,0xb0c98061cd9915d9300c,0x39b30cbb260185d665b8,0x54c030eacbb70a980617,0x5996215300c3ab2ec42a,0x6018756619754c030ecd,0xc3cc898061f1b8599130,0xc3e310b32260187665d])) else (if j<3 then (natLimbs [0xac3a0949,0x42b0cc310fc00cc2c0d,0xc70cc20cc2a0815f0020,0x57c0b1030ac3108150c4,0x2313c0234323431082bf,0x2272840542bf02ca10,0x2bf02c40cc4f002cb283,0xf002b0cc3f00330ac7b2,0x82f00140cc3b282a0831,0xb1c330c31b1eca0f410a,0x4390c1f929c30e0f0e02,0xf024a0a430b42983c381,0x1fe17c40d44bad5d52e,0x8973eb925c02da56ccb6,0x35b02d616aab4d598ac9,0x1638b1958b2c4d620b0d,0x5852c1d608b0157f2bed,0x5f0af55792bbd5d8ae95,0x70ab65598ac455e2abd5,0x58aa454e2a3d50ea7f53,0xe29d14e2a6e535a9a14c,0xaa6252fa9714a8a4c524,0xa919486a4051ea8e946e,0xa34513a89142ea145062,0x7fd3f89f94fb27cd3b89,0xd94eb274d3a09cd4e2a6,0xcd3609ad4d5269d33498,0xd4c025e12d69684b2a56,0x12aa9524a7a531292946,0x49ca4d9252926491a41d,0x2088f7477a39d1be8dc4,0x6ca3591a68d0466a3291,0x8e8c445e22e516c8b345,0x5a2a114a8a244fa27113,0x2896449a24111a88a441,0x21fd0f887943b21cd0e0,0x86d435214d0a084d4252,0x10907e83741a208903e8,0x1c40a201cffe7f73f79f,0x88fbe7dc3e79f08f747a,0xd3d01e60f2a7923c79e3,0xf087813bc9dd8ee6770,0x3b69da8ece7643b09d64,0xea274e3a31ce4e6c7333,0x981cb4e4a71d3881c0cd,0xd86e93709b64da26ba35,0xb9ad0d626ae3559aa0d4,0xa6a234d1a34cec65f32b,0x9928c8e64432098f8c76,0x63831a98c8c5e62c3149,0x898c4662030c182cbde5,0xdd2ea9734b945c72e217,0x4b7c5b12d49698b465a,0x2ce9654b1a58a2c395f,0xcad05602ac1540a90545,0x29e94d4a5051128493f0,0x9de4e226a933496c4a42,0x4b923c90446622c91448,0x8844121790b084841c20,0xa104481c40b2040fc47c,0x83d71ea0f4479c3c61e1,0x8ed875c3ab1d40e30712,0x3861b78db06d23521a78,0xd3069234619f0cd86483,0x121878c3061230117a0b,0xb05d22e116c8b5857e2a,0xd14b0a104e425b12208c,0x844021310087bc3c41d5,0xe686ec35219c0c78608,0x2e01630ab051026e1200,0x8483c81c00ce06082d01,0x4409504181c40be04d02,0xb802e000557e51731,0xcd65cafba106b82cb5b7,0x935d471592b6f2ab98e2,0xb26ec655801c564dd949,0xb0038ac9bb1936007159,0x267f2ac1ce0b266d6147,0x19c164cdac18e3382c9a,0x5d65e0d7058ee3f26c2a,0xc929ecd6148159253bd8,0xc8102b24a77b19020564,0x54eeb32041acaa1d7364,0xe805cf62ab7cab00b9ec,0x55cf9360173d8b2db0ea,0xa4a7b1573e4d855c362a,0xe649b0ab86c59cf83a0d,0x70d8abd32141ae1b155b,0xe55835c362ab6ca906b8,0x6c55ad9420d70d8b39b0,0x641ae1b147ba62535c36,0x28f6cc4a6b86c55e9909,0x4d70d8a3dd3121ae1b14,0x7b662435c362af4c8486,0xb86c59e79160f70486c7,0xb2843acab059ea5c8059,0x560b4fc9aeab22c169c9,0x35d56458393ac9b9ce6b,0x6ae591809cd60d1fc2a,0xc8b9ac1a3d8559073582,0x3bf30b98e6b06ae59180,0x94d60aae49b0abb4a1c3,0xd955d9649430fb0cbb4a]) else (natLimbs [0xd0101280a827,0x42a4a03711c14a02a10,0x9041003404348338,0x4e078014348302064100,0,0x8f05c307c00e8230,0x41c281c2bc00809041a2,0x81a2bc0082c06410400e,0x810000000000000841e1,0x10000000000000d0140,0x8070839080b081708350,0x800000034e0780050400,0x2810406604050c0,0x3af0020ebc0083a,0xac270410e986080024a,0xf00200000000052bc008,0x52bc00800034e1381e0,0x14140c154a0b0507050,0x68504000000000000008,0x41000034104000000000,0x2141000000000,0xc743d07401000009,0x28100210400c423d0430,0xe10152b060a4a064a0,0x7810414e0420000574a0,0x82c050281418164a0a4a,0x81821341000000928100,0x4d040000000000020506,0x5040410141504080000,0x2c042c06c10b020cc2,0xa09c4705c00b04001507,0x506c404c4705c00b040,9463419924,0x815052c30c440508db0,0xc3110ca042ab28200000,53313,0xd0446082982f44d07401,0x744d07400f0507050400,0xb12410a85040000,0x1c405c404001c404857,0x11c31244710171011041,0x9041024104150415b102,0x311c3705c011c405c170,0x2b06c00ac1b002b06c0,0x81504c4b06c00b04b12,0xc1b0030b02a0815042c0,0x502b12c1b00350a850b1,0xc409c10449704202c4b0,0x6c00c0d101d101d10100,0x82f41d00291341d0,0x207e410800001041034,0x1d002d04100021f44d07,0x400a45000c1744d07401,0x210c1744904400000,0xd1010541d1341d00311,0xb4101430000383078310,0x42104103830744040067,0xc00578a13c0e282c0c19,0xf0015e284f038a0b03f0,0x2a0d83f01c4e282a103,0x4f038a0a84f038a0a43f,0x3a0b03c2bc00bc0050,0x360e4af002b0c2b52820])))
def g253H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x3663a02ac003518,0x6055400797ed2000003d,0x9870000a40a5f00247b1,0xe150300006158f001c21,0xafce520caf0b40005b40,0x22080dc4653565616a5,0x9c82ab3db4c49726ee4f,0xebdd029a83b000d9ec5c,0xb1392000006d3006e646,0xbc8ee8d499062c489824,0xcd492d27ab8223932924,0xafc00054405f939988a5,0xb151400285a49e7a5a70,0x4b5e00167527a50f2c00,0x6442e80079ae86000,0x1bf7c0dc55587d20d,0x480a12e93a8d9c4a0167,0x200310ee1138c7d70764,0x840a5000028528081000,0x2a8781868460706c0031])
def g253D7 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (natLimbs [335855888,0xdbf7494d10dbf7454d10,0xdef734c910bef804c910,0xfe65348510fe55348510,0xdbf7454110fe52154110,0xdbf74cc110fe521cc110,0xb7f854c110dbf744c110,0xfe5214c110bef8348110,0xd5f739cd65b3d841cd65,0xd5d731cd65b7a801cd65,0xb79801cd65d7b709c165,0xb5f835c165b5c835c165,0xb3d841c165b5e831c165,0xb5d831c165d79701c165,0xbb580dc564db5751c564,0xdb5731c564bb5801c564,0xdb4719c1649f580dc564,0x97f855c263e5f8359563,0xe5c8359563c7d65dc163,0xc7d7659653b5f8359653,0xc7f7659553c7d7659643,0xcbd76592439f7805c643,0xcbf76591439ef805cf62,0x9ed8794f629ed8790f62,0x9ef835c3629ed80dcd21,0x9ed83dc12197f855ce60,0xe7b8059560e788059560,0xeb78159160eb48159160,0xc7d65dcd60c7d7659650,0xb7b8059650cbd7659250,0xd5d7394e50b798094e50,0x9ed87d8a509ef874ca50,0xde5325c6509df835d950,0xc7f7659550dcf734c950,0xc7d7659640cbd7659240,0x97f855ce409ed87d8a40,0x9ef874ca40de5325c640,0xcbf7659140c7d7659730,0xe5d6558f309ed87d8b30,0xbcd83d8b30c7d7659630,0xcbd76592309ed87d8a30,0xbe980d8a30beb804ca30,0xde5325c630e796558230,0xeb9645823097f855d930,0x97d86dd530d6d82dd530,0x97e871d530a7d861d530,0x97e879953097e8759530,0x97c8759530c7d7659530,0x97f855d130d3f7599130,0xd3f7559130e5d6558d30,0xd6f755c930d6c755c930,0x9ed87d8930d6f75d8930,0xbcd83d8930be980d8930,0xd6f754c930beb804c930,0xd6f7548530e796558130,0xeb96458130ed96358130,0xf5a5394130f595354130,0xc7e855d830c7d855d830,0xcbe845d830cbd845d830,0xcef825d83097f865d430,0x97d8799430c7d7699430,0x97f875943097d8759430,0xc7d76594309bf865d030,0xd3e655d030d3d655d030,0x9bd8799030cbd7699030,0xd3d75990309bd8759030,0xcbd7659030d3d7559030,0x9ed87d8830ced76d8830,0xd6d75d8830dad74d8830,0xced7648430d6d7548430,0xdad7448430ddb874c030,0xdd9764c030f5b854c030,0xf58854c030dd9754c030,0xf5a654c030f59654c030,0xf9a644c030f99644c030,0xfc9214c0309ee8794d20,0x9ee8790d20be58190d20,0x9ee87cc520bad84cc520,0xdcf73cc120b6f854c120,0xdcf734c120e756558f10,0xbe583d8b10be580d8b10,0xbe7804cb10e756558310,0xeb56458310b77854c310,0xbe783483109ef874ca10,0xde5325c610db474dcd10,0xe756558d10bf38054d10,0x9f68790d10be7835c910,0xbe583d8910be580d8910,0xfa7744c910fa4744c910,0xbe7804c910ef16558110,0xef16358110e756558110,0xeb56458110fe13290110,0xfb15450110fb14350110,0xfe13250110b77854c110,0xfa77448110fa47448110,0xbe78348110fe14048110,0xdaf744c910be78348510,0xbe78048510daf7448110,0xbb1801c564cd9764c030,0xd59754c030ab5861d110,0x9b48759110da4745c910,0xbe180d8910e716558110,0xeb16458110be38048510]) else (if j<2 then (natLimbs [356659415,0xf855d930d7c855d9309f,0xf835d930ddf835d930d7,0xd86dd530d7d84dd530d7,0xd81dd5309fd86dd530b7,0xd86dd530d7d76dd530b7,0xd861d530d7d761d5309f,0xd86dd1309ff865d130d7,0xe655d130d7d655d130d7,0xf755d130d7c755d130db,0xf7599130f3f7599130db,0xd7599130f3c7599130db,0xf7559130f3f7559130db,0xd7559130f3c7559130fb,0x78159130fb48159130d7,0xf7559130bf78159130f5,0xf7558d30f5c7558d30d7,0xf7558d30bdd8694d30f9,0xe6494d30f9d6494d30f9,0xe6454d30f9d6454d30bd,0xd8690d30bdf8650d30f5,0xf7550d30f5c7550d30f5,0xe6550d30f5d6550d30d7,0xf7550d30ded745c930fc,0xd435c930bef815c930be,0xd87d8930def75d8930f6,0xf75d8930ded75d8930f6,0xc75d8930def74d8930de,0xd74d8930bed83d8930fc,0xe53d8930fcd53d8930fc,0xe43d8930fcd43d8930be,0xd81d8930bed80d8930de,0xd744c930fcd434c930be,0xf814c930d7f755c530d7,0xc755c530bbf845c530de,0xd725c530d7f7558530eb,0xd6458530d7f754c530be,0xf8748530def7548530f6,0xf7548530ded7548530f6,0xc7548530bef8348530fc,0xe5348530fcd5348530be,0xf8048530f7b7558130f7,0x87558130ef96458130fd,0xb8358130fd88358130ef,0x96358130fda5358130fd,0x95358130fda4358130fd,0x94358130d7f7558130eb,0xd6458130bdf8358130ed,0xd6358130bf98694130fb,0xa6494130fb96494130fd,0x96394130feb6294130fe,0x92194130fba6454130fb,0x96454130fd96354130fd,0x94354130feb6254130fe,0x92154130d7f7550130cf,0xd815d830d7e655d030d7,0xd655d030dbd7599030db,0xd7559030ded75d8830de,0xd74d8830bed81d8830cf,0xd7658430d7d7558430db,0xd7458430fd9864c030fd,0x9814c030fd9614c030de,0xf7350d20dee53dc520de,0xd53dc520def734c520be,0xf804c520def71cc120de,0xf714c120bf78058f10bf,0x58694f10fb56494f10fb,0x56454f10fe653d8b10fe,0x553d8b10bf78358310ef,0x56358310fb56454310fe,0x76254310bf586cc310fb,0x564cc310fd563cc310fe,0x762cc310bf5864c310fb,0x5644c310fd5634c310fe,0x7624c310ff1604c310bf,0x78058d10bf58694d10fb,0x77494d10fb47494d10fb,0x66494d10fb56494d10fb,0x77454d10fb47454d10fb,0x66454d10fb56454d10fe,0x6535c910fe5535c910fe,0x653d8910fe553d8910fe,0x7734c910fe5434c910ff,0x38558110ff18558110ff,0x38358110ff28358110ff,0x18358110ff08358110ff,0x25358110ff15358110bf,0x78358110ef56358110fb,0x77454110fb47454110fb,0x66454110fb56454110fe,0x57254110fe76254110ff,0x16054110ff25350110ff,0x15350110fe53250110ff,0x15050110bf586cc110fb,0x774cc110fb474cc110fb,0x664cc110fb564cc110fd,0x563cc110fe572cc110fe,0x762cc110ff160cc110ff,0x140cc110bf5864c110fb,0x7744c110fb4744c110fb,0x6644c110fb5644c110fd,0x5634c110fe5724c110fe,0x7624c110ff1604c110ff]) else (natLimbs [0x9143dbf7,0x655143e7d6558d43d7e6,0x5dc143d7d65dc143ded8,0x55cf62ded845cf62ded5,0x45cf62dee805cf62ded8,0x5cf62bed8494f62f6d5,0x494f62bed8094f62bef8,0x454f62ded7354f62bef8,0x54f62bed8590f62bed8,0x90f62bef8550f62bed8,0x550f62fad5450f62ded7,0x350f62bef8050f62dee5,0x35c762ded535c762def8,0x55c362ded855c362def8,0x45c362ded845c362ded5,0x45c362def835c362dee8,0x35c362ded835c362dec8,0x35c362dee535c362ded5,0x35c362dee435c362ded4,0x35c362ded81dc132ebd6,0x494d61ebd6454d61bef8,0x4c931bed8094d21bdf8,0x35d560bdc835d560e7c8,0x759560e7f84595609fd8,0x3dd160e7d65dd160e7d6,0x55d160ebf7559160ebd7,0x559160e7d65dcd60ebd6,0x4dcd60ebd649cd60ddf7,0x39cd60bf9809cd60b7f8,0x55cd60e7d655cd60ebd6,0x45cd60b7d851cd60bbd8,0x41cd60ebd641cd60ddd7,0x31cd60edf7358d60edc7,0x358d609fe8794d609fd8,0x794d60afd8694d60ebd6,0x494d60bf98094d60ebd6,0x454d609fe8790d609fd8,0x790d60afd8690d60bf98,0x90d60e7d6550d60d7d8,0x55da509ff835da50d7d6,0x55d250dbe645ce50dbd6,0x45ce509fd8758e50cfd7,0x658e50ddd7358e50b7d8,0x694e50d7d7694e50d7d7,0x494e50f3e6494e50f3d6,0x494e50ded74d8a50bed8,0x3d8a50ded73d8a50f6e5,0x3d8a50bed81d8a50ded7,0x44ca50bef814ca50ded7,0x348650f6e53486509fd8,0x6dd150d7d65dd150fb78,0x159150fb48159150bf78,0x159150d7f7655150dbe6,0x4dcd50dbd64dcd50f3e6,0x454d50f3d6454d50def7,0x4d8950f6d54d8950bed8,0x3d8950def73d8950f6d5,0x3d8950bed81d8950bed8,0xd8950bef814c950ebd6,0x458550ddf734c550def7,0x348550f6d5348550ebd6,0x458150dbd845da409ff8,0x35da40dbd7559240dbd6,0x45ce409fd8758e40cfd7,0x658e40ddd7358e40ded7,0x5d8a40bed83d8a40ded7,0x3d8a409fd83dd9409ff8,0x35d9409fd86dd5409ff8,0x65d540dbf7559140dbf7,0x6551409fd86dcd40d7e6,0x5dcd40d7d65dcd40dbd6,0x4dcd40e7d6558d40bbf8,0x650d40dbf7650d40f3e6,0x550d40f3d6550d40def7,0x5d8940ded75d8940fad5,0x4d8940bed83d8940def7,0x3d8940fad43d8940bed8,0xd8940def734c940fad4,0x34c940bef804c940e7d6,0x558140d7e655d330d7d6,0x55d330dbd7599330dbd7,0x559330fb78159330fb48,0x159330bf78159330f9e6,0x454f30f9d6454f30f5e6,0x550f30f5d6550f30ded7,0x5d8b30ded74d8b30fcd5,0x3d8b30fcd43d8b30bed8,0x1d8b30bed80d8b30ebd6,0x458730bef8048730cfd7,0x658330ebd6458330bdf8,0x358330edd6358330d7e6,0x55d230d7d655d230dbd7,0x599230dbd7559230dbe6,0x45ce30dbd645ce309fd8,0x758e30cfd7658e30ddd7,0x358e30ded75d8a30ded7,0x4d8a30bed83d8a30ded7,0x3d8a30bed81d8a30ded7,0x44ca30bef814ca30ded7,0x548630bef8348630ded7,0x348630df97358230ef96,0x358230fba6454230fb96,0x454230feb6254230fe92]))) else (if j<5 then (if j<4 then (natLimbs [0x4a6840d0,0x219f3b3e167b6cf559e3,0x339c66f6cd699a5b32a6,0x636cbc596832af650ac9,0x91926321963bac7398db,0x31a76342c6258b431626,0x294c4c9888b10b61e6c3,0x2584b306c6084c0a9809,0x2ff15fc4bf297d92fa35,0xf28bdf17b6af555e8cbc,0xdd7942f195e02bba5764,0x2eb95d54ba497462e7d5,0xcb8b93571aae265c2eb8,0x457012de15b80b6a16c8,0x2d5d5a66b425678acc75,0x95eb1f16322c4c5868b0,0x7160b2bf557a8aef15d2,0x2b8356d6ad4d5992b1a5,0x5f2ab61564aab15532aa,0x55302a36544ea8194fb,0xa9df538ea6e14d4a9915,0x304a5cd4ada9435268a4,0x7148b28f551dea3a5471,0xa8dd51aea34544f287d5,0xb8a0ed408a7e74f9e9f,0x253d427994f149dc93ad,0x27424e429bdd36b26d04,0xd709aa534426674cc299,0x6d31d26224c1497ed2e8,0xa5a74b1e95dd2afa53e4,0xa2893cd260249f48fc91,0xbd230245148849085200,0x23e847a08ee11d9239a4,0x6ce8cf518e22f2455a89,0xe912ca22f440a87d90f3,0xa1d8439286c50d1218a4,0x29c84b508aa0f441a682,0xed048a07940c2812501d,0x202b40027f5cfd69f833,0xea07c98f7e1ee43d747a,0x64f379e333c247830efa,0x1dd33b647644ec11d6a3,0xa92747ce7a9ccb393071,0xdce269c2c38046f3cdd7,0x1b8436b46cc0d879adc3,0x5766a44d339a34340267,0x5ccd6998c32c464bcc79,0x98d23162621cc2e983c3,0x245fa0bdf179d2ee65d,0x48b9897072dba5af0b49,0x16682c8e5898b0295db2,0xb6255f8aae953c2a2453,0xa0a6394a628f85190a21,0x942227f04f809db13952,0x6e84d4c99012ff25bc4a,0xf49499272249048788fe,0x91ca232e45d88aa91342,0x226438085f909520d640,0xe08070fed1f983e647bc,0xf601e7e3cc07878eee1,0xdac3ad474e8e731c9237,0xec6f18db01b1e35b86a6,0x8d351a3a33a865b8c8d1,0x8b4309c6030bdc17642e,0x205af0b3d16142b8055b,0xa9514d6294c5190a111,0x3f2273c4d2897b126c24,0x7848308ee119a22b0445,0x887310a420c440807e60,0xf8a1e6c3bd07620e821c,0x5c37b06d50d681a28330,0x63f0c3c17d02e505a90,0xb10159c2a3051c0a0813,0x8c261049808ee1110208,0x83f0078c0e941c203630,0x6840c8417b82cd05460a,0x812c022e03f607440d3,0x816b025e041406d80a80,0x12001980150000b7d83d,0xd165b7d80dd165b7d849,0xcd65d7f749cd65b7f845,0xcd65b7d841cd65b7d849,0xc165b7f845c165d7f745,0xc165b7d841c1659fd83d,0xd165bbf835d564bbd859,0xcd64bbf855cd64bbd859,0xc164bbd839c164bbf855,0xc164bbf835c164e7f845,0x9563e7d655d163bdd839,0xc163b7f855c163e7d655,0xc163bdf835c163b7f845,0x9653d7d655d253f3d855,0x9253fb78159253fb4815,0x9253bf78159253d7d765,0x5253f3d6455253dbe645,0xc253dbd645c2539fd86d,0xd153d7d65dd153fb7815,0x9153fb48159153bf7815,0x9153dbe64dc153dbd64d,0xc153dbd75592439fd80d,0xd9439fd86dd5439ff865,0xd543f5f8359543f5c835,0x9543bdf8359543dbf755]) else (natLimbs [0xf0294183,0x780ca0c3215650619e00,0x5436570f85c0158bc015,0xd2830cf002b4a1009c0a,0x50ac41981095c0160a19,0xa3f0028251f814a0e87c,0xa50633c7f00942c1424,0x2ba5074a158418059243,0xa4830f0c124387a14921,0x8ae9410b8942c0e8f4a0,0xb1fc0250b041a853804a,0x100c150a63c3205e0128,0x8e00ac2028138030160a,0x31828cc3e0054661b1e0,0xa330c662a0a0a32081b0,0x6e04159428550dc042d2,0x85a27010a33110d4442f,0x2942f001a8642d285e0,0x5466183381056508c4e,0x41594241b80ca0a8814,0xe021694251d0a330d0d4,0x3e0216942f010a16a508,0x8be005066221a942a0c1,0x685248604428c8243216,0x921a190b490c5433090d,0x4742d284430590b4a106,0x14e00b040a71387c2e0,0xb0663f005610ac62123,0x462170194300f80ca160,0x6c7654143650a82e1b28,0x62182c2a8a0e8e144506,0x142303f1425081e8a0c8,0xd4207e2842305d1418af,0x141601142c0f8182250b,0x412e08921a144a490f0,0x42c250628e01285820a3,0x804a0a09c0c38ac3c141,0x4941e08008525090507c,0x1d94250450290c943916,0x7c00a9903230e454184,0x3044a0d89821a85c4428,0xd43c107a941e081ec3a5,0x9821612830a12988281,0x60a050a8509428149439,0x1607c4250a02824143cc,0xa0d882c1c8615260e431,0x6079941e0b802b0e0b82,0x2452841683e942913044,0x250b440a5285a186c1f,0x82a5081005c1c94202d0,0xa2383928524417054a13,0x802ae20d8419853882ce,0x3f00611053942ce3f006,0xc16178839138185e20d8,0x40fe1788c3a50bc41a84,0xc4250b07220d895c40a0,0xd450341c164a11892302,0x45d48b4915d22a245148,0x9c912d2242445487b90b,0x521524274848904f2086,0x404c7f18f7d1e9a3c2c7,0x528e751cd239747168de,0xb1b0a350c6928ce31966,0x320c6178c11180a2f545,0xdb8bab173e2e4c58d8ac,0x7149e28c450089d11366,0x260c4b28959129a24744,0x6488bd10f6212c41f882,0x110061fdc3ec87cd0f82,0x1dfc3b987670e921cac3,0x8f86dd0d7e1a84338865,0x30c4618142f385db0b56,0x151428a84f7096a125c2,0x33840107c60f141ca835,0x305fe0a6413482390412,0x71c0c28143020203440,0x50808300a60043fd57f5,0x6fe29fb03f247e18fbd1,0xf6e3ebb7d34f9e5f27be,0x377c50f7f9eea3db37b1,0x2f5c5eacbd2f7a52f445,0xe7cbcd8796ef27de4cbc,0x93791af21de40bc7b78a,0x2f109e1e3c1b782aefd1,0xdee3bd67758ee99dd03b,0x8876f2ed85da93b43766,0x8ec95d8fbb107614ebed,0xd763ae675aeeafdd583a,0x987512e9c5d313a41742,0xee821cef39b47326e5ed,0xcbab9547278e425c78b8,0xc77116e215c32384c708,0xce101c1d38227014dfc9,0xbed37c26f78ded9bcf37,0x8f6f12ddc5bb1375c6e9,0xadd1db97b7296e46dc75,0xb8bb6ff6daadaf5b5bb6,0xb16d56da95b4fb6996d1,0x4da11b3636546c54d849,0xafd35d96b94d6c9ad635,0xa66b40d669ab835466a3,0x8d411a7634e669c0d2fd,0xa53b48f6912d1c5a35b4])) else (if j<6 then (natLimbs [0xa9484e0,0x6052b80120500152909,0xc00c0a570020a6130380,0x106984c0e00282d0e854,0x1a00814c260700252856,0x1416941066814a0c2a0c,0x16081416081414182822,0xc0a0414060b430a0a0c1,0x418283430458c4085c85,0x816c220061804020a12,0x8210141041e820086840,0x7081809080a101010a0e,0x101c0b0f080142861942,0x58417040b8361104401,0x42343a0d00418d0e8340,0x1029c0085944a182c4a0,0x528285e13002a250b41a,0x4230c0410008484a08,0x400c447410c318420868,0x5420485420485c21043a,0x50ac2a54182166042818,0x180a10b294050f804a03,0x6150448150858140840,0x14082b40a50784254178,0x20b01e01280a1864182,0xc10282c1020c8304060b,0x40a0c0c181110642100,0x502820306820400a9803,0x30c0000000001384c183,0x8162d0094160c5540a50,0x616a0528362305802c10,0x2a14618c44153282001c,0xb6206c4041609081e10,0x3a0015110010b082400c,0x2a44209004a250680180,0xc42084c4045841200628,0x25118300016104801d06,0x80150458110412210480,0x2c120b44a0d004a08b02,0xa21042a08b0216104801,0x8548841200944a0d0031,0x482e8941a00b44a0d003,0xa2506801c14182830506,0xa088d88410c46856206,0xc4208485620446058403,0x102a10882ac460b00524,0x81582c01058c160062c6,0x23058020b00ac461b058,0x491c2a4962305802b10,0xc8150c58492090042370,0x940512880d101a20344,0x447440a880854441054,0x98c421b058033103a4c0,0xd8305088814218641200,0xb03a0d00205d06802912,0x83400a83400a822c0882,0x9041165068049128340,0xa10c422104802c120b4,0x4a0d00443d128340148b,0x5a25068024168941a00,0x94116041082d10822416,0x88410e8941a00b042351,0x283400a10c6a25068018,0x46058583c102c3c1904,0x461e0c62230e880e0c46,0x141683400c2105c19044,0xc1e0b03c0120b44a0d00,0x4084168983208b83c102,0xc3e00642b8a13818a160,0x7c0c51182a211b0845e0,0x6285e00e85818678015c,0x50819e00571427031446,0xa89c0c50b03236108bc,0xc50bc0c50b03e06288a,0x19138016c50504e03131,0x5070a0a34e062a841417,0x89c0150d84e062985451,0x17c0c507060af031420,0xcd9fc0850b051d307802,0x8198b06e00cc581f0094,0x150c33c00ad284027009,0x415130e3316064ae041c,0x282058290614084ae041,0xc28202c31090c1744448,0x604a38606a182f89090f,0x8618084284e1f10210a1,0x20bc0c506c1e00e85820,0xa3810a16090a0a0a03e0,0x506c1a2b802c0c95c04,0x286440cf002b4a13088b,0xe0128282f010a190c8dc,0xa878405a1492206416,0x8525090507b2830af029,0x4192b80190a88a2a5044,0xa1c8b0342928721f020a,0x19c388851a8400c3a149,0x424141eca0e0e4a1c864,0xae00b03c7e078033160a,0xb4312438786092192b8,0x2c0d164ae0050405a14,0x9218604a494288188321,0x49424141eca0c6628e01,0x285828cc51c02505050a]) else (natLimbs [486670336,0xc11a90480,0x18000044209003008240,0x9863a086a28a122b802,0x904581067818a0c66441,0x670114281882100004c6,0xa161303800c680cc2607,0x2e1303800c2608d584,0x130e03000a0300081803,0x8004430200d0181610,0x100000280d0200c02001,0x81a04008004068300803,0x800606829e0c840d01,0x8542060c040894080008,0x588109438c3610800943,0xc20d881808029820104,0xa2020000f2100430002,0x2034304062038161b101,0x62022162043505843508,0x6a0c0410030c40988c36,0x11144a2915881310122b,0x86a18d4105b08285d12,0x540450a8a0416084002,0x1057818a0e89c00ae284,0x2230d83c01d0a3a1c840,0xd02048a1c8542450e438,0x53138018ea15c00c59c0,0x45074045048ae0042c04,0x822c082bc0c50633220b,0x3808a146744a022840af,0x31418b029c0c5082845,0x5120bc01c0cc41604068,0x50428850415008003008,0x2a183514050e0b44a0,0x228420854245022c0a00,0x40020b02801000839450,0x1431613c821410728a08,0x74220832010061040203,0xa03000802000c860d,0x25018340864200000000,0x12e1304181002081840,0x702c303080e058610008,0x4003006010008000340a,0x584060a0309940b2818,0x28305040428205041430,0x206101836102250202a0,0x8541050c850894087584,0x390c5803008004a10304,0x61406002010020016083,0x9250183408b020304181,0xa868400840d0200c0200,0x140200081a0400800406,0x83008030080060073050,0x20601000400000e49410,0xe60c10e60a10e60a10e6,0xa10000d50810d41006a,0x85086a080850401c9282,0xc0e0021a607001,0x41303800800000000108,0x800e05848500850b816,0x942040021018941417,0x4a0c58081494100000,0x4160901800905824060,0x2010020016080525048,0x1160400025c106034200,0x420702c2001c0b0800c0,0x401618410a8400888116,0x428031283000020808a,0xe9404e0080da57003160,0x40018b0106f01941b0c,0x161b0982c0101a006506,0xcae00ac31d0ad82c0119,0x5c01586c160042c0600c,0x200141a0c0200c02001,0x80808e81a104c1010280]))))
def g253H7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (natLimbs [0xacb2fa00,0x39ca000000000000,0x377800000000066e,16036,0x59e00000000000938,0xa1be2f8a5c0000,0x385000030379,0x56544000131800000000,0x299724800024209bf87,0x40000000001094001e4c,0x18e79760009ad0000,0x89400000000000,0x22d403000000061bce,0x6060bb64000000000000,0x65a20b0eb,0x80000000a36a2e000f73,0xfbf00016461880000000,0,0,0xa5327eb8880,0x14cb0004c0400012,0x17ad8000000000000000,0xb4cd7735aa1e4000,24784,0x5238aa651c2,0x3aec59d9b10300000000,0x48a62900a1d1,0x3cc00000000000000000,0x1a7100015a21a2000000,0x6aaf2d0000000000,0x608000001eec0000,0x242e404404417aca60,0x8d0000c5d1b,0xcc98fa3c000000000000,0x2958000000000000000,1318,0x357c0000002995,0xca2000000235acd20000,0x24e99eb6bcf30ebe64,0x6a0000000001572000a3,0x628f800000015b000000,0x1f420000000000000000,0x646e900000001dae,0x90280000000000000,0,0xf4a80,0x10fd67c03fc00000,0x424741611310400031f,0xfda00000002d2c000000,0x8b18000,0x1ca800002100012910,0x70828bbe,0x3c76779accb0001ccff4,0xb15670dbf38000542000,0xf141078000000000000,0x283e0000000000000,0xfa7000000056d0000,32832,7696547840,381984,0xa0007d40000a6b000000,0x309e74d0006c3c0012e2,0x112e5848001,0xc94000c4e2d90000f409,0x61800328fc8ad6c7b4c0,0x8a7800000000000,0x238c676440885535323,0xe000b060000000000812,0x1daf4638500290000000,471470792,0x86e00000000000000,0x9f00000000000c900000,0x38fa0003ae80000006f,0x79018000000000000000,0x3158000000000,0xdb14ccc001a2f88d8001,0x84600000045c1504e860,0x1d0a00000000034,0x28000000000000000061,0x800021d2000a98a2c400,0xb532ac35d6000000,0,0,0x83a0000002c320,0xe66b5771,0x70000299000000144000,0x1898000000d54f4a,0x80000000001000000000,0x67a9190000,0x7390000d414,0x2d142c00000086f8001c,0x2bd5f00011cae2a00000,5492953,0x82da553ca8110e000000,0x1180000000000000,9385678376,0xa04000b0c00000016408,0xd500000000000000004d,0x780016ad030110005320,0x80320030006111310000,0xa2012495100016512002,0x3c00070000065,0x1a300021106052020020]) else (natLimbs [5322,0x31460000002838,0xc240001,0x4d800000000000000000,0x23e000000000000,0x5a0c000000000000000,0x61cc24969433c,0xf46000153d0320000000,25013,0x1800000001a34c4c001c,0x57000000000000000000,0xe1e800000092,0x5000000140f05d000000,0x1a130000001a44534,0x6135888000b52cb64,0x50e00025280000000,0,0x2c54000b4,0x37b12ab08,0x6000649800051e000000,0x56f0007b80000,0x3d85d020000,357564422,0xbf0007924000ac47b480,0x1ec6000658581b24,0xb6a2000019c000e6f000,0xb35641f111512,0x1ac00000000000,13,0xa8cb9895fce173d8003d,0x7a000000000000000000,410,0x589e0000434000e67097,0xcd6317133f2833c771e1,0x29a000195bdbaaabfa2d,0x290967c9882a3cfa6cda,0x5819b155c00143f00030,0x241da00000000031d167,0x60600000001ab7000000,0x1e1cf0b0000c9ce41,0x722cc026b2e198000,0xe70c376d2400001e0,0x4c6800000023100000,0xe7700000000010f100,0x1bfa9b7c2100068e2c4,0x400000000028b6000000,1,0xe2d0001d0c0000000000,0xe3b00000000000,0xe3c000000147400045,0x5bad800000073ec001e4,0x7d9c8000000000000000,0xd3a0000000000000000,0x8c8000000000e228002]))
def g253D8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (natLimbs [876871336,0x221ffcc110ffa608877f,0x74597beba2cbdfdcd65e,0xfce6b2f7d73597be39ac,0xbdfdc165efce0b2f7d70,0x597be382cb7fdd165bfe,0xe6b2dff70597debaac9e,0xf9cd64f7ae6b27be7059,0x3deb82c97f5d954efaca,0xaa7bd64552febacc77f5,0xd263bfae131dff7558f7,0xeb2ac77fdd163bfee0b1,0xdfd7694fbeb2ca77f5d2,0x53f7cc929fbd6494fbea,0xa4a77f5c253bfeeca9df,0xd7654fbeb2aa77fdd153,0xf7cc8a9fbd6454effb82,0xa77f5da43bfaeb21f7e6,0x590fbeb2c87ef59243bf,0xae121dff7650efebb287,0x7fdd543bfaeaa1f7e655,0xfbeb2a87ef59143f7aa,0x8a1dff7050ff6aa6c5fb,0x94f62fdaa7b17ee43d8b,0xf6a1ec5fb55132fdaa69,0x97ed434cbf6992a37f5d,0x731bfae198dff754c7f6,0x992637fdc131fdca690f,0xed53486febacc17f5d26,0xbfae7305ff755837eb2,0xac17fdd160dfac8b05ff,0x735837eb1ac17f5da50e,0xfacb285fd74943df324a,0x1ef59250bfae72877e53,0x943f7b14a1fb4ca50fda,0x43285ff76542febb2a1d,0xf59550bfee8a87be6454,0x3deb22a1df55150bfee6,0xa877d53543f7b12a1fb4,0xc950fda42a85fd76902f,0xebac81df99640efacb20,0x7bd64902feb9c81fbd8a,0x40fda65205ff76502feb,0xb2817fdd540bfaeaa077,0xe65503beb2a81ef59140,0xf7aa8a05ff73503dea1a,0x81fbd8940fda64a05fd7,0x6cc2febae61df99730ef,0xacb985fd74cc3df32661,0xef59330fbac7987dd53c,0xc3eea1e61fbd8b30fda4,0x3985fd768c2febac61df,0x99630efacb185fd748c3,0xdf32461ef59230bfae71,0x87ef628c3f699461fb48,0x630ff2c1187f9508c2ff,0xbb2617f5d930bfeea987,0x7f754c2febaa61df1d53,0xefcca9877d654c2ffba,0x2617f5d130f7cc8987bd,0x644c3ef31a61f758d30f,0xbca6987dd534c3ef21a6,0x1f750d30fdae4987ef62,0x4c3f699261fb48530ff4,0xc0987f9604c3fd28261f,0xe54130bfaec185fd750c,0x3bf32861df59430bfae8,0x187be640c3deb2061fbd,0x8830fda42187ed54483f,0x729a41fb54d20fdc8690,0x7ed43483f6a8a41fbcc5,0x20fda62907ed50483f6a,0x241fbcc120fda60907f,0x565c43fb31e21fd58f10,0xfeca7887f553c43fab06,0x21fd54310fee61887f53,0xc42febac217f5ce10fd,0xa65087f775443fab2a21,0xfd55110feee6887f4734,0x43fb31a21fd58d10feca,0x6887f553443fb21a21fd,0x50d10feac0887f550443,0xfaa0221fdcc110fea608,0x85ff75442ffb9a21fb4c,0x910fda40887b771593da,0x38ac97ddc564cfacab1d,0xf57190ef6b9ec57b5c76,0x2bdae1b15ef714caf7b8,0x265af59161b7ae998def,0x73486f7b82437d5c660c,0xfacab06bd64582fab8ca,0x17d5c640beae31857f75,0x4c27ebb0615f5d430b7a,0xe8185f5710c3ec980617,0xbdcd20bdee29077665c4,0x3bab2e21ed59310fcec5,0x887e532c43f2906217d5,0xc610eecca8877565443d,0xbba221ed1d110f6cc888,0x7b564443f2b9221f9d89,0x10fca64887f260443f8b,0x221fc90110fe280887e,0x520442dfba221f948510]) else (natLimbs [0x602c0313,0x1cb4b02880e0b2f0a471,0x4a11300c21d2862844c0,0x2c874a18d8a10f0310dc,0x52092892585c48749150,0xb21d28415c405874a14,0x57101c14a0544824a303,0x915120928b0e458285c4,0x1e28160a17110ca05828,0x5c44a1e16092a1710e45,0x8285c44a1b160a1710d4,0x4c4821e2c4a152857101,0x4e45054ac4391014b0e4,0x3051d4cc439160857130,0xc3c14a92888285c41e28,0x1617102c1d2858f811de,0xa3a2470e8dc11a2a3224,0x6168bc116ca2c645568a,0x4113ea26244a688f1112,0xa212440687b10e4a1ae4,0x32e85f10b4a14a425684,0x21074a0d2418682a1048,0xa07a40c6812101aa0224,0xe7fe0ff29fd23f5e7e,0x60fc09f6a3e9e7cd0f8a,0x9efe3dc67af0f529e8a3,0xcd67940f189e1a3c0677,0x80eda9d923ae67550e98,0x9d1a39fe73a0e649caa3,0x90e71c0e289c3238266f,0xe0dec9bb6372e6e00db4,0x9b5236766c90d869af63,0x5a66ae0d4a9a7234ae68,0xf0d0a99ee339e66e0cce,0x997632be64d0c8a98f23,0x19e62e0c4e987630ce61,0x20c1a9822301e5fe0bea,0x97b62f265de0bae97422,0xe465c10b7696da2d865a,0x90b42966e2cae5920b1a,0x961a2c1657f0af495ce2,0xb765680ac495722a9654,0xe0a8694ea299652c0a50,0x947e28ae50c0a0893fa2,0x7b64ef09c8938226c64d,0x10994930a25be4ae0950,0x928624c6493091c92222,0x40647b08ea91ba234e46,0x508c09166228e44c0890,0x910621ce433085890962,0xee4180824902a20163f,0xd07ee8fb61f4e3e307b8,0x8f5e1e863c807828ef21,0xdbe3b007548e821ce639,0x6071e8e2a1c1637b06de,0x8d9e1aee356069c8d221,0x9fe33606568c92190631,0xb06268c32181e2fc05ea,0x8bb2172e2de05b08b4a1,0x6662c605808ae215862a,0xa05468a7214b62910508,0x89fe13b626f04d2898a1,0x2de2540498892211fe23,0x8046288ae113e224043c,0x886a10ae20b040687f60,0xfc61f203d487920ede1d,0x6039e871a0e161be0374,0x86d60d861ae035086860,0xcee198031a861a0c1617,0xe02ee85c60b5e16202ac,0x85420a56145028084e20,0x99e12e024a847e08ce11,0x4021c842208060fa01e6,0x83ba074e0e201b4834e0,0x6760c9018682f605a60a,0xc0146827a04b608e0110,0x820603d607100d6819a0,0x30605b00aa813e024e04,0x4007c80e2019602e0050,0x808a00ee01a0028802e0,0x2e0001ff5d563ffae8b,0x1ffd5458fff382c7ff5c,0x163ffac929ffd6454ffe,0xb1aa7ff59543ffac6a1f,0xfd5350fff29ac3ff54d6,0x1ffeeab07fd75583ffba,0x2c1ff5d160ffaa8b07ff,0x73583ff39ac1ff5cd60f,0xf8e6b07fe53583fea9ac,0x1ff90d60ffa86b07fd63,0x943feb0ca1ff4c650ffa,0xc8a87fd63543fea1aa1f,0xf58550ffa62a87fd6054,0x3feb1c81ff59540ffcc6,0xa07fd63503ff29a81ff5,0x4d40ffac0a07fd50503f,0xeb2661ff58730ffac198,0x7fd40cc3feb1c61ff586,0x30ffa63187fd764c3feb,0xa261ff59130ffac6987f,0xd434c3feb8a61ff58530,0xffa62987fd604c3fea02,0x61ff58430ffca6887fd5])) else (if j<3 then (natLimbs [476336220,0xac019221018170034c05,0xf8685838284491c1a10,0xc128b058685474a23141,0x810552814e46c0871922,0x120a04c0e4482812c391,0x21a1108e214e46300904,0x1c0872c1e1a120a14d4,0x5874a2c0c3418112874e,0x460d0604024a14391c25,0x1300661c5460944c0871,0x9141a1d2a1a1510e4687,0x443a864a15391d2a1a10,0x50e450cc007132c14302,0x410b21f00747191505c0,0x607141e1e1a1610d454,0x842c874a14302c100c0,0x8670019289c015310e3e,0xe0b0128c068f8382c04,0xa2c191f00805048584c0,0x474a861a110e08d45301,0x2a1888f19144ac033181,0x30054c44c0472014103e,0x16120e0a192471085474,0xa31142c100c085453001,0x5289c019220e0f0208a1,0x28c0683c082284a2c191,0xf00307441e8684c0474a,0x851ca21a120b0128a873,0xb09050403020114c02,0xc2e1a120c9609261470f,0x830019c482064a852440,0x2e1a111d2a1471428331,0x5c0054a1c8b011064545,0xc0b040302c04a2c20cc,0x302c0c0810b301289190,0xc0b09030201c044152b2,0x8130f0b00ac6c00d300f,0x2b0f0b00ac58f048382c,0x4a301e3e0e0b0128b06,0x300f0c0901c0472c2074,0x342413011c507848685c,0x474a190e0a10d61b005,0x1288148f05c04a2c1814,0x523ccf00b12871405c04,0x42c1414c30110b053014,0xc0472c14541817011c50,0x6c3c2004a2c143e0e0a1,0x21a15247068483820f4a,0x2c1c42121a151d286148,0xf05c04a2c181a3c1700b,0x1286140544c02c14c01b,0x110b050bc4c30115140,0x403c2c0053333001434c,0x4428868382c0444a8523,0x20e08a219285474706c,0xc1d147a12191d2a146,0x382884864a2a1896120e,0xa1926147100b8485474,0xa311d1e28b03140f4643,0x42448a1520503d110d0a,0x28b07154644478a14185,0x5111e28505478a2c0d1e,0x28b034415478a0f1628b,0xbc3478a142d103d110d,0x8005450151a28a44434,0x2140f8a2c1d11021d28b,0x540874a2c10a11300b2,0x1d28649464144c087151,0xd13021cc0b0528464415,0xc005874a2113021c88b0,0x5304941c0872c18c1241,0x51107021cb081922280c,0x61ca0b04874a2c0d04b,0xa0a8444412c3910b0e4,0x2154441282a145519110,0x4a0a864a2c390e091128,0xb0e450b49464382412a4,0x4c0152815120b00c0b06,0x412c390c551050e44461,0x5c44a053919120b0088b,0x505c41d143914c02d25,0xe0904ab00b09300b490,0x5444382412ac02c2c061,0xc6454a050d0401282a16,0x10652a1c3c5874a0f2a1,0x20d0a2b10d050a07c014,0xc4361053120c3e285440,0x433c028c72c0a2067120,0xc18a05c42518c709143b,0x10242d1c545c425c7091,0x438c42c291c50b00c4c7,0x2e2c0a1c28d7109caa3c,0x68219c4140628191a1c2,0x88c445870a2310571053,0xc143e2874404c028c72,0xc0a1f13002850a0e061e,0x8405281057120c14a051,0x5c41e0528172864571f0,0x51415c406c0c7053320,0x5088372b1c1b001481dc,0xa15c41606c0052078181,0x4a0414cac42cc7c0051c]) else (if j<4 then (natLimbs [957117704,0x5228e45158a391314141,0x817022842cc08a0ccd10,0xb302285284443422c05c,0x8a20160101105628644,0x808a241514b015085228,0xe46208a3914120900cca,0x210652872a848040260b,0x4a1c360506010210682c,0x8220d42414043141e110,0x128886454320140c8836,0x11002d2868441400b1a1,0x489005611285822c4a33,0x3914743104e5105461d4,0xa0c3910752830e444140,0x1d0c44151910743031d1,0x44a39103410520c44281,0x41804035431422010098,0x2d2850580402c4a150e0,0x600507452c824028334a,0x18aa0100982d28642814,0x180400b1a1ccd1300b12,0x85201444c01d2c1a110a,0x5060100d50c509844ac,0x332c1612041b0030806,0x2a4443411ac02c1e1201,0x982d28684814180400,0xb1a1e10170128b058481,0x80141d14aa120e010098,0x2d2882a0d8381410b448,0x2c0462835120e040b002,0xcc480d0b8381c044821e,0xe0504a82f0208744838,0x28141c00b2a211d1914e,0x4e851328198a47151812,0x2b00e8b054f4342c0468,0xa151d3d0d0b006628547,0x3a04c04342288a2c2012,0x2b00e8b0543c04228458,0xa191d3d0d0b006628547,0x4c04342288a2c1c1a13,0x2291c5060c0b0302c08,0xa2c1c302e100c0b0228b,0x828134644c014381ca1,0x130050e052844c014381,0x51910e114e4546443814,0x39143c652a1c50587194,0xa1315150b004c50e050c,0xb0302c0068a15203413,0x2291c5060c0b040302c,0x8a2c20302c0c0b01122,0x85482806c00a442c1834,0x1302291c5060c0b04030,0x2012cc03324302c140c0,0x8070210cc98f8382c086,0x4a151d1e13008050585c,0x84474a861832150e08d,0x702112a189c013864715,0x14302c240c08041a1300,0x54a0c0b0302c04a301c3,0x2c0c086701285488f06,0x8382c0194a152027011c,0x509058685c084474a190,0xc321a1608d70211289c0,0x15310e1c14100464e4cc,0x7c087241510a21d28c04,0x28874a2c10a2130050e0,0x530140f0901c0872c203,0x61c14112880e47350f0d,0x4c04a87142064251302,0x1c5460944c08719141a1,0xd2a1a1510e4687443a85,0x4a19391c661300181d28,0x507c019071314161f008,0x5044746455335143d15,0xd09111a2470f4645434,0x244891d15111d18d4547,0x46454435151e28b03443,0x18a2c111467111e28b86,0x874a2c0c9054a0301872,0x82c1064061d1054a0687,0x4a1a0f103410061c68a0,0x64587468a2315148e1e2,0x8c450c0b440302c0058a,0x1926283074e442b0b030,0x2041514c0058a28302c0,0xc0b005628648281405c0,0xa442c1c3628181050e4,0x63914380c302c0c08b31,0x3022880619151428c033,0x50a242c180c08521300,0x1528983c08228854a191,0xd1e1300307451e86c084,0x474a851ca21a0b021128,0xa870b098403020114c00,0x5192b011a14386832582,0x8449851c3e120e0a1528,0x6470b86474a852318302,0xc0c0b0128c070c0b0684,0x302c0154a1928523c16,0xe0b0065285490c09c04,0x730161a1702111d28643,0x868235c014844a23004d]) else (natLimbs [0xe8906513,0x22863528200c4243c08,0xa20310e02284c6463328,0x422cc08a1910ccb30228,0x53542814180400d840c4,0x328903611090500310c8,0x244019844a1431050081,0x10646200c40834a14343,0x1120c4448040260b8a18,0x903512002e286c08a441,0x510e8885513022868a14]))))
def g253H8 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then (natLimbs [0x1ee3800000000000000,0,0x1545b14a000000000,29,0x15800073580000000000,0x144180012d0000,980736,0,0x25180004b72000,5814272,0x63b000000000,0x2a0acc70000,0,0,0,0x1251db5600063df8b2,0,0,0x2ccf4798474,0x58440000000000418,0x3f218000000000127310,0x2e0000001ca180000000,0x1e6300000000000000,0x4cc6aea80004d,0x88854000000000000000,0,0,674432,0,0x108f8000000,0,0xc19ba000000000,1,0xbf80000000000000000,0x3136000292f2ee80,0,0xa3c000,0x1d20809f67,0x70000000000000000002,0xa4000000000000000000,0x629b12dfaee000000,0x5ca0ee700,0x456234e00000000000,666,0xd37ae718000000738600,4446486528,0,0,0x1f27000000000,0x320261b80014e40,0,0x313e000000000,11456,0,0,0x9400000ccf00d000000,0x4220000000307e0000,0x93b8000000,0,0x13e60000000000738ca,0x9c000000000000001189,0xa9b8000ce28000000000,0x341000052d809e00,0,0,0,0x10200000000,25524,0x70ce379a978000000230,0xa00000000005a3200063,0x20000000b3c80000007,0x9e200000000000000000,0x40460000000000000000,0,0,0,0x396000000180680,0x6b468f000000001,0x1180000000f228000000,0x62f3c86800000,0,0x30780000000,0x50a00000000000000000,0,0x133a93880002998,0x1aa7800021a,0x4a658f1424b65593e994,0x72420e3f800000000000,0x4298000000211c,0,0x163d0000000000000000,0,0x8348001e0f,0x80000000000000000000,0,1024,0x500c140468020000,0x16400000090030000c10,0x8000080000208008210,0x4c00000000100082e004,0x80801100010482002082,0x40012000018400608000]) else (if j<2 then (natLimbs [1879296,0,0x3280000000000000,0x107a000184000,0x698600004960,0x1a5500000000000,0x90c00000000000000000,7696547840,0,76446019,0x8489f488000000000000,0,0x63800000000000000000,0x3229b18800,0xb200000,0,0,0,0x1028000000000000,0xb1600003448000,0x22160003c6e659800,0,0,6758,0x800000008e00007cda00,0x532c000490a3,0x1180002c980000000000,0x33c20000528000000,0xd2e800192d00,0x5b3e00000014a14,0x99800000000520000000,0,0,0,0x2c3f007b030000000000,0x1069ea1c00018c400000,0x483000000000000,0xa3680000000000127,0x80000000000000000000,0,0xc1f000110d8000,0,27776,0,0x665000000004ec000,0x60e8000000000113,0xa8000000000000000000,0,23422976,0x1e5e800183900,0,0,0x74c32878000000000000,0,0,0x1990000000,0xebd800000000,92672,0,0x12f90000000000000,0x313000000000000,0,0x297400064d,0x80001b42000000000000,0x85a80000000,4258,0x80000000000000000000,0,0,0,0,0xac421600000001a920,0x14848000000,0x50800000000b3,0xd74c54ea3b6000000000,345989320,0,0,0x14d200000000,0x51240000000000,301,0xc0000000000000000000,0x1c4e53c31f2c62c984,0,0,0,0,0x654800194,0x1000184e289c00000000,0,0,0x1638b1bf02180,94248,0x1a5900000000000000,0x797c000601000,0x59ec00000000,0,0x6a34605800,18,0x3aa57800000000000000]) else (natLimbs [314003624,0x52200000000000,1146368,0x4312000000000000018,0x3f00000005b880000000,0,0x3a8fc198000edf98,0x57efb000000000014dd8,0x3a2a0000000000,0,36583,0x1280018fb8000c3a8000,0,4812963840,0x1cfdec3c60600000b18,0xcfd00000000000000,0,5501878272,0,0,0x72d600000,0,0x81d8000000,0x6fe80000005bf9ce,0x800000000000000000c,0xe000012dd00000000000,0,0,19168,0xc7e04b8000,0x71f69038001d24800000,8240234496,0,9539584,0xee8800000000,1347,0xaa08b8800000000000a4,0x800000061b4000000000,137568,0,0,0,0x43a600000000000,0,0x3390000000000000,30,0x13800000000010c58001,0x8160001d0900006c2000,0x16c052ac00000,0,0x40342cc8000000,0x1925000000,0x3af0a7280018a09b140,0,0x1bd6000000,0x45080000b4400069,0xd400000002a580000005,0x7200000000000000000,0x10700000000f07800000,0x23bc00000000,0,0x490c0000000885000,48,0x28000000000000000000,3774,0x80000000000000000147,0xa8000000000000000008,0xdae4d40007d200000000,0x12740000000000,0xa070000273800000000,0xa93800167800000000,0xab100000004050000,0x390e0000000000000000,0xcf3800000000008,0x800000000001acb8000,0,46052,0x8e7d00000000001aca0,0,0x94e086000002e800000,0x6b92000000000000008,0x4800000000000000c52,0xe5da40,0x20000000000000000000,0xc7600000000000,0x1cab80000000001294,0x8000000000000048d4a9,0xcca22294402cabe00000,0xc3a0000000,0xa3e800000011aa000000,0x88c0000000000000000,7,0x406000000000000008c3,6304652,0x10000000000000000000,0,0,0,5,0x526000000024a0000000,0,5512364032,0]))) else (if j<4 then (natLimbs [0x515d2ac643e00070,0x26000000000000000000,0x8d339330268000000,0x68bc67c0000000000000,0,509116417,0xa0e00000000000000694,0x400053656810000e3a00,117624,59899904,620756992,0,0,76604769412,0xa0000000000000000000,0x1c28800000000000000,0x1a5509e8000000,0x8ec0000000000000000,5920048896,0xe8000000000001,0xe7fa0de000734a000000,0x16c8000102d00,0x89680000000,0,0x3180000000000,0xaf640f00,0xa940000000,30455808,0,3,0xaa8000431a0000000000,0,10,0x8b0000000000000014f7,0x72a00000000000000047,0xd4f44808000000000000,0x4d68000000000108d8,0xcff00014d6,0xd430000000000000,8311537664,444825600,0,0x123e000000000,10520,0,1236992,0,0,0,0x30a400000,0x18a9a3ca0003,0xccc00000000000000000,0x1e18800029,0x60000000000000000000,0x79420000000,0x33500000000917800,0x1a4f0000000000000000,101872,0xe0780000000000000,0x1418000080f0000b1,0x70000000000000000000,0x7a600001cfa,2787328,0x12678000000608400000,74407,0xc5000000000007256a2d,0x80000002cc18c7800e00,0x3d5f1500000,0x105c00000000000,0x6a300000000cc,0x8000000161338c200000,0x14d780000007,0x88e00000004d7000132c,0x121d000186c391e6f,0x88000000000000000000,0,512,0xa0000000000000000000,0x21bc0000001eaa8,0,0x70ad47900000006c9a00,0x4be000042bc0,0x306400000000000000,0x588c0000025d32800,0x1d057352093000000000,0x194000000000000,261,0x80000000000000000000,0,16648,0x1b800044a2000000,0x123c1b74b4da2600000,0x7c4800000000000,0x4b660000000000,0,377216,0xa5b0000,0,0x14fa8000d4400,0x1e2609d800000000003,0x89250b00000000000000]) else (if j<5 then (natLimbs [0x4cd20000000000000000,0,0,1564,0x80000178000000000062,0x8000000000000000004,0xbf000000000000000000,0x193980000004c2200,0x49a4000000000000001,0x2a800026880aa0000000,0x41c00000000000000,4955570176,5,0x91400000000000000000,0,0x39d200030ce00000000,0x14f180000000000,1682,0x36008000000284800000,0,0x5cae0000000000,0,143296,0x2c9800000000000000,0,767557632,0x6af800000000003184,0x1340000000000000031f,0x80000005130000000000,0x61de000000000000000,0x4980000000000,0,0xa45800000000,0x18ee0000cf480000000,0x63c8000,0,0x7cdecff800000000005,0xd0000f3700000000000,0x173f8000000000,576768,60848,0,0x7d06eba4904000000000,0x1eb9800000000004,0xae8000e0300000000000,0x17298000000000,0xb1b000000000010a600,0,0x1a8180000000000000,0,0,0,0,789120,0x10eb80000000,0x63f20000000a68,0x433800000000007d0200,0xcd80000000000a,0x1b000000000000000000,0xc5bc8b,0xe000000000000000007b,0x94000000000010140000,0x14c900000000000000,0x33a4000000000043ac00,0x7468c10b36800000000,0,0x1f048000000000,0x6910000000000000000,0,0,0,0,0,0,0x3c91a9a54,0x26000011b32c80000000,0,0,371488,0x6ce800000000000001,0x4f30001a830000000000,0,0x7cd070700000000,0x629d7068000000,0,115712,0x42c00000007082,0,8,0xf2000000000000000000,0,0xc1a800000,0x113a000000000000000,0x88b80000000000,0,345728,0,0xe4b4a109478000000,5467648,304576,0,0x191ec39a000000]) else (natLimbs [1590400,27280,0x6ae40000000000,0x1b2000008b,0,2304,0x5c44000000,0,0,0x11680000000000000,0,0x193f000000000000,0x21c2000026c0000001,0x67a5ad0000000066b823,0x869d48520001c6a00000,0,318,0,0x4822000000000000000,280690689,0xe6b000000000000bafa7,0xe40143bfebd000000000,52952,0x28dc0000000000,0,0x71ba000000000000000,0,0xd00000,0,0,0,102,0x4db22000000000000000,0,0,0x63d800000000,0,0x62620000000000,0,0x62c200000000,811,0xe22c39e0000000b2f000,0,0,0,0,0x6b8400000000,0x3d2a000000111e0001,0x43300000000000000000,0,0x25c800000000000000,0,95219089408,4956442944,0,0,24,0x96000000000000000000,0x162423b20000001017,0x8000000000000029c48c,0xc0b18000000000000000,0,26318848,0x30000150e0001c3600,0x2ada000000087eb,0xd6000785c0000000000,37,0x300000000000ad500000,0,0x44bf2900000000000,0,0x54900000000,0,0,0,520159232,0x2e600000000000000000,0,4,0x52cd1c800000064a4000,0xa6779696a,0x2000000000000005ad47,0x42ec43800000000018c6,0,0x1c8400069a800000,42049,0xce0c1680017230000000,0]))))
def g253D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x1d060b014048eb0512e4,0x30502503c088e090c165,0x2c801c98e1624050b238,0x6144060b02233511c510,0x3c2812b2a384801891e1,0x82b194123c0584940a04,0xcca89003862430595110,0x14801c8002a20f0e9c65,0x81c8a81028100662060e,0xa080a10080621d40e181,0x1529022288e145141a00,0x588a238a1c7860404c94,0x951c2400a58f0c1514a0,0x91e02c2430195116400e,0x1480c1464a8876007207,0x8133282c48f003123c10,0x12856506891e0052c201,0x1e182c4951e02c28a0f0,0x80c10a2b2a2470d0029a,0x180802b1028750406030,0x2c40ea0780a23841428,0x480a238a160440e28407,0x1444702864b12389100,0x6891c50b1038a0c0058,0x91c50b282c4801c50416,0x240722fa2ebbc9b746aa,0xccb882edd9dadb52e86c,0xd691514e003bb6facfd7,0xd2a74b67e8de1852b84c,0xc888e117e2583d852052,0x3fd65ff593fd54ff98,0xffd63ff94ffd53ff90ff,0xd43ff587fd51ffcc7fd3,0x1ff983fd60ff943fd50f,0xf903fd40ffcc3fe30ff4,0xc3fc30ff843fd10df997,0x7d65ef993bd64fbd8bed,0x32fb487ed20fdc43f510])
def g253H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (natLimbs [0x552aeaca,0x9128000000015c000c26,0x800000144600000001ae,0,0x9680000000001931c900,0x107800000000000,0x1afd000595800000,0xe7200004ee000000000,0xf122920000000000,0x96500000000000000000,0x428ba880000000000,9,0x7a000a868000000eeab3,0x1b4f2290000107000000,0xe55000,0x400005880000000,0xf8311940000000001,0xb095a4a2980508180000,793138,0xa3cb0000d5dba340008f,0x7762ad4c000000000000,0,0x386c0000000000,0x94b0000003d2a91a0,0x25a00093ff4500,201472,28672,0x2c6feb693d,0xc3c0000000000001c1b,0xaf2000131029813be2c8,0xb1280000000,0x12000000000188900049,0xac000076000000208a00,0x3840000000000000,0xc0a0160000000000000,0x170a0660002,0x9c000304486c000a44d,0x239c0c00000002e00000,0x80c00059410860f400,0xe1f8000a3,0x8000828e3e4000000000,0x54080000000000000000,0,0x1cb60000003a5e4712,0xf537b0003800c03580d3,0x35216000000000000000,0x733000392843b000000,0x35c2000d8b0002475e3c,0xf43d80400166ab136060,493879296,0xb372af00,0xc7380008d000047,0x222d5460000007c7c00,0xe5a800306600045a,0xb400004730000000001,0x32600000000000000005,0xa2396600000000000000,0x147303509f1a,0x840006ecb634a9ee8766,0x700023bd8d8000000000,0x5402b74000b52,0xda951ea504ab0,0xce00000000001e440008,0x83800283400000073700,0,0x24d402348a478000000,0,0x4a40e180004a80000000,0,0xb1ee8a0,0x631251fdfe64200000,0x967fb6400000,0x928002563b1d000320,0xda8cf110006d08001b37,0xa200000010fe0000001,0x80e88fc8ab21b5040000,0x2a4e00059eaa070,0xf1534895800000000014,0x880000000007ac702581,0xe000384bb94000000000,0x18f1457f0f8000,0x2a73a7e0001420,0x99076a43a26c0,0x1200000000b39b736b,0xec0006ee00004c400000,0x3882000000000,0x3e00a3d0000003aaa000,0x30628a90001ba4,0xb9578840000000,0xc586de00000000,0x71b400102349,0x7d3a38c8000c24bbac00,0x2d2c67d50c,0x80000000000005cbb8f6,0xa09e222392,0x9840000000007b7f83e0,0xf17000000000000000,0xd5929d000000,0x991c9f0001ccb080004,0x44008042594400711114,0x11b0020071810421000,0x1000011000142100111,0x4100110910010020003]) else (natLimbs [1546,0xddb00001378000000000,0x13a80025a20000000000,0x4ae404e8a68,0x38800000000000000008,0x3a000000000000000000,0x1adb000000000,0x44fabe017e000000,36244140,63456,0x86080000016,0x15a120001404000b4c00,0xd5a2d6e64f553d2400,0x11b400018bdac,0x219c0000000000927941,0x20a6a78001efa0000b8a,0x10a00087180028f3e600,0x3a100009a70002c,0x6494a000727400000000,0x6c80000000347423000,0x194f0000000000000000,0x69d0000000,0x82d74ddb22de60000001,0xd03134000000334c0007,0x29000517c00000000000,0x751246c000a4,0xaf0bb810001d050001c8,0x4001f3000000034a6000,31840,0xe1530bca640000,0x8a400000000002,0xae0c3000000029a00000,0x7ccc000000000000000,0xb348000000000a18,0x12b7d09fc64000,0xec0000482ee580000000,0xe5e00000039aad,0x49000495c00000082780,0x197c000000000000000,0x45580000ba000000000,5944,52789248,0x1aa500000018fc000b]))
def g253D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50838027f
def g253H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [2359296,0xda03000000002128e0,0x4020b57517508585,0xf8666d9663793000050,0x7921e540000394c66d2b,0x70000010a00081b24220,0x5f00000003c85,0x47e00000023f870d1004])
def g253L : Nat → Packing
  | 4 => (17,6,6,0,0,7,0,g253D4)
  | 5 => (106,5,6,0,0,10,0,g253D5)
  | 6 => (369,4,6,0,0,13,0,g253D6)
  | 7 => (663,3,6,0,0,15,0,g253D7)
  | 8 => (345,2,6,0,0,15,0,g253D8)
  | 9 => (35,1,6,0,0,11,0,g253D9)
  | 10 => (1,0,6,0,0,0,0,g253D10)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 89 2 9 5 0 g253H5
  | 6 => lookupWord 26 127 7 11 7 0 g253H6
  | 7 => lookupWord 92 929 4 13 9 0 g253H7
  | 8 => lookupWord 165 3389 3 14 10 0 g253H8
  | 9 => lookupWord 86 863 4 13 9 0 g253H9
  | 10 => lookupWord 8 59 3 10 6 0 g253H10
  | _ => fun _ => none
def g253 : Forest := ⟨253,10,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P4_0 : block g253 4 0 17=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B4 : block g253 4 0 17=true := g253P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P5_0 : block g253 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P5_2 : block g253 5 2 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P5_98 : block g253 5 98 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B5 : block g253 5 0 106=true := (@block_merge g253 5 0 2 104 g253P5_0 (@block_merge g253 5 2 96 8 g253P5_2 g253P5_98))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_0 : block g253 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_1 : block g253 6 1 41=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_42 : block g253 6 42 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_138 : block g253 6 138 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_234 : block g253 6 234 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_330 : block g253 6 330 39=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B6 : block g253 6 0 369=true := (@block_merge g253 6 0 138 231 (@block_merge g253 6 0 1 137 g253P6_0 (@block_merge g253 6 1 41 96 g253P6_1 g253P6_42)) (@block_merge g253 6 138 96 135 g253P6_138 (@block_merge g253 6 234 96 39 g253P6_234 g253P6_330)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_10 : block g253 7 10 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_106 : block g253 7 106 84=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_190 : block g253 7 190 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_286 : block g253 7 286 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_382 : block g253 7 382 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_478 : block g253 7 478 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_574 : block g253 7 574 89=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 663=true := (@block_merge g253 7 0 286 377 (@block_merge g253 7 0 106 180 (@block_merge g253 7 0 10 96 g253P7_0 g253P7_10) (@block_merge g253 7 106 84 96 g253P7_106 g253P7_190)) (@block_merge g253 7 286 192 185 (@block_merge g253 7 286 96 96 g253P7_286 g253P7_382) (@block_merge g253 7 478 96 89 g253P7_478 g253P7_574)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_51 : block g253 8 51 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_147 : block g253 8 147 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_243 : block g253 8 243 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_279 : block g253 8 279 66=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 345=true := (@block_merge g253 8 0 147 198 (@block_merge g253 8 0 51 96 g253P8_0 g253P8_51) (@block_merge g253 8 147 96 102 g253P8_147 (@block_merge g253 8 243 36 66 g253P8_243 g253P8_279)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_10 : block g253 9 10 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 35=true := (@block_merge g253 9 0 10 25 g253P9_0 g253P9_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 1=true := g253P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact g253B4
  · exact g253B5
  · exact g253B6
  · exact g253B7
  · exact g253B8
  · exact g253B9
  · exact g253B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 11 := lower_forest (g:=g253) (i:=0) (hints:=29956) (before_sound K238 V238) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def postedGraph : Sig := 0xfffffffffffffffffffffffffffffafaffffffffffeeffeefefefafaeeee0000fffffffffffffffffffffffffffffafaffffffffffeeffeefefefafaeeee0000
theorem postedGraphProper : proper postedGraph := by unfold proper; decide +kernel

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [5, 7]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.and, [13, 8]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.and, [5, 9]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 17]⟩], 20⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim

def eightInputs : List Sig := vars 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r postedGraph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (([16, 16, 32, 64, 1, 1, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((([16, 16, 32, 64, 1, 1, 1, 1] : List Nat).getD i.val 0) ||| (1 <<< i.val))

set_option maxHeartbeats 0 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) postedGraph ≠ bit (highRow i) postedGraph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true postedGraph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = postedGraph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 postedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) postedGraphProper
    (out.resolve_right (fun h => h postedGraphProper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true postedGraph 11 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by rw [witnessSize]; omega),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

def coreMoves : List Move := ([16, 33, 98, 84, 118].map swapRows) ++ fixRows 1 0
def removed : List (Sig × Row × Row) := [(eightInputs.getD 0 zero, 16, 17)]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem restricted : Lower true eightInputs postedGraph 12 := by
  have h := lift_ok (u:=true) (ms:=coreMoves) (T:=postedGraph) (raw:=eightInputs)
    (base:=varsX 253) (G:=graphGoal 253) (xs:=removed)
    (by decide +kernel) postedGraphProper (proper_of _ (by decide +kernel)) low253
  exact h

theorem excluded : Impossible true postedGraph 11 eightInputs.toFinset := by
  intro k small run
  have steps := list_run run eightInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper postedGraphProper)
    steps (eightInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := restricted q bank built hit
  omega

end PEqualNP.Outside.L_meta_31705

theorem PEqualNP.Outside.L_meta_31705 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_31705.replaceShort PEqualNP.Outside.L_meta_31705.excluded gates o fit correct

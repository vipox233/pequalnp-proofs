import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49153.Atlas.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
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

def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
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
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

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

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
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

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
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

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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

theorem canalize_left {R u d} (hd : allowed u d) (w : Bool → Wire R) :
    ∃ t, Constant (comb d (fun _ => t) (w t)) := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by funext r; simp [comb, combine]⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by funext r; simp [comb, combine, inv]⟩

theorem canalize_right {R u d} (hd : allowed u d) (w : Bool → Wire R) :
    ∃ t, Constant (comb d (w t) (fun _ => t)) := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by funext r; simp [comb, combine, inv]⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩

theorem contract_two {R S : Type} {u} {goal pivot : Wire R} {s ws}
    (run : Run u goal s ws) (rows : Bool → S → R)
    (value : ∀ b, restrictRows (rows b) pivot = (fun _ => b))
    (nonconstant : ∀ b, ¬Constant (restrictRows (rows b) goal))
    (occurs : pivot ∈ ws)
    (roots : Bool → List (Wire S)) {p : Nat} (banks : Bool → List (Wire S))
    (reached : ∀ b, Reach u (roots b) p (banks b))
    (supplied : ∀ b, supply u (banks b) (ws.map (restrictRows (rows b)))) :
    ∃ b q next, Reach u (roots b) q next ∧
      Available u next (restrictRows (rows b) goal) ∧ q+2 ≤ p+s := by
  induction run using Run.ind generalizing p banks with
  | stop =>
    have e : pivot = goal := List.mem_singleton.mp occurs
    exact False.elim (nonconstant false ⟨false, e ▸ value false⟩)
  | perm permutation _ ih =>
    apply ih (permutation.mem_iff.mpr occurs) banks reached
    intro b a ha
    exact supplied b a ((permutation.map _).mem_iff.mp ha)
  | @two steps a b rest op hd ka kb tail ih =>
    let next := comb op a b :: kept ka a (kept kb b rest)
    have pairA (t : Bool) : Available u (banks t) (restrictRows (rows t) a) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have pairB (t : Bool) : Available u (banks t) (restrictRows (rows t) b) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have held (t : Bool) {pool} (stable : ∀ w, Available u (banks t) w → Available u pool w)
        (head : Available u pool (restrictRows (rows t) (comb op a b))) :
        supply u pool (next.map (restrictRows (rows t))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | keep
      · exact head
      · apply stable
        apply supplied
        apply List.mem_map_of_mem
        rcases mem_kept keep with rfl | keep
        · simp
        · rcases mem_kept keep with rfl | keep
          · simp
          · simp [keep]
    by_cases used : pivot = a ∨ pivot = b
    · have choose : ∃ t, Constant (restrictRows (rows t) (comb op a b)) := by
        rcases used with eq | eq
        · subst a
          obtain ⟨t, hc⟩ := canalize_left hd (fun t => restrictRows (rows t) b)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
        · subst b
          obtain ⟨t, hc⟩ := canalize_right hd (fun t => restrictRows (rows t) a)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
      obtain ⟨t, hc⟩ := choose
      have sp := held t (fun _ h => h) (Or.inr (Or.inl hc))
      obtain ⟨q, out, reach, found, smaller⟩ :=
        contraction (nonconstant t) (restrict_run (rows t) tail) (roots t) (reached t) sp
      have one : 1 ≤ mass (next.map (restrictRows (rows t))) := by
        classical
        simp [next, mass_cons, cost, hc]
      dsimp only [next] at one
      exact ⟨t, q, out, reach, found, by omega⟩
    · have inRest : pivot ∈ rest := by simpa [List.mem_cons, not_or.mp used] using occurs
      have inNext : pivot ∈ next := by cases ka <;> cases kb <;> simp [next, kept, inRest]
      have all (t : Bool) : ∃ pool, Reach u (roots t) (p+1) pool ∧
          supply u pool (next.map (restrictRows (rows t))) := by
        obtain ⟨binOp, x, y, eq, hx, hy, _, _⟩ := comb_prime hd (pairA t) (pairB t)
        have new := Reach.two binOp (reached t) hx hy
        refine ⟨_, new, held t (fun _ h => available_cons _ h) ?_⟩
        rw [restrict_comb, eq]
        exact Or.inl (by simp)
      choose pools reach sp using all
      obtain ⟨t, q, out, rch, found, smaller⟩ := ih inNext pools reach sp
      exact ⟨t, q, out, rch, found, by omega⟩

abbrev Row := Fin 64
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
theorem input_list : List.ofFn (fun j : Fin 6 => inputs.getD j.val zero) = inputs := rfl
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
  if h : r.val < 64-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(64-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 64 (64-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 64-d.val <;> simp [shifted,h,r.isLt]

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
  (List.range 6).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def fixRows (z o : Nat) : List Move :=
  (List.range 6).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 64 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 64 d)

theorem lower_two_slices {u roots T pivot L}
    (properT : proper T) (plainT : plainWord T = true) (plainRoots : roots.all plainWord = true)
    (essential : Essential T roots pivot) (rows : Bool → Row → Row)
    (sub : Bool → List Sig) (goals : Bool → Sig)
    (mapTarget : ∀ b, rename (rows b) T = goals b)
    (mapRoots : ∀ b a, a ∈ roots → Available u ((sub b).map observe) (observe (rename (rows b) a)))
    (value : ∀ b, restrictRows (rows b) (observe pivot) = (fun _ => b))
    (properGoals : ∀ b, proper (goals b))
    (bounds : ∀ b, Lower u (sub b) (goals b) L) :
    Lower u roots T (L+2) := by
  intro p bank reachable hit
  obtain ⟨k, states, le, live, root⟩ := reach_live properT plainT plainRoots reachable hit
  obtain ⟨i, j, different, isolated⟩ := essential
  have pivotMem := raw_required live roots pivot root i j different isolated
  let front := states.toList.map observe
  have run : Run u (observe T) k front :=
    list_run live states.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have occurs : observe pivot ∈ front :=
    List.mem_map_of_mem (Finset.mem_toList.mpr pivotMem)
  have target (b : Bool) : restrictRows (rows b) (observe T) = observe (goals b) :=
    (observe_rename (rows b) T).symm.trans (congrArg observe (mapTarget b))
  have nonconstant (b : Bool) : ¬Constant (restrictRows (rows b) (observe T)) := by
    rw [target]
    exact observe_proper (properGoals b)
  let banks := fun b => (sub b).map observe
  have covered (b : Bool) : supply u (banks b) (front.map (restrictRows (rows b))) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [←observe_rename]
    exact mapRoots b w (root _ (Finset.mem_toList.mp hw))
  obtain ⟨b, q, out, reached, got, weighted⟩ :=
    contract_two run rows value nonconstant occurs banks banks (fun _ => Reach.start) covered
  rw [target] at got
  have enough := bounds b q out reached got
  omega

theorem lower_cubes_two {u raw base0 base1 T G0 G1 j L r s z0 o0 z1 o1}
    (essential : checkEssential T raw [(inputs.getD j zero, r, s)] = true)
    (lowMap : checkMap (fixRows z0 o0) raw T base0 G0 = true)
    (highMap : checkMap (fixRows z1 o1) raw T base1 G1 = true)
    (lowBit : movedWord (fixRows z0 o0) (inputs.getD j zero) = zero)
    (highBit : movedWord (fixRows z1 o1) (inputs.getD j zero) = one)
    (properT : proper T) (proper0 : proper G0) (proper1 : proper G1)
    (low : Lower u base0 G0 L) (high : Lower u base1 G1 L) : Lower u raw T (L+2) := by
  let moves : Bool → List Move := fun b => if b then fixRows z1 o1 else fixRows z0 o0
  let sub : Bool → List Sig := fun b => if b then base1 else base0
  let goal : Bool → Sig := fun b => if b then G1 else G0
  have maps (b : Bool) : checkMap (moves b) raw T (sub b) (goal b) = true := by
    cases b
    · exact lowMap
    · exact highMap
  apply lower_two_slices properT (essential_plain essential).1 (essential_plain essential).2
    (essential_ok essential (inputs.getD j zero) (by simp)) (fun b => movedRow (moves b)) sub goal
  · exact fun b => (map_correct (u:=u) (maps b)).1
  · exact fun b => (map_correct (u:=u) (maps b)).2
  · intro b
    rw [←observe_rename, ←moved_eq_rename]
    cases b <;> change observe (movedWord _ _) = _
    · rw [show movedWord (moves false) (inputs.getD j zero) = zero from lowBit]
      exact funext bit_zero
    · rw [show movedWord (moves true) (inputs.getD j zero) = one from highBit]
      exact funext bit_one
  · intro b
    cases b
    · exact proper0
    · exact proper1
  · intro b
    cases b
    · exact low
    · exact high

theorem lower_fix_two {u raw base0 base1 T G0 G1 j L r s}
    (essential : checkEssential T raw [(inputs.getD j zero, r, s)] = true)
    (lowMap : checkMap (fixRows (1 <<< j) 0) raw T base0 G0 = true)
    (highMap : checkMap (fixRows 0 (1 <<< j)) raw T base1 G1 = true)
    (lowBit : movedWord (fixRows (1 <<< j) 0) (inputs.getD j zero) = zero)
    (highBit : movedWord (fixRows 0 (1 <<< j)) (inputs.getD j zero) = one)
    (properT : proper T) (proper0 : proper G0) (proper1 : proper G1)
    (low : Lower u base0 G0 L) (high : Lower u base1 G1 L) : Lower u raw T (L+2) :=
  lower_cubes_two essential lowMap highMap lowBit highBit properT proper0 proper1 low high

theorem lower_weaken {u roots T m n} (lower : Lower u roots T m) (le : n ≤ m) :
    Lower u roots T n :=
  fun p bank reached hit => le.trans (lower p bank reached hit)

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
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

abbrev Bits := BitVec 128
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 128 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 128 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 128 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 128 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
def asRow (cols : Nat → Bits) (i : Fin 128) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 6 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem input_coords : ∀ (j : Fin 6) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 128) (j : Fin 6) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 6 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<6 ∧ a=inputs.getD j zero := by
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
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun n w => n+keyWord w) 0

theorem contract_two_cost {R S : Type} {u} {goal pivot : Wire R} {s ws}
    (run : Run u goal s ws) (rows : Bool → S → R)
    (value : ∀ b, restrictRows (rows b) pivot = (fun _ => b))
    (nonconstant : ∀ b, ¬Constant (restrictRows (rows b) goal))
    (occurs : pivot ∈ ws)
    (roots : Bool → List (Wire S)) {charges : Bool → Nat} (banks : Bool → List (Wire S))
    (reached : ∀ b, Reach u (roots b) (charges b) (banks b))
    (supplied : ∀ b, supply u (banks b) (ws.map (restrictRows (rows b)))) :
    ∃ b q next, Reach u (roots b) q next ∧
      Available u next (restrictRows (rows b) goal) ∧ q+2 ≤ charges b+s := by
  induction run using Run.ind generalizing charges banks with
  | stop =>
    have e : pivot = goal := List.mem_singleton.mp occurs
    exact False.elim (nonconstant false ⟨false, e ▸ value false⟩)
  | perm permutation _ ih =>
    apply ih (permutation.mem_iff.mpr occurs) banks reached
    intro b a ha
    exact supplied b a ((permutation.map _).mem_iff.mp ha)
  | @two steps a b rest op hd ka kb tail ih =>
    let next := comb op a b :: kept ka a (kept kb b rest)
    have pairA (t : Bool) : Available u (banks t) (restrictRows (rows t) a) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have pairB (t : Bool) : Available u (banks t) (restrictRows (rows t) b) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have held (t : Bool) {pool} (stable : ∀ w, Available u (banks t) w → Available u pool w)
        (head : Available u pool (restrictRows (rows t) (comb op a b))) :
        supply u pool (next.map (restrictRows (rows t))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | keep
      · exact head
      · apply stable
        apply supplied
        apply List.mem_map_of_mem
        rcases mem_kept keep with rfl | keep
        · simp
        · rcases mem_kept keep with rfl | keep
          · simp
          · simp [keep]
    by_cases used : pivot = a ∨ pivot = b
    · have choose : ∃ t, Constant (restrictRows (rows t) (comb op a b)) := by
        rcases used with eq | eq
        · subst a
          obtain ⟨t, hc⟩ := canalize_left hd (fun t => restrictRows (rows t) b)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
        · subst b
          obtain ⟨t, hc⟩ := canalize_right hd (fun t => restrictRows (rows t) a)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
      obtain ⟨t, hc⟩ := choose
      have sp := held t (fun _ h => h) (Or.inr (Or.inl hc))
      obtain ⟨q, out, reach, found, smaller⟩ :=
        contraction (nonconstant t) (restrict_run (rows t) tail) (roots t) (reached t) sp
      have one : 1 ≤ mass (next.map (restrictRows (rows t))) := by
        classical
        simp [next, mass_cons, cost, hc]
      dsimp only [next] at one
      exact ⟨t, q, out, reach, found, by omega⟩
    · have inRest : pivot ∈ rest := by simpa [List.mem_cons, not_or.mp used] using occurs
      have inNext : pivot ∈ next := by cases ka <;> cases kb <;> simp [next, kept, inRest]
      have all (t : Bool) : ∃ pool, Reach u (roots t) (charges t+1) pool ∧
          supply u pool (next.map (restrictRows (rows t))) := by
        obtain ⟨binOp, x, y, eq, hx, hy, _, _⟩ := comb_prime hd (pairA t) (pairB t)
        have new := Reach.two binOp (reached t) hx hy
        refine ⟨_, new, held t (fun _ h => available_cons _ h) ?_⟩
        rw [restrict_comb, eq]
        exact Or.inl (by simp)
      choose pools reach sp using all
      obtain ⟨t, q, out, rch, found, smaller⟩ := ih inNext (charges := fun t => charges t + 1) pools reach sp
      exact ⟨t, q, out, rch, found, by omega⟩

def dualPoolCut (c0 c1 : BoundPool) (cap : Nat) (ws : List Sig) : Bool :=
  decide (cap + c0.paid < c0.bound + 2) &&
  (decide (cap + c1.paid < c1.bound + 2) &&
  (ws.all (availableB true c0.domain c0.wires) &&
  (ws.all (availableB true c1.domain c1.wires) &&
  ws.any (fun pivot => masked c0.domain pivot == zero && masked c1.domain pivot == c1.domain))))

theorem dualPoolCut_sound {raw T c0 c1 cap ws}
    (valid0 : ValidPool true raw T c0) (valid1 : ValidPool true raw T c1)
    (nd : ws.Nodup) (test : dualPoolCut c0 c1 cap ws = true) :
    Impossible true T cap ws.toFinset := by
  intro steps hcap run
  simp only [dualPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, beq_iff_eq] at test
  obtain ⟨small0, small1, all0, all1, pivot, hpivot, zeroed, oned⟩ := test
  obtain ⟨f0, roots0, bank0, dom0, nc0, low0, paid0, avail0, _⟩ := valid0
  obtain ⟨f1, roots1, bank1, dom1, nc1, low1, paid1, avail1, _⟩ := valid1
  let rows : Bool → Row → Row := fun b => if b then f1 else f0
  let roots : Bool → List (Wire Row) := fun b => if b then roots1.map observe else roots0.map observe
  let banks : Bool → List (Wire Row) := fun b => if b then bank1 else bank0
  let charges : Bool → Nat := fun b => if b then c1.paid else c0.paid
  have nonconstant (b : Bool) : ¬Constant (restrictRows (rows b) (observe T)) := by
    cases b
    · exact nc0
    · exact nc1
  have value (b : Bool) : restrictRows (rows b) (observe pivot) = (fun _ => b) := by
    cases b
    · exact masked_zero dom0 zeroed
    · exact masked_one dom1 oned
  have reached (b : Bool) : Reach true (roots b) (charges b) (banks b) := by
    cases b
    · exact paid0
    · exact paid1
  have supplied (b : Bool) : supply true (banks b) ((ws.map observe).map (restrictRows (rows b))) := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    cases b
    · exact availableB_sound dom0 avail0 (all0 v hv)
    · exact availableB_sound dom1 avail1 (all1 v hv)
  have occurs : observe pivot ∈ ws.map observe := List.mem_map_of_mem hpivot
  obtain ⟨b, q, next, reach, hit, weighted⟩ :=
    contract_two_cost (list_run run ws nd rfl) rows value nonconstant occurs roots (charges := charges) banks reached supplied
  cases b
  · have enough := low0 q next reach hit
    change q + 2 ≤ c0.paid + steps at weighted
    omega
  · have enough := low1 q next reach hit
    change q + 2 ≤ c1.paid + steps at weighted
    omega

abbrev CutData := BoundPool × Option BoundPool
def ValidCut (u : Bool) (raw : List Sig) (T : Sig) (c : CutData) :=
  ValidPool u raw T c.1 ∧ ∀ b, c.2 = some b → u = true ∧ ValidPool true raw T b

def cutTest (u : Bool) (c : CutData) (k : Nat) (rest : List Sig) (op : Choice) :=
  match c.2 with
  | none => scalarPoolCut u c.1 k rest op
  | some b => dualPoolCut c.1 b k (choiceVal op :: rest)

theorem cutTest_sound {u raw T c k rest op} (v : ValidCut u raw T c)
    (nd : (choiceVal op :: rest).Nodup) (check : cutTest u c k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  cases h : c.2 with
  | none =>
    simp only [cutTest,h] at check
    exact scalarPoolCut_sound v.1 nd check
  | some b =>
    obtain ⟨rfl,hb⟩ := v.2 b h
    simp only [cutTest,h] at check
    exact dualPoolCut_sound v.1 hb nd check

def closeChild (u : Bool) (pools : Nat → List CutData) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || (pools (keySet ws)).any (fun p => cutTest u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact cutTest_sound (pValid _ _ hp) nd ok

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × (Nat → List CutData) × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 128 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 128) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 128 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
    (pv : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
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
  by_cases hj : j<6
  · let i : Fin 6 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 64 ≤ 2^j := by
      change 2^6 ≤ 2^j
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

theorem reflectState {u T k} (ws : List Sig) (p : List Move)
    (ok : autoOK T p = true) (low : Impossible u T k ws.toFinset) :
    Impossible u T k (ws.map (movedWord p.reverse)).toFinset := rotate_excluded low p ok

abbrev Observed (p q : Fin 128 → Row) := {v : Decor // faithful p q v}

def inputObserved (m : Nat) (p q : Nat → Bits) (i : Nat) :
    Observed (asRow p) (asRow q) :=
  ⟨(rawDecor m p q).getD i defaultDecor, faithful_get (raw_faithful m p q) i⟩

def combineObserved {p q} (d : Nat) (a b : Observed p q) : Observed p q :=
  ⟨dbin d a.val b.val, faithful_bin d a.property b.property⟩

abbrev Closed (T : Sig) (k : Nat) := { ws : List Sig // Impossible true T k ws.toFinset }
def rotateClosed {T k} (c : Closed T k) (p : List Move)
    (ok : autoOK T p = true) : Closed T k :=
  ⟨c.val.map (movedWord p.reverse), rotate_excluded c.property p ok⟩

abbrev Pool (raw : List Sig) (T : Sig) := { c : BoundPool // ValidPool true raw T c }

def checkedPool {raw T dom n} (slice : Slice true raw T dom n)
    (cs : List Choice) (c : BoundPool) (ok : materialize true raw cs dom n = some c) : Pool raw T :=
  ⟨c, materialize_sound slice ok⟩

def prefixPool {raw T d n} (slice : Slice true raw T d n) (cs : List Choice)
    (ok : makePool true d raw cs = some (cs.reverse.map choiceVal ++ raw)) : Pool raw T :=
  checkedPool slice cs (d,n,cs.length,cs.reverse.map choiceVal ++ raw)
    (by simp only [materialize,ok,Option.map_some,Option.some.injEq])

abbrev ChosenPool (raw : List Sig) (T : Sig) := {c : CutData // ValidCut true raw T c}
def usePool {raw T} (p : Pool raw T) : ChosenPool raw T :=
  ⟨(p.val,none),p.property,by simp⟩
def joinPools {raw T} (p q : Pool raw T) : ChosenPool raw T :=
  ⟨(p.val,some q.val),p.property,by
    intro b hb
    change some q.val = some b at hb
    cases Option.some.inj hb
    exact ⟨rfl,q.property⟩⟩
def stateCheck {p q T raw} (k : Nat) (ws : List (Observed p q))
    (route : Nat → List (ChosenPool raw T) × List (Closed T (k-1))) : Bool :=
  let items := ws.map Subtype.val
  let vs := items.map Prod.fst
  decide vs.Nodup && !vs.contains T &&
    testAll (k, items.length, items, preCov true items, (fun h => (route h).1.map Subtype.val),
      fun h => (route h).2.map Subtype.val) items

def closeState {T raw p q} (pairs : properPairs T p q) (k : Nat) (ws : List (Observed p q))
    (route : Nat → List (ChosenPool raw T) × List (Closed T (k-1)))
    (ok : stateCheck k ws route = true) : Closed T k := by
  let items := ws.map Subtype.val
  refine ⟨items.map Prod.fst, ?_⟩
  simp only [stateCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at ok
  apply node_sound (raw := raw) pairs _ ok.1.1 ok.1.2 _ _ ok.2
  · intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact a.property
  · intro _ c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact a.property
  · intro _ ys hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    exact a.property

def chooseRoute {α β : Type} (p : Array α) (below : Array β) (i : Nat) : List α × List β :=
  if i < p.size then ((p[i]?).toList, []) else ([],(below[i-p.size]?).toList)

theorem fromClosed {raw T k} (c : Closed T k)
    (names : c.val.toFinset = raw.toFinset) (xs : List (Sig × Row × Row))
    (pr : proper T) (check : checkEssential T raw xs = true) (all : xs.map Prod.fst = raw) :
    Lower true raw T (k+1) := by
  apply lower_impossible pr (essential_plain check).1 (essential_plain check).2
  · intro a ha
    exact essential_ok check a (List.mem_toFinset.mpr (all ▸ ha))
  · rw [← names]
    exact c.property

end PEqualNP.Outside.L_meta_49153.Atlas.Model
namespace PEqualNP.Outside.L_meta_49153.Atlas
open PEqualNP.Outside.L_meta_49153.Atlas.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace B0
def R : List Sig := vars 7
def T : Sig := 0xe8e8e8e8e8e8e8e8
def P : Nat → Bits
  | 0 => ((0xbecfbecfbecfbecf : BitVec 64) ++ (0xbecfbecfbecfbecf : BitVec 64))
  | 1 => ((0xdf73df73df73df73 : BitVec 64) ++ (0xdf73df73df73df73 : BitVec 64))
  | 2 => ((0xefbcefbcefbcefbc : BitVec 64) ++ (0xefbcefbcefbcefbc : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x4205420542054205 : BitVec 64) ++ (0x4205420542054205 : BitVec 64))
  | 1 => ((0x2412241224122412 : BitVec 64) ++ (0x2412241224122412 : BitVec 64))
  | 2 => ((0x1828182818281828 : BitVec 64) ++ (0x1828182818281828 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 7 P N 0
def w1 := inputObserved 7 P N 1
def w2 := inputObserved 7 P N 2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2]
  (fun _ => ([], [])) (by decide +kernel)
theorem low : Lower true R T 4 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B0

namespace B1
def R : List Sig := vars 15
def T : Sig := 0xe888e888e888e888
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 5, 13)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 5, 13)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B1

namespace B2
def R : List Sig := vars 23
def T : Sig := 0xe8e88888e8e88888
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B2

namespace B3
def R : List Sig := vars 27
def T : Sig := 0xee888888ee888888
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B3

namespace B4
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B4

namespace B5
def R : List Sig := vars 19
def T : Sig := 0xeeee8888eeee8888
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B5

namespace B6
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B6

namespace B7
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B7

namespace B8
def R : List Sig := vars 15
def T : Sig := 0xe880e880e880e880
def P : Nat → Bits
  | 0 => ((0xfc7fefee3fff8ff8 : BitVec 64) ++ (0xffdfdc7fff1ff1ff : BitVec 64))
  | 1 => ((0xff8ff7f7c7fff1ff : BitVec 64) ++ (0x1fefef8fffe3fe3f : BitVec 64))
  | 2 => ((0x1ff1fbfbf8fffe3f : BitVec 64) ++ (0xe3f7f7f1fffc7fc7 : BitVec 64))
  | 3 => ((0xe3fe3dfdff1fffc7 : BitVec 64) ++ (0xfc7bfbfe3fff8ff8 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x2436d021c9258248 : BitVec 64) ++ (0x6da043924b0490db : BitVec 64))
  | 1 => ((0x498b48407a4a9093 : BitVec 64) ++ (0x169080f49521262d : BitVec 64))
  | 2 => ((0x12d1848097932425 : BitVec 64) ++ (0xa309012f26484b46 : BitVec 64))
  | 3 => ((0x836c030124fc4906 : BitVec 64) ++ (0xd8060249f8920db0 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0xcccccccccccccccc 4 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[] ((((0x1442120181102 : Nat) >>> (((h / 8 + (((0xc189 : Nat) >>> ((h % 8) * 2)) &&& 3)) % 25) * 2)) &&& 3))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 3, 11)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B8

namespace B9
def R : List Sig := vars 29
def T : Sig := 0xfaa0a000faa0a000
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B8.low
end B9

namespace B10
def R : List Sig := vars 11
def T : Sig := 0x8800880088008800
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 10, 11), (0xcccccccccccccccc, 9, 11), (0xff00ff00ff00ff00, 3, 11)] (by decide +kernel)
end B10

namespace B11
def R : List Sig := vars 15
def T : Sig := 0xe880e880e880e880
def P : Nat → Bits
  | 0 => ((0xfc7fefee3fff8ff8 : BitVec 64) ++ (0xffdfdc7fff1ff1ff : BitVec 64))
  | 1 => ((0xff8ff7f7c7fff1ff : BitVec 64) ++ (0x1fefef8fffe3fe3f : BitVec 64))
  | 2 => ((0x1ff1fbfbf8fffe3f : BitVec 64) ++ (0xe3f7f7f1fffc7fc7 : BitVec 64))
  | 3 => ((0xe3fe3dfdff1fffc7 : BitVec 64) ++ (0xfc7bfbfe3fff8ff8 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x2436d021c9258248 : BitVec 64) ++ (0x6da043924b0490db : BitVec 64))
  | 1 => ((0x498b48407a4a9093 : BitVec 64) ++ (0x169080f49521262d : BitVec 64))
  | 2 => ((0x12d1848097932425 : BitVec 64) ++ (0xa309012f26484b46 : BitVec 64))
  | 3 => ((0x836c030124fc4906 : BitVec 64) ++ (0xd8060249f8920db0 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xcccccccccccccccc 4 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 0 w0 w1
def w5 := combineObserved 0 w0 w2
def w6 := combineObserved 0 w1 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w4, w5, w6, w3]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 2 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 4 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p4 : Pool R T := prefixPool s4 [(0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (3, 0x8080808080808080, 0xff00ff00ff00ff00)] (by decide +kernel)
def w7 := combineObserved 0 w4 w2
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w7, w0, w1, w2, w3]
  (fun _ => ([(usePool p2), (joinPools p3 p4)], [])) (by decide +kernel)
def w8 := combineObserved 0 w2 w3
def w9 := combineObserved 3 w8 w0
def v2 : Closed T 4 := closeState (raw := R) properPN 4 [w9, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def p5 : Pool R T := prefixPool s4 [] (by decide +kernel)
def v3 : Closed T 4 := closeState (raw := R) properPN 4 [w4, w5, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p5)] #[v0] ((((0x84 : Nat) >>> ((h % 9) * 2)) &&& 3))) (by decide +kernel)
def a0 : List Move := [swapRows 33, swapRows 48]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 4 := rotateClosed v2 a0 a0ok
def a1 : List Move := [swapRows 49, swapRows 32]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 := rotateClosed v2 a1 a1ok
def a2 : List Move := [swapRows 50]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r2 : Closed T 4 := rotateClosed v1 a2 a2ok
def a3 : List Move := [swapRows 16]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r3 : Closed T 4 := rotateClosed v3 a3 a3ok
def r4 : Closed T 4 := rotateClosed v3 a2 a2ok
def a4 : List Move := [swapRows 50, swapRows 16]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 4 := rotateClosed v3 a4 a4ok
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w4, w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p5), (usePool p2)] #[r0, r1, v1, r2, v3, r3, r4, r5] ((((((0x10b1119302 : Nat) <<< 64) ||| 0x8a21010740315600) >>> (((h / 8 + (((0xec000a : Nat) >>> ((h % 8) * 3)) &&& 7)) % 26) * 4)) &&& 15))) (by decide +kernel)
def a5 : List Move := [swapRows 32]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r6 : Closed T 5 := rotateClosed v4 a5 a5ok
def a6 : List Move := [swapRows 33]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r7 : Closed T 5 := rotateClosed v4 a6 a6ok
def r8 : Closed T 5 := rotateClosed v4 a0 a0ok
def a7 : List Move := [swapRows 48]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r9 : Closed T 5 := rotateClosed v4 a7 a7ok
def a8 : List Move := [swapRows 49]
theorem a8ok : autoOK T a8 = true := by decide +kernel
def r10 : Closed T 5 := rotateClosed v4 a8 a8ok
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p5), (usePool p2)] #[v4, r6, r7, r8, r9, r10] ((((((0x320367108 : Nat) <<< 64) ||| 0x2350104030391) >>> (((h / 8 + (((0x360b0231 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 25) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 3, 11)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B11

namespace B12
def R : List Sig := vars 29
def T : Sig := 0xfaa0a000faa0a000
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B11.low
end B12

namespace B13
def R : List Sig := vars 21
def T : Sig := 0xfafaa0a0fafaa0a0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B13

namespace B14
def R : List Sig := vars 30
def T : Sig := 0xfcc0c000fcc0c000
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B8.low
end B14

namespace B15
def R : List Sig := vars 30
def T : Sig := 0xfcc0c000fcc0c000
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B11.low
end B15

namespace B16
def R : List Sig := vars 22
def T : Sig := 0xfcfcc0c0fcfcc0c0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B16

namespace B17
def R : List Sig := vars 15
def T : Sig := 0xfee8fee8fee8fee8
def P : Nat → Bits
  | 0 => ((0xec33efee19e3bbd8 : BitVec 64) ++ (0x67dfdc33c777b0cf : BitVec 64))
  | 1 => ((0xf4ccf7f6667c3de9 : BitVec 64) ++ (0x99efecccf87bd333 : BitVec 64))
  | 2 => ((0xfb0f3bfb879fc1f6 : BitVec 64) ++ (0x1e77f70f3f83ec3c : BitVec 64))
  | 3 => ((0x3f03dfdf81ffe07 : BitVec 64) ++ (0xe07bfbf03ffc0fc0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x20115020a2008840 : BitVec 64) ++ (0x22a0414401108045 : BitVec 64))
  | 1 => ((0x4044884108841080 : BitVec 64) ++ (0x8910821108210112 : BitVec 64))
  | 2 => ((0x810a048050290102 : BitVec 64) ++ (0x140900a052020428 : BitVec 64))
  | 3 => ((0x2a0030005522005 : BitVec 64) ++ (0x4006000aa4400a80 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[] ((((0x1442120181102 : Nat) >>> (((h / 8 + (((0xc189 : Nat) >>> ((h % 8) * 2)) &&& 3)) % 25) * 2)) &&& 3))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B17

namespace B18
def R : List Sig := vars 11
def T : Sig := 0xffeeffeeffeeffee
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
end B18

namespace B19
def R : List Sig := vars 15
def T : Sig := 0xfee8fee8fee8fee8
def P : Nat → Bits
  | 0 => ((0xec33efee19e3bbd8 : BitVec 64) ++ (0x67dfdc33c777b0cf : BitVec 64))
  | 1 => ((0xf4ccf7f6667c3de9 : BitVec 64) ++ (0x99efecccf87bd333 : BitVec 64))
  | 2 => ((0xfb0f3bfb879fc1f6 : BitVec 64) ++ (0x1e77f70f3f83ec3c : BitVec 64))
  | 3 => ((0x3f03dfdf81ffe07 : BitVec 64) ++ (0xe07bfbf03ffc0fc0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x20115020a2008840 : BitVec 64) ++ (0x22a0414401108045 : BitVec 64))
  | 1 => ((0x4044884108841080 : BitVec 64) ++ (0x8910821108210112 : BitVec 64))
  | 2 => ((0x810a048050290102 : BitVec 64) ++ (0x140900a052020428 : BitVec 64))
  | 3 => ((0x2a0030005522005 : BitVec 64) ++ (0x4006000aa4400a80 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 1 w2 w1
def w5 := combineObserved 1 w3 w1
def w6 := combineObserved 1 w3 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w4, w5, w6]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def w7 := combineObserved 1 w3 w0
def a0 : List Move := [swapRows 32]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v0 a0 a0ok
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w7, w5]
  (fun h => chooseRoute #[(usePool p2), (usePool p1)] #[r0] ((((0x408 : Nat) >>> ((h % 6) * 2)) &&& 3))) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p3 : Pool R T := prefixPool s3 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xfefefefefefefefe, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 2 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B18.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
def w8 := combineObserved 1 w0 w1
def w9 := combineObserved 1 w8 w2
def v2 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w9, w3]
  (fun _ => ([(usePool p0), (joinPools p3 p4)], [])) (by decide +kernel)
def w10 := combineObserved 2 w8 w3
def v3 : Closed T 4 := closeState (raw := R) properPN 4 [w10, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def p5 : Pool R T := prefixPool s3 [] (by decide +kernel)
def a1 : List Move := [swapRows 50]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 := rotateClosed v3 a1 a1ok
def r2 : Closed T 4 := rotateClosed v2 a1 a1ok
def a2 : List Move := [swapRows 48]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r3 : Closed T 4 := rotateClosed v1 a2 a2ok
def a3 : List Move := [swapRows 49]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 4 := rotateClosed v1 a3 a3ok
def a4 : List Move := [swapRows 50, swapRows 32]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 4 := rotateClosed v1 a4 a4ok
def a5 : List Move := [swapRows 50, swapRows 33]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r6 : Closed T 4 := rotateClosed v1 a5 a5ok
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w8, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v3, r1, v2, r2, r3, r4, r5, r6] ((((((0x3010054b961 : Nat) <<< 64) ||| 0xa20003000071280) >>> (((h / 8 + (((0x9e2031001 : Nat) >>> ((h % 8) * 5)) &&& 31)) % 27) * 4)) &&& 15))) (by decide +kernel)
def r7 : Closed T 5 := rotateClosed v4 a0 a0ok
def a6 : List Move := [swapRows 33]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r8 : Closed T 5 := rotateClosed v4 a6 a6ok
def a7 : List Move := [swapRows 33, swapRows 48]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r9 : Closed T 5 := rotateClosed v4 a7 a7ok
def r10 : Closed T 5 := rotateClosed v4 a2 a2ok
def r11 : Closed T 5 := rotateClosed v4 a3 a3ok
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v4, r7, r8, r9, r10, r11] ((((((0x13934200 : Nat) <<< 64) ||| 0x1316710020080035) >>> (((h / 8 + (((0x40b1830 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 25) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B19

namespace B20
def R : List Sig := vars 23
def T : Sig := 0xfefee8e8fefee8e8
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B17.low
end B20

namespace B21
def R : List Sig := vars 23
def T : Sig := 0xfefee8e8fefee8e8
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B19.low
end B21

namespace B22
def R : List Sig := vars 25
def T : Sig := 0xffaaaa00ffaaaa00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50, swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B22

namespace B23
def R : List Sig := vars 26
def T : Sig := 0xffcccc00ffcccc00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B23

namespace B24
def R : List Sig := vars 27
def T : Sig := 0xffeeee88ffeeee88
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B17.low
end B24

namespace B25
def R : List Sig := vars 27
def T : Sig := 0xffeeee88ffeeee88
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B19.low
end B25

namespace B26
def R : List Sig := vars 28
def T : Sig := 0xfff0f000fff0f000
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B26

namespace B27
def R : List Sig := vars 15
def T : Sig := 0xfeeafeeafeeafeea
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B7.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B27

namespace B28
def R : List Sig := vars 29
def T : Sig := 0xfffafaaafffafaaa
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B27.low
end B28

namespace B29
def R : List Sig := vars 30
def T : Sig := 0xfffcfcccfffcfccc
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 65, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B27.low
end B29

namespace B30
def R : List Sig := vars 31
def T : Sig := 0xfee8e888fee8e888
def P : Nat → Bits
  | 0 => ((0x3e0f83e07e3e3f : BitVec 64) ++ (0xc7ff1fffffe071c7 : BitVec 64))
  | 1 => ((0x7c1f07c1f803fc7 : BitVec 64) ++ (0xf8ffe3ffffe38e38 : BitVec 64))
  | 2 => ((0xf801ffffffffc007 : BitVec 64) ++ (0xff1ffc70019c0fff : BitVec 64))
  | 3 => ((0xfffe007ffffffff8 : BitVec 64) ++ (0x1fff80061ff03f : BitVec 64))
  | 4 => ((0xffffff801fffffff : BitVec 64) ++ (0xffe00000181fffc0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0xaa82910c80160a09 : BitVec 64) ++ (0x41250492aaa030c3 : BitVec 64))
  | 1 => ((0x5054249065801442 : BitVec 64) ++ (0x884a212555418618 : BitVec 64))
  | 2 => ((0x1d6a52a52aaa4004 : BitVec 64) ++ (0xd2134840618c0b6d : BitVec 64))
  | 3 => ((0x618d6b4a534ca690 : BitVec 64) ++ (0x1c92018616d036 : BitVec 64))
  | 4 => ((0x86318c739c713927 : BitVec 64) ++ (0x24800006181b6d80 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
def w5 := combineObserved 1 w0 w1
def w6 := combineObserved 0 w3 w4
def w7 := combineObserved 2 w5 w6
def w8 := combineObserved 0 w2 w3
def w9 := combineObserved 0 w2 w4
def v0 : Closed T 4 := closeState (raw := R) properPN 4 [w7, w0, w1, w8, w9]
  (fun _ => ([], [])) (by decide +kernel)
theorem s0 : Slice true R T 0x5050505050505050 4 :=
  slice_correct (ms := fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B23.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
def v1 : Closed T 5 := closeState (raw := R) properPN 5 [w7, w0, w1, w8, w2, w4]
  (fun _ => ([(usePool p0)], [v0])) (by decide +kernel)
theorem s1 : Slice true R T 0x5555555555555555 7 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B15.low
def p1 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000), (0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
theorem s2 : Slice true R T 0xff000000ff0000 4 :=
  slice_correct (ms := fixRows 8 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf000f000f000f00 4 :=
  slice_correct (ms := fixRows 4 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0x5500550055005500 4 :=
  slice_correct (ms := fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
def a0 : List Move := [swapRows 50]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 4 := rotateClosed v0 a0 a0ok
def a1 : List Move := [swapRows 66]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 := rotateClosed v0 a1 a1ok
def v2 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w5, w8, w9, w6]
  (fun h => chooseRoute #[(usePool p1), (usePool p2), (usePool p3), (usePool p4), (usePool p0)] #[v0, r0, r1] ((((0xa200001882e0e10 : Nat) >>> ((h % 20) * 3)) &&& 7))) (by decide +kernel)
def p5 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xe0e0e0e0e0e0e0e0, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s5 : Slice true R T 0x3030303030303030 4 :=
  slice_correct (ms := fixRows 2 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B22.low
def p6 : Pool R T := prefixPool s5 [] (by decide +kernel)
theorem s6 : Slice true R T 0x4444444444444444 4 :=
  slice_correct (ms := fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B26.low
def p7 : Pool R T := prefixPool s6 [] (by decide +kernel)
theorem s7 : Slice true R T 0xff00ff00ff00ff 5 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B2.low
def p8 : Pool R T := prefixPool s7 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
theorem s8 : Slice true R T 0xff00ff00ff00ff00 7 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B21.low
def p9 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (3, 0xe000e000e000e000, 0xeeeeeeeeeeeeeeee)] (by decide +kernel)
theorem s9 : Slice true R T 0x5555000055550000 4 :=
  slice_correct (ms := fixRows 1 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p10 : Pool R T := prefixPool s9 [] (by decide +kernel)
def p11 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (3, 0xe000e000e000e000, 0xffff0000ffff0000)] (by decide +kernel)
def w10 := combineObserved 0 w5 w2
def w11 := combineObserved 0 w10 w3
def v3 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w11, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p5), (usePool p6), (usePool p7), (joinPools p8 p9), (usePool p10), (joinPools p8 p11)] #[] ((((0xcd294 : Nat) >>> ((h % 10) * 3)) &&& 7))) (by decide +kernel)
def p12 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000), (3, 0xeeee0000eeee0000, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
theorem s10 : Slice true R T 0xf0f0f0f0f0f0f0f0 7 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p13 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000)] (by decide +kernel)
def w12 := combineObserved 0 w5 w4
def w13 := combineObserved 3 w12 w2
def v4 : Closed T 6 := closeState (raw := R) properPN 6 [w13, w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p7), (usePool p10), (usePool p12), (usePool p3), (usePool p13)] #[] ((((0x1108a03010000 : Nat) >>> ((h % 19) * 3)) &&& 7))) (by decide +kernel)
def p14 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s11 : Slice true R T 0xaaaaaaaaaaaaaaaa 5 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B29.low
def p15 : Pool R T := prefixPool s11 [] (by decide +kernel)
theorem s12 : Slice true R T 0x3333333333333333 7 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B12.low
def p16 : Pool R T := prefixPool s12 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s13 : Slice true R T 0xcccccccccccccccc 5 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B28.low
def p17 : Pool R T := prefixPool s13 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w10, w5, w8, w3, w4]
  (fun h => chooseRoute #[(usePool p14), (usePool p15), (usePool p7), (usePool p0), (usePool p4), (joinPools p16 p17), (usePool p3)] #[] ((((0x845480018192 : Nat) >>> ((h % 23) * 3)) &&& 7))) (by decide +kernel)
def p18 : Pool R T := prefixPool s7 [(1, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa)] (by decide +kernel)
def p19 : Pool R T := prefixPool s8 [(1, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa), (1, 0xcccccccccccccccc, 0xf000f000f000f000), (1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000)] (by decide +kernel)
def p20 : Pool R T := prefixPool s10 [(1, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa), (1, 0xcccccccccccccccc, 0xf000f000f000f000)] (by decide +kernel)
def w14 := combineObserved 1 w1 w8
def v6 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w5, w8, w2, w14, w3, w4]
  (fun h => chooseRoute #[(joinPools p18 p19), (usePool p7), (usePool p0), (usePool p2), (usePool p3), (usePool p6), (usePool p20)] #[] ((((((0x300 : Nat) <<< 64) ||| 0x8600010620628c00) >>> ((h % 25) * 3)) &&& 7))) (by decide +kernel)
def p21 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xeeeeeeeeeeeeeeee, 0xf000f000f000f000)] (by decide +kernel)
def p22 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (1, 0xeeeeeeeeeeeeeeee, 0xf000f000f000f000), (0, 0xfeeefeeefeeefeee, 0xffff0000ffff0000)] (by decide +kernel)
def w15 := combineObserved 1 w5 w8
def v7 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w8, w2, w15, w3, w4]
  (fun h => chooseRoute #[(joinPools p8 p9), (usePool p4), (usePool p0), (usePool p21), (usePool p2), (joinPools p22 p17)] #[] ((((0x26511a : Nat) >>> (((h / 3 + (((0x1d0 : Nat) >>> ((h % 3) * 3)) &&& 7)) % 9) * 3)) &&& 7))) (by decide +kernel)
def p23 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xff000000ff000000)] (by decide +kernel)
theorem s14 : Slice true R T 0xffff0000ffff0000 7 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B19.low
def p24 : Pool R T := prefixPool s14 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xff000000ff000000)] (by decide +kernel)
def a2 : List Move := [swapRows 67]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r2 : Closed T 5 := rotateClosed v1 a2 a2ok
def v8 : Closed T 6 := closeState (raw := R) properPN 6 [w7, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p6), (usePool p7), (usePool p3), (usePool p0), (usePool p4), (usePool p23), (usePool p24)] #[v1, r2] ((((((0x5002005413 : Nat) <<< 64) ||| 0x246891200702000) >>> (((h / 8 + (((0xc2a3012 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 26) * 4)) &&& 15))) (by decide +kernel)
def p25 : Pool R T := prefixPool s1 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (2, 0xeeeeeeeeeeeeeeee, 0xff000000ff000000)] (by decide +kernel)
def v9 : Closed T 6 := closeState (raw := R) properPN 6 [w7, w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p6), (usePool p2), (usePool p25)] #[] ((((0x8c101 : Nat) >>> ((h % 11) * 2)) &&& 3))) (by decide +kernel)
def v10 : Closed T 6 := closeState (raw := R) properPN 6 [w7, w0, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p2), (usePool p4), (usePool p24)] #[] ((((0x3086100 : Nat) >>> ((h % 13) * 2)) &&& 3))) (by decide +kernel)
def v11 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w10, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p3), (usePool p4), (usePool p0)] #[] ((((0x144000463 : Nat) >>> ((h % 19) * 2)) &&& 3))) (by decide +kernel)
def w16 := combineObserved 3 w5 w2
def v12 : Closed T 6 := closeState (raw := R) properPN 6 [w16, w0, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p3), (usePool p7), (usePool p4), (usePool p0)] #[] ((((0x1400058220 : Nat) >>> (((h / 4 + (((0xc0 : Nat) >>> ((h % 4) * 2)) &&& 3)) % 17) * 3)) &&& 7))) (by decide +kernel)
def p26 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf000f000f000f000, 0xffff0000ffff0000)] (by decide +kernel)
def p27 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xf000f000f000f000, 0xffff0000ffff0000), (2, 0xeeeeeeeeeeeeeeee, 0xf0000000f0000000)] (by decide +kernel)
theorem s15 : Slice true R T 0xf0f0f0f0f0f0f0f0 6 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
def p28 : Pool R T := prefixPool s15 [(0, 0xf000f000f000f000, 0xffff0000ffff0000)] (by decide +kernel)
theorem s16 : Slice true R T 0xffff0000ffff 5 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p29 : Pool R T := prefixPool s16 [] (by decide +kernel)
def w17 := combineObserved 0 w8 w4
def v13 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w5, w17, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p26), (usePool p15), (usePool p7), (usePool p6), (usePool p2), (joinPools p8 p27), (usePool p3), (usePool p28), (usePool p29)] #[] ((((((0x6 : Nat) <<< 64) ||| 0x6235817402040424) >>> (((h / 5 + (((0x1b73 : Nat) >>> ((h % 5) * 4)) &&& 15)) % 17) * 4)) &&& 15))) (by decide +kernel)
theorem s17 : Slice true R T 0xf0f0f0f0f0f0f0f 5 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B3.low
def p30 : Pool R T := prefixPool s17 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def p31 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (3, 0xf0f0f000f0f0f0, 0xeeeeeeeeeeeeeeee)] (by decide +kernel)
def p32 : Pool R T := prefixPool s1 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (3, 0xff000000ff000000, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def p33 : Pool R T := prefixPool s15 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00)] (by decide +kernel)
def w18 := combineObserved 3 w6 w2
def v14 : Closed T 6 := closeState (raw := R) properPN 6 [w18, w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p3), (usePool p7), (joinPools p30 p31), (usePool p32), (usePool p33), (usePool p2), (usePool p29)] #[] ((((0x80101741400c1 : Nat) >>> ((h % 21) * 3)) &&& 7))) (by decide +kernel)
def p34 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000)] (by decide +kernel)
def p35 : Pool R T := prefixPool s16 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def r3 : Closed T 5 := rotateClosed v1 a0 a0ok
def a3 : List Move := [swapRows 67, swapRows 66]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 5 := rotateClosed v1 a3 a3ok
def v15 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w5, w8, w9, w3, w4]
  (fun h => chooseRoute #[(usePool p34), (usePool p2), (usePool p3), (usePool p35), (usePool p4), (usePool p10)] #[r3, r4, v2] ((((0x48613572240110 : Nat) >>> (((h / 5 + (((0x5 : Nat) >>> ((h % 5) * 1)) &&& 1)) % 15) * 4)) &&& 15))) (by decide +kernel)
def w19 := combineObserved 3 w1 w2
def w20 := combineObserved 1 w19 w0
def v16 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w20, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p15), (usePool p7), (usePool p2), (usePool p6), (usePool p0), (usePool p3)] #[] ((((((0x8 : Nat) <<< 64) ||| 0x4c000100d144) >>> ((h % 23) * 3)) &&& 7))) (by decide +kernel)
def w21 := combineObserved 3 w0 w4
def w22 := combineObserved 3 w21 w3
def v17 : Closed T 6 := closeState (raw := R) properPN 6 [w19, w22, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p6), (usePool p7)] #[] ((((0x81 : Nat) >>> ((h % 4) * 2)) &&& 3))) (by decide +kernel)
def w23 := combineObserved 0 w19 w3
def v18 : Closed T 6 := closeState (raw := R) properPN 6 [w23, w21, w0, w1, w2, w3, w4]
  (fun _ => ([(usePool p2)], [])) (by decide +kernel)
def w24 := combineObserved 3 w1 w4
def w25 := combineObserved 1 w24 w8
def v19 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w8, w2, w25, w3, w4]
  (fun _ => ([(usePool p2)], [])) (by decide +kernel)
def p36 : Pool R T := prefixPool s11 [(3, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def w26 := combineObserved 1 w0 w6
def v20 : Closed T 6 := closeState (raw := R) properPN 6 [w19, w0, w1, w2, w3, w26, w4]
  (fun h => chooseRoute #[(usePool p15), (usePool p4), (usePool p7), (usePool p6), (usePool p36), (usePool p0), (usePool p3)] #[] ((((((0x8 : Nat) <<< 64) ||| 0x20460007630020c0) >>> ((h % 25) * 3)) &&& 7))) (by decide +kernel)
def p37 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000)] (by decide +kernel)
def p38 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000), (3, 0xcccccccccccccccc, 0xfaaafaaafaaafaaa)] (by decide +kernel)
def w27 := combineObserved 1 w0 w8
def w28 := combineObserved 3 w1 w27
def v21 : Closed T 6 := closeState (raw := R) properPN 6 [w28, w0, w1, w8, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p0), (usePool p7), (usePool p37), (usePool p38)] #[] ((((0x8810000c0010 : Nat) >>> ((h % 18) * 3)) &&& 7))) (by decide +kernel)
def p39 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000), (0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
theorem s18 : Slice true R T 0xffff0000ffff0000 6 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B17.low
def p40 : Pool R T := prefixPool s18 [] (by decide +kernel)
def p41 : Pool R T := prefixPool s15 [] (by decide +kernel)
def v22 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w8, w9, w6]
  (fun h => chooseRoute #[(usePool p1), (usePool p39), (usePool p2), (usePool p3), (usePool p40), (usePool p41)] #[v2] ((((((((0x7124 : Nat) <<< 64) ||| 0x926984904b040305) <<< 64) ||| 0x250009d61b4c0082) >>> (((h / 16 + (((0xbe200c3019 : Nat) >>> ((h % 16) * 3)) &&& 7)) % 49) * 3)) &&& 7))) (by decide +kernel)
theorem s19 : Slice true R T 0xf0f00000f0f0000 4 :=
  slice_correct (ms := fixRows 4 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p42 : Pool R T := prefixPool s19 [] (by decide +kernel)
def v23 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w10, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p15), (usePool p3), (usePool p6), (usePool p0), (usePool p42), (usePool p2), (usePool p4)] #[] ((((((((((0x100135030e0 : Nat) <<< 64) ||| 0x40408401c0f01230) <<< 64) ||| 0x83180a13141c1749) <<< 64) ||| 0xa320a8400408080) >>> (((h / 27 + (((((0x19041031b8 : Nat) <<< 64) ||| 0x2300a1b223213000) >>> ((h % 27) * 4)) &&& 15)) % 80) * 3)) &&& 7))) (by decide +kernel)
def p43 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def p44 : Pool R T := prefixPool s12 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)] (by decide +kernel)
def p45 : Pool R T := prefixPool s13 [] (by decide +kernel)
def p46 : Pool R T := prefixPool s12 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000)] (by decide +kernel)
def p47 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def r5 : Closed T 6 := rotateClosed v4 a1 a1ok
def a4 : List Move := [swapRows 67, swapRows 50]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r6 : Closed T 6 := rotateClosed v4 a4 a4ok
def r7 : Closed T 6 := rotateClosed v3 a2 a2ok
def r8 : Closed T 6 := rotateClosed v5 a2 a2ok
def v24 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w10, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p43), (usePool p7), (usePool p0), (usePool p4), (usePool p10), (joinPools p44 p45), (usePool p3), (joinPools p46 p45), (usePool p42), (usePool p47)] #[r5, r6, v3, r7, v5, r8] ((((((((((0x111 : Nat) <<< 64) ||| 0x14011600103e5201) <<< 64) ||| 0x400110f1c1110b81) <<< 64) ||| 0x190190121d11a37) >>> (((h / 17 + (((0x401021100030c01 : Nat) >>> ((h % 17) * 4)) &&& 15)) % 51) * 4)) &&& 15))) (by decide +kernel)
def v25 : Closed T 7 := closeState (raw := R) properPN 7 [w16, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p3), (usePool p2), (usePool p4), (usePool p42), (usePool p0)] #[] ((((((((0x6022000200100 : Nat) <<< 64) ||| 0x24000000008114) <<< 64) ||| 0x20804506a200000) >>> (((h / 22 + (((((0x12008 : Nat) <<< 64) ||| 0x30000021010) >>> ((h % 22) * 4)) &&& 15)) % 65) * 3)) &&& 7))) (by decide +kernel)
def p48 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s20 : Slice true R T 0x3333333333333333 6 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B9.low
def p49 : Pool R T := prefixPool s20 [] (by decide +kernel)
def p50 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def p51 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def r9 : Closed T 6 := rotateClosed v9 a1 a1ok
def r10 : Closed T 6 := rotateClosed v10 a1 a1ok
def r11 : Closed T 6 := rotateClosed v8 a1 a1ok
def r12 : Closed T 6 := rotateClosed v14 a1 a1ok
def r13 : Closed T 6 := rotateClosed v12 a1 a1ok
def r14 : Closed T 6 := rotateClosed v5 a0 a0ok
def r15 : Closed T 6 := rotateClosed v11 a1 a1ok
def r16 : Closed T 6 := rotateClosed v15 a0 a0ok
def a5 : List Move := [swapRows 16]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r17 : Closed T 6 := rotateClosed v6 a5 a5ok
def v26 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w5, w8, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p48), (usePool p0), (usePool p6), (usePool p7), (usePool p15), (usePool p49), (usePool p50), (usePool p2), (usePool p3), (usePool p41), (usePool p47), (usePool p4), (usePool p51), (usePool p10)] #[r9, r10, r11, r12, r13, v3, v5, r14, r15, v13, v15, r16, v7, v6, r17] ((((((((((((((0x2084802d2300584 : Nat) <<< 64) ||| 0x200fb059410ae220) <<< 64) ||| 0x34675e2f2a884898) <<< 64) ||| 0x5d41b7203054038c) <<< 64) ||| 0xaa381eb01c603f06) <<< 64) ||| 0x8386080800766863) >>> (((h / 24 + (((((((0x30 : Nat) <<< 64) ||| 0xec600231814014) <<< 64) ||| 0x1401c2b0f144083) >>> ((h % 24) * 6)) &&& 63)) % 76) * 5)) &&& 31))) (by decide +kernel)
def v27 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w20, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p6), (usePool p0), (usePool p2), (usePool p4), (usePool p3), (usePool p42)] #[v16] ((((((((((0x130420c7 : Nat) <<< 64) ||| 0x80000400290) <<< 64) ||| 0x1a20000100100000) <<< 64) ||| 0x400018000a20c80) >>> (((h / 25 + (((((0x202500000 : Nat) <<< 64) ||| 0x291a021103001120) >>> ((h % 25) * 4)) &&& 15)) % 77) * 3)) &&& 7))) (by decide +kernel)
theorem s21 : Slice true R T 0x3300330033003300 4 :=
  slice_correct (ms := fixRows 2 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
def p52 : Pool R T := prefixPool s21 [] (by decide +kernel)
def v28 : Closed T 7 := closeState (raw := R) properPN 7 [w23, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p7), (usePool p52)] #[] ((((((0x10000010040440 : Nat) <<< 64) ||| 0x4051002044410) >>> (((h / 22 + (((0x48210404404 : Nat) >>> ((h % 22) * 2)) &&& 3)) % 65) * 2)) &&& 3))) (by decide +kernel)
def w29 := combineObserved 3 w21 w2
def v29 : Closed T 7 := closeState (raw := R) properPN 7 [w29, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p0), (usePool p10), (usePool p2), (usePool p6), (usePool p3), (usePool p4)] #[] ((((((((((0x6492b41245 : Nat) <<< 64) ||| 0x4544822da4080184) <<< 64) ||| 0x8002941108a61554) <<< 64) ||| 0x20480480304cd490) >>> (((h / 25 + (((((0x1000c000c410880 : Nat) <<< 64) ||| 0x319880c140001c00) >>> ((h % 25) * 5)) &&& 31)) % 77) * 3)) &&& 7))) (by decide +kernel)
theorem s22 : Slice true R T 0x5555555555555555 6 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B14.low
def p53 : Pool R T := prefixPool s22 [] (by decide +kernel)
def w30 := combineObserved 3 w0 w2
def v30 : Closed T 7 := closeState (raw := R) properPN 7 [w19, w30, w0, w1, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p53), (usePool p0), (usePool p6), (usePool p3)] #[] ((((((((((0x4 : Nat) <<< 64) ||| 0x28040000880) <<< 64) ||| 0x20c000200000000) <<< 64) ||| 0x14004000004) >>> (((h / 22 + (((0x3110000415e : Nat) >>> ((h % 22) * 2)) &&& 3)) % 69) * 3)) &&& 7))) (by decide +kernel)
theorem s23 : Slice true R T 0x3333000033330000 4 :=
  slice_correct (ms := fixRows 2 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p54 : Pool R T := prefixPool s23 [] (by decide +kernel)
def w31 := combineObserved 3 w0 w3
def a6 : List Move := [swapRows 66, swapRows 16]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r18 : Closed T 6 := rotateClosed v18 a6 a6ok
def r19 : Closed T 6 := rotateClosed v17 a2 a2ok
def a7 : List Move := [swapRows 67, swapRows 50, swapRows 16]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r20 : Closed T 6 := rotateClosed v17 a7 a7ok
def v31 : Closed T 7 := closeState (raw := R) properPN 7 [w19, w31, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p7), (usePool p4), (usePool p52), (usePool p3), (usePool p0), (usePool p54)] #[r18, r19, r20] ((((((((((0x11164010100 : Nat) <<< 64) ||| 0x1010515140100101) <<< 64) ||| 0x9010027010381) <<< 64) ||| 0x1100060130100251) >>> (((h / 18 + (((0x500904020 : Nat) >>> ((h % 18) * 2)) &&& 3)) % 61) * 4)) &&& 15))) (by decide +kernel)
def p55 : Pool R T := prefixPool s15 [(0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
def p56 : Pool R T := prefixPool s10 [(0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
def r21 : Closed T 6 := rotateClosed v19 a1 a1ok
def v32 : Closed T 7 := closeState (raw := R) properPN 7 [w19, w0, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p4), (usePool p3), (usePool p55), (usePool p52), (usePool p2), (usePool p7), (usePool p6), (usePool p42), (usePool p56), (usePool p0), (usePool p54)] #[v12, r18, v20, v16, r21] ((((((((((0x415611f0a016 : Nat) <<< 64) ||| 0x1850046e65895603) <<< 64) ||| 0x109c543002111135) <<< 64) ||| 0x1bd44031340700a4) >>> (((h / 20 + (((((0x1dc0088a : Nat) <<< 64) ||| 0x40008201023f1803) >>> ((h % 20) * 5)) &&& 31)) % 60) * 4)) &&& 15))) (by decide +kernel)
def r22 : Closed T 6 := rotateClosed v20 a1 a1ok
def v33 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w27, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p15), (usePool p48), (usePool p3), (usePool p2), (usePool p4), (usePool p6), (usePool p7), (usePool p37), (usePool p29)] #[r22] ((((((((((((0x5140061780141070 : Nat) <<< 64) ||| 0x9030510004644301) <<< 64) ||| 0x4004134010340000) <<< 64) ||| 0x71543244404a04) <<< 64) ||| 0x50500044440371) >>> (((h / 27 + (((((((0xd : Nat) <<< 64) ||| 0xfb61802304206134) <<< 64) ||| 0x504050042400824) >>> ((h % 27) * 5)) &&& 31)) % 80) * 4)) &&& 15))) (by decide +kernel)
def p57 : Pool R T := prefixPool s7 [] (by decide +kernel)
def p58 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000), (1, 0xcccccccccccccccc, 0xf000f000f000f000)] (by decide +kernel)
def p59 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000)] (by decide +kernel)
def v34 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w8, w2, w27, w3, w4]
  (fun h => chooseRoute #[(usePool p48), (usePool p2), (usePool p0), (usePool p3), (joinPools p57 p58), (usePool p37), (usePool p6), (usePool p4), (usePool p7), (usePool p59)] #[v21, v7, r17] ((((((((((0x123011 : Nat) <<< 64) ||| 0x210116711b010c12) <<< 64) ||| 0x1a13171100114621) <<< 64) ||| 0x1191011030800005) >>> (((h / 18 + (((((0x18000204000 : Nat) <<< 64) ||| 0x1000001121140003) >>> ((h % 18) * 6)) &&& 63)) % 54) * 4)) &&& 15))) (by decide +kernel)
def p60 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf000f000f000f000, 0xffff0000ffff0000)] (by decide +kernel)
def p61 : Pool R T := prefixPool s8 [(0, 0xf000f000f000f000, 0xffff0000ffff0000), (1, 0xaaaaaaaaaaaaaaaa, 0xf0000000f0000000)] (by decide +kernel)
def p62 : Pool R T := prefixPool s8 [(0, 0xf000f000f000f000, 0xffff0000ffff0000), (1, 0xcccccccccccccccc, 0xf0000000f0000000)] (by decide +kernel)
def v35 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w17, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p26), (usePool p60), (usePool p2), (joinPools p57 p61), (usePool p15), (usePool p53), (usePool p7), (usePool p3), (joinPools p57 p62), (usePool p49), (usePool p6)] #[v13] ((((((((((((0x22277202 : Nat) <<< 64) ||| 0x2082272222270222) <<< 64) ||| 0x9322022222022227) <<< 64) ||| 0x5000220200462722) <<< 64) ||| 0x2a0262272212272b) >>> (((h / 25 + (((((0x20346032a : Nat) <<< 64) ||| 0x1c01121003101201) >>> ((h % 25) * 4)) &&& 15)) % 73) * 4)) &&& 15))) (by decide +kernel)
def p63 : Pool R T := prefixPool s12 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (3, 0xff000000ff000000, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def p64 : Pool R T := prefixPool s10 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00)] (by decide +kernel)
def v36 : Closed T 7 := closeState (raw := R) properPN 7 [w18, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p3), (usePool p15), (usePool p6), (usePool p2), (usePool p0), (usePool p4), (usePool p42), (usePool p32), (usePool p63), (usePool p64)] #[v14] ((((((((((((0x1710850444410141 : Nat) <<< 64) ||| 0x4b8111100111a403) <<< 64) ||| 0x4470a61400144409) <<< 64) ||| 0x1440047317170141) <<< 64) ||| 0x712106010141044) >>> (((h / 27 + (((((((0x22 : Nat) <<< 64) ||| 0xac03c61200200000) <<< 64) ||| 0x9004010300400000) >>> ((h % 27) * 5)) &&& 31)) % 80) * 4)) &&& 15))) (by decide +kernel)
def p65 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000)] (by decide +kernel)
theorem s24 : Slice true R T 0xff00ff00ff00ff00 6 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B20.low
def p66 : Pool R T := prefixPool s24 [] (by decide +kernel)
def v37 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w8, w9, w3, w4]
  (fun h => chooseRoute #[(usePool p34), (usePool p65), (usePool p2), (usePool p3), (usePool p40), (usePool p66)] #[v15, v22] ((((((((((0x70c0480 : Nat) <<< 64) ||| 0x4924d04820904132) <<< 64) ||| 0xe840080249349269) <<< 64) ||| 0x84c2584693083490) >>> (((h / 24 + (((((0x24 : Nat) <<< 64) ||| 0x2101001109440) >>> ((h % 24) * 3)) &&& 7)) % 73) * 3)) &&& 7))) (by decide +kernel)
def p67 : Pool R T := prefixPool s1 [] (by decide +kernel)
def p68 : Pool R T := prefixPool s14 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def r23 : Closed T 7 := rotateClosed v25 a0 a0ok
def r24 : Closed T 7 := rotateClosed v25 a1 a1ok
def r25 : Closed T 7 := rotateClosed v24 a0 a0ok
def r26 : Closed T 7 := rotateClosed v24 a1 a1ok
def r27 : Closed T 7 := rotateClosed v23 a0 a0ok
def r28 : Closed T 7 := rotateClosed v23 a1 a1ok
def r29 : Closed T 7 := rotateClosed v26 a1 a1ok
def r30 : Closed T 7 := rotateClosed v26 a2 a2ok
def v38 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p67), (usePool p53), (usePool p49), (usePool p7), (usePool p15), (usePool p41), (usePool p47), (usePool p66), (usePool p51), (usePool p40), (usePool p68)] #[v25, r23, r24, v24, r25, r26, v23, r27, r28, v26, r29, r30] ((((((((((((((0xc20d08208076a815 : Nat) <<< 64) ||| 0x1248300c63298802) <<< 64) ||| 0x184e0286018c8358) <<< 64) ||| 0x92f88cc002a0010c) <<< 64) ||| 0xb250c33182d40004) <<< 64) ||| 0x140c030006000c02) >>> (((h / 24 + (((((0x3300013 : Nat) <<< 64) ||| 0x57110b1004815580) >>> ((h % 24) * 4)) &&& 15)) % 78) * 5)) &&& 31))) (by decide +kernel)
def p69 : Pool R T := prefixPool s10 [] (by decide +kernel)
def r31 : Closed T 7 := rotateClosed v28 a2 a2ok
def r32 : Closed T 7 := rotateClosed v31 a2 a2ok
def r33 : Closed T 7 := rotateClosed v29 a6 a6ok
def r34 : Closed T 7 := rotateClosed v29 a7 a7ok
def v39 : Closed T 8 := closeState (raw := R) properPN 8 [w19, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p53), (usePool p7), (usePool p41), (usePool p49), (usePool p6), (usePool p66), (usePool p40), (usePool p69), (usePool p3), (usePool p42)] #[v25, v28, r31, v30, v31, r32, v32, r33, r34, v27] ((((((((((((((0x10840109180 : Nat) <<< 64) ||| 0x2040101421698739) <<< 64) ||| 0x8222048e010c80a) <<< 64) ||| 0xd2410c0100488410) <<< 64) ||| 0x450100080682840) <<< 64) ||| 0x386080bc910a029) >>> (((h / 24 + (((((0x610113f4 : Nat) <<< 64) ||| 0x62746000219a0e0) >>> ((h % 24) * 4)) &&& 15)) % 73) * 5)) &&& 31))) (by decide +kernel)
def p70 : Pool R T := prefixPool s8 [] (by decide +kernel)
def r35 : Closed T 7 := rotateClosed v36 a1 a1ok
def r36 : Closed T 7 := rotateClosed v28 a5 a5ok
def r37 : Closed T 7 := rotateClosed v32 a1 a1ok
def r38 : Closed T 7 := rotateClosed v32 a6 a6ok
def r39 : Closed T 7 := rotateClosed v37 a0 a0ok
def r40 : Closed T 7 := rotateClosed v34 a5 a5ok
def r41 : Closed T 7 := rotateClosed v33 a5 a5ok
def v40 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w8, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p48), (usePool p50), (usePool p53), (usePool p2), (usePool p3), (usePool p41), (usePool p49), (usePool p66), (usePool p40), (usePool p69), (usePool p42), (usePool p70)] #[r35, v28, r36, r37, r38, v26, v35, v37, r39, v34, r40, v33, r41] ((((((((((((((((0x2201810 : Nat) <<< 64) ||| 0x318ca0a80000486c) <<< 64) ||| 0x1ac170900508ce72) <<< 64) ||| 0xdc4a186418c0001) <<< 64) ||| 0x5006c3300631b4) <<< 64) ||| 0x841155321f09120a) <<< 64) ||| 0x381469014841806f) >>> (((h / 25 + (((((0xd379b00e1 : Nat) <<< 64) ||| 0x2d8c900020104022) >>> ((h % 25) * 4)) &&& 15)) % 82) * 5)) &&& 31))) (by decide +kernel)
def p71 : Pool R T := prefixPool s12 [] (by decide +kernel)
def p72 : Pool R T := prefixPool s14 [] (by decide +kernel)
def r42 : Closed T 8 := rotateClosed v39 a5 a5ok
def r43 : Closed T 8 := rotateClosed v39 a0 a0ok
def a8 : List Move := [swapRows 50, swapRows 16]
theorem a8ok : autoOK T a8 = true := by decide +kernel
def r44 : Closed T 8 := rotateClosed v39 a8 a8ok
def r45 : Closed T 8 := rotateClosed v39 a1 a1ok
def r46 : Closed T 8 := rotateClosed v39 a6 a6ok
def r47 : Closed T 8 := rotateClosed v40 a1 a1ok
def r48 : Closed T 8 := rotateClosed v40 a2 a2ok
def v41 : Closed T 9 := closeState (raw := R) properPN 9 [w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p67), (usePool p71), (usePool p69), (usePool p70), (usePool p72)] #[v39, r42, r43, r44, r45, r46, v38, v40, r47, r48] ((((((((0x4710d23a3 : Nat) <<< 64) ||| 0x4010e01500403000) <<< 64) ||| 0x600401824b92c300) >>> (((h / 14 + (((((0x6 : Nat) <<< 64) ||| 0x180c211ce12cc05) >>> ((h % 14) * 5)) &&& 31)) % 41) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 10 :=
  fromClosed v41 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 9, 13), (0xff00ff00ff00ff00, 5, 13), (0xffff0000ffff0000, 5, 21)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B30
end PEqualNP.Outside.L_meta_49153.Atlas


namespace PEqualNP.Outside.L_meta_49153

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 6) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 6) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 6) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 6) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

inductive Prog : Set F → F → ℕ → Prop where
  | done {s f} (h : Av s f) : Prog s f 0
  | gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k + 1)

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

theorem restrict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p with
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

theorem strict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 6} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 6} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p with
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

def stock : Set F := Set.range fun (i : Fin 6) (x : X) => x i

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
    (List.ofFn fun (i : Fin 6) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 6) (x : X) => x i)) o = f := by
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

def sixTarget : F := fun x : Fin 6 → Bool => Nat.testBit (3941132416 * 2 ^ 32 + 3900735616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

namespace Evidence
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def limbs64 (ws : List Nat) : Nat := ws.foldl (fun v w => (v <<< 64) + w) 0
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

def inputs : List Sig := [(BitVec.ofNat _ (limbs64 [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),(BitVec.ofNat _ (limbs64 [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),(BitVec.ofNat _ (limbs64 [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),(BitVec.ofNat _ (limbs64 [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),(BitVec.ofNat _ (limbs64 [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),(BitVec.ofNat _ (limbs64 [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0x0,0x0]))]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
def varsX (m : Nat) : List Sig := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else if (m >>> 9).testBit j then one else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 0 &&& x 2 &&& x 4) ||| (x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 0 &&& x 1 &&& x 5) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5)
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
  | 0 => (limbs64 [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1])
  | 1 => (limbs64 [0x1,0x0,0x1,0x0,0x1,0x0,0x1])
  | 2 => (limbs64 [0x1,0x1,0x0,0x0,0x1,0x1])
  | 3 => (limbs64 [0x1,0x0,0x0,0x0,0x1])
  | 4 => (limbs64 [0x1,0x1,0x1,0x1])
  | 5 => (limbs64 [0x1,0x0,0x1])
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
    let r := (hints >>> (6*i)) &&& 63
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

def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior

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

abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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
  let x := fun j => if m.testBit j then v j else if (m >>> 9).testBit j then BitVec.allOnes 1024 else 0
 (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 0 &&& x 2 &&& x 4) ||| (x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 0 &&& x 1 &&& x 5) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else if (m >>> 9).testBit j.val then BitVec.allOnes 1024 else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · by_cases pin : (m >>> 9).testBit j.val = true
    · simp only [vertex,if_neg hh,if_pos pin,bit_one,BitVec.getLsbD_allOnes,decide_eq_true i.isLt]
    · simp [vertex,hh,pin,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else if (m >>> 9).testBit j then BitVec.allOnes 1024 else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2

def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,_,_,l,base) := s
  let ms := fixRows ((m &&& 63) ^^^ ((m &&& 63) &&& (q ||| o))) o
  earlier.contains (q,base) && (l == base) && properB (graphGoal q) &&
    checkMap ms (vars m) (graphGoal m) (vars q) (graphGoal q) &&
    (movedWord ms (subcube z o) == one)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  rcases s with ⟨z,o,q,sp,hi,l,base⟩
  simp only [certifiesSlice,Bool.and_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨earlier,rfl⟩,pr⟩,mapped⟩,all⟩ := ok
  exact slice_correct mapped all (proper_of _ pr) (prior _ earlier)

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot
def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP556 : Nat → Bits
  | 2 => ~~~(0x1052 : Bits)
  | 3 => 0xdef6
  | 5 => ~~~(0x40a4 : Bits)
  | _ => 0

def samplesQ556 : Nat → Bits
  | 2 => ~~~(0xedfa : Bits)
  | 3 => 0x2422
  | 5 => 0x4818
  | _ => 0

def compactPerms556 : Array (List Nat) := ([[], [83], [50], [50, 83], [82, 83], [82]] : List (List Nat)).toArray

def compactDomains556 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords556 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount556 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath556 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive556 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords556 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs556 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords556 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords556 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket556 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP558 : Nat → Bits
  | 1 => 0x6fecd577d56d1a
  | 2 => ~~~(0x408a5c611599c : Bits)
  | 3 => 0x77fba4be78dba4
  | 5 => ~~~(0x2023d43040ef22 : Bits)
  | _ => 0

def samplesQ558 : Nat → Bits
  | 1 => 0x12022825000c10
  | 2 => ~~~(0x7bbffb3fb3ffdc : Bits)
  | 3 => 0x8801310300304
  | 5 => 0x2101c00a8000c8
  | _ => 0

def compactPerms558 : Array (List Nat) := ([[], [83], [50], [50, 83], [82, 83], [82], [33], [33, 83], [33, 50], [33, 50, 83], [33, 82, 83], [33, 82], [49, 50], [49, 50, 83], [49], [49, 83], [49, 82], [49, 82, 83], [81, 82, 83], [81, 82], [81, 83], [81], [81, 50, 83], [81, 50]] : List (List Nat)).toArray

def compactDomains558 : Array (Sig × Nat) := ([(subcube 2 0, 4), (subcube 4 0, 4), (subcube 8 0, 4), (subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords558 : Nat → Nat
  | 0 => (limbs64 [0x90b,0x73affe07f81fe042,0xa8bd613dd813075f,0x8477f806027c4721,0x1728d20900500900,0x78977f80536b7a7a,0xa4bff80ff013b05c,0xcb341f0e6479112a,0x314a6ff002ebffc0,0x76b4ff01fe012d57,0x1b84b4a44ea8d3f7,0xad6d49fe00c5628a,0xb9e7c763b9601814,0x578e76ec10200401,0x4009149febef402,0xc82482401ff07f83,0x72f28fff07f81ecf,0x833ff06eb73abfe0,0xff03070fd0060e4f])
  | _ => 0

def compactCount558 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 3
  | 3 => 2
  | _ => 0

def compactPath558 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords558 (18 + 12*i) 12
  | 4 => let v := readCompactBits compactWords558 (232 + 12*i) 12
    (readCompactBits compactWords558 (220 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 3 => let v := readCompactBits compactWords558 (942 + 13*i) 13
    (readCompactBits compactWords558 (894 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive558 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords558 (0 + 4*i) 4
  | 5 => readCompactBits compactWords558 (30 + 5*i) 5
  | 4 => readCompactBits compactWords558 (268 + 6*i) 6
  | 3 => readCompactBits compactWords558 (968 + 7*i) 7
  | _ => 0

def compactPoolIDs558 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords558 (12 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords558 (4 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits compactWords558 (43 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords558 (35 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords558 (292 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords558 (286 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 3 => let v := readCompactBits compactWords558 (986 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords558 (982 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket558 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords558 (49 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 13)
    let v := readCompactBits compactWords558 (51 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords558 (304 + 5*(i % 10)) 5
    let off := ((i/10 + d) % 36)
    let v := readCompactBits compactWords558 (354 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits compactWords558 (994 + 1*(i % 3)) 1
    let off := ((i/3 + d) % 12)
    let v := readCompactBits compactWords558 (997 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP43 : Nat → Bits
  | 0 => 0x6feffe3fe3fff4
  | 1 => ~~~(0x402e000c08144 : Bits)
  | 3 => ~~~(0x20001e00203230 : Bits)
  | 5 => ~~~(0x82d0000034c80 : Bits)
  | _ => 0

def samplesQ43 : Nat → Bits
  | 0 => 0x121122c76044f4
  | 1 => 0x52268b4122e2a
  | 3 => ~~~(0x5fabb1e67af678 : Bits)
  | 5 => ~~~(0x7758fb95f76ca6 : Bits)
  | _ => 0

def compactPerms43 : Array (List Nat) := ([[], [83], [49], [49, 83], [81, 83], [81], [16], [16, 83], [16, 49], [16, 49, 83], [16, 81, 83], [16, 81], [48, 49], [48, 49, 83], [48], [48, 83], [48, 81], [48, 81, 83], [80, 81, 83], [80, 81], [80, 83], [80], [80, 49, 83], [80, 49]] : List (List Nat)).toArray

def compactDomains43 : Array (Sig × Nat) := ([(subcube 0 1, 4), (subcube 0 2, 4), (subcube 0 8, 4), (subcube 0 32, 4)] : List (Sig × Nat)).toArray

def compactWords43 : Nat → Nat
  | 0 => (limbs64 [0xea950,0x77f80ef37f81717f,0xf81fe076d9fe068d,0xdfe061ac44bc1013,0xe23808b146104002,0x40033a7ffc0612,0xa6b2948fa7877f80,0xe35dfe00eda71ba0,0x683fe015a3941614,0x719c7951ae4ad6e8,0xc249ffc00f44ff00,0xaa927160ab2ff00d,0x95e4be3c0c15f18,0x9bfc0432bff0076e,0xc003d0800424527f,0xafbc00a208208007,0xfc02adff07b9cee7,0xfe04f7ff81caffe0,0x23a9070fc0060e4f])
  | _ => 0

def compactCount43 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 3
  | 3 => 2
  | _ => 0

def compactPath43 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords43 (18 + 12*i) 12
  | 4 => let v := readCompactBits compactWords43 (206 + 12*i) 12
    (readCompactBits compactWords43 (194 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 3 => let v := readCompactBits compactWords43 (921 + 13*i) 13
    (readCompactBits compactWords43 (873 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive43 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords43 (0 + 4*i) 4
  | 5 => readCompactBits compactWords43 (30 + 5*i) 5
  | 4 => readCompactBits compactWords43 (242 + 6*i) 6
  | 3 => readCompactBits compactWords43 (947 + 7*i) 7
  | _ => 0

def compactPoolIDs43 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords43 (12 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords43 (4 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits compactWords43 (43 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords43 (35 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords43 (266 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords43 (260 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 3 => let v := readCompactBits compactWords43 (965 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords43 (961 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket43 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords43 (49 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 11)
    let v := readCompactBits compactWords43 (51 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords43 (278 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 37)
    let v := readCompactBits compactWords43 (318 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits compactWords43 (973 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 14)
    let v := readCompactBits compactWords43 (979 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP1069 : Nat → Bits
  | 0 => ~~~(0x10021b02c15183c : Bits)
  | 2 => 0xdbeb09e7ef32d94
  | 3 => ~~~(0x440969c5053a3d4 : Bits)
  | 5 => 0xf7df7b3fd559a7c
  | _ => 0

def samplesQ1069 : Nat → Bits
  | 0 => ~~~(0xedffeef3f7ffebe : Bits)
  | 2 => 0x2505a2214256c84
  | 3 => 0x44454870a056c0a
  | 5 => 0x88004821400230
  | _ => 0

def compactPerms1069 : Array (List Nat) := ([[], [50], [80], [80, 50]] : List (List Nat)).toArray

def compactDomains1069 : Array (Sig × Nat) := ([(subcube 4 0, 4)] : List (Sig × Nat)).toArray

def compactWords1069 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount1069 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath1069 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive1069 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords1069 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs1069 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords1069 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords1069 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket1069 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP2091 : Nat → Bits
  | 0 => ~~~(0x1000106070380318 : Bits)
  | 1 => 0x7afcf87cfdf8cb5c
  | 3 => ~~~(0x2300ee7080f8f0fc : Bits)
  | 5 => 0x75f3f66ff2f837b8
  | _ => 0

def samplesQ2091 : Nat → Bits
  | 0 => ~~~(0x6f7fffde7effff9e : Bits)
  | 1 => 0x541450848924a14
  | 3 => 0x23156a4e141b5f02
  | 5 => 0xa24209422491588
  | _ => 0

def compactPerms2091 : Array (List Nat) := ([[], [81]] : List (List Nat)).toArray

def compactDomains2091 : Array (Sig × Nat) := ([(subcube 8 0, 4)] : List (Sig × Nat)).toArray

def compactWords2091 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount2091 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath2091 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive2091 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords2091 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs2091 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords2091 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords2091 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket2091 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP45 : Nat → Bits
  | 0 => ~~~(0x0 : Bits)
  | 2 => ~~~(0x2009a03840a2 : Bits)
  | 3 => 0xbff9aff8eef6
  | 5 => ~~~(0x10f00000ac54 : Bits)
  | _ => 0

def samplesQ45 : Nat → Bits
  | 0 => 0x8206554216e
  | 2 => ~~~(0xdbee4d34f0ea : Bits)
  | 3 => 0x4142d9a986d2
  | 5 => ~~~(0xed8cf1f6a956 : Bits)
  | _ => 0

def compactPerms45 : Array (List Nat) := ([[], [83], [50], [50, 83], [82, 83], [82]] : List (List Nat)).toArray

def compactDomains45 : Array (Sig × Nat) := ([(subcube 0 1, 4)] : List (Sig × Nat)).toArray

def compactWords45 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount45 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath45 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive45 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords45 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs45 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords45 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords45 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket45 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP47 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xed7fef7ffd9fff9,0x3ffffe75fff0f7df,0xbdffffd83dfffbf3,0x3fe6263ff99fffb4]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x43802644002718,0x1400b000810071c3,0x99a1499800222112,0x14c6021bc882ae30])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0xdf2bfff7c6f311a,0x6fffb3ff9f83f0cf,0xc6e0d889fbe67f7f,0xcb4787cbcfe19e1c]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x4324000384839e2,0x6c0002700c13800e,0x46fcdec9c0801861,0xb6785c230e5159c])) : Bits)
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x9480d10001d019,0x2800000512a0f6dd,0xa442b00009444200,0x2b00262dc119da04])) : Bits)
  | _ => 0

def samplesQ47 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x128031840560004,0x4065c200101308d0,0x700e0d601079b83,0xc60000c0089e7a4]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x43902256050350,0x17501924482aa187,0x29084c04add11448,0xa1113480a55d114a]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x20d60090798d7e0,0x801b3c72029c0021,0xe2433f1832406273,0xe38619c1cfe01a14]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0xbcdbabde737849d,0xf679e3c6fe3fc5db,0xb7d16e3705c3be63,0xce7da51f30ed37dc])) : Bits)
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0xf6b778ef6fcafd6,0xdd57fb6f5b5a6cad,0x7b9afdfdab5553db,0xbf7577ada5d9db26])) : Bits)
  | _ => 0

def compactPerms47 : Array (List Nat) := ([[], [50], [81], [81, 50]] : List (List Nat)).toArray

def compactDomains47 : Array (Sig × Nat) := ([(subcube 0 1, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 0 2, 5), (subcube 0 4, 5), (subcube 0 8, 5), (subcube 0 32, 5), (subcube 2 0, 5), (subcube 32 0, 5), (subcube 2 1, 4), (subcube 4 1, 4), (subcube 4 2, 4), (subcube 4 8, 4), (subcube 4 32, 4), (subcube 8 2, 4), (subcube 8 4, 4), (subcube 8 32, 4), (subcube 32 1, 4)] : List (Sig × Nat)).toArray

def word47_0 : Nat → Nat
  | 0 => (limbs64 [0x74642c602438b1c3,0xf81f746652538b4,0xc3907477e110241c,0x2141138dcd907e14,0xdd3187442141103e,0x7dc0908e372144c,0x9074471421010f8,0x437340906144081e,0x372241c538135109,0x30041d42e4351994,0x38390728818214fe,0x13907e000515241d,0x318814204f1cbe00,0x11391408e2c01f7e,0x3ffbefdfbf7effd,0xff7ffefdbfefdffb,0x7fffffffefffbffe,0xfffbf7efdfbf7fff,0xffffffdfbf7ffdff,0x77effbff7ffffffe,0xffffbf7fddfbffff,0xfdfb7efdfff7efff,0xffffefffb7ffdfff,0x7efffff7ffdffcb8,0x48b848b148a944a9,0x42b1407944794261,0x4061402848284828,0x4829442944314231,0x4231409048884880,0x4899429942814281,0x428140814110c911,0x4909490149194709,0x47114050c848c858,0x4840485948594851,0x4849484148414848,0x8659464946594441,0x404140f048e848e0,0x48e886f846e846f9,0x46e946f844f142e9,0x42d088c888d048c0,0x48d948d148c948c8,0x86d944c944108808,0x8810481048084800,0x4819481148114809,0x4809480148088608,0x4419440944094411,0x4184580580304888,0x6848844048003fe0,0x7f81fe07f819c796,0xb7be8ff81202b626,0xda67f80103e79a39,0x19c940e0ee429486,0x1de693b168a1ff8,0x1fe0432f66f88418,0x153dc6349d5141a,0x726c35c330070961,0x527288e0d709610,0x1a9390e220a408a4,0xe4700644108145c9,0x2123840a48611508,0x50441a4c6900834,0x99c1ffffffffffff,0xfc12212012221e11,0x211601600800e49f])
  | 1 => (limbs64 [0xcbe090c74b808504,0x4037d911d12003f8,0xd842c71421010063,0xb82f7d8324e1422f,0x81010370d148034f,0xe362c45022f84431,0x87009e14dd344e2c,0x348738b142101251,0x6e370d2e379949,0x5338b4470cbe091c,0x338b478dc70f6e01,0x5074d14481420013,0xf81cb4f610214110,0xe37d8d247480378,0xd911f8142101240d,0xc745240505234620,0x29045660cb0814a4,0x12634b40b1410e44,0x8808e12694734d0b,0x648716610b206040,0xb69660c33764850,0x6694b10818004297,0x69891c036614b944,0x4811880c70259844,0x881d29054042cf30,0x214303804bd91948,0x4381420c004b1f69,0x46085007d9110818,0x536244007d8b14f,0x206005081e072d29,0x4422449740530e91,0x238d201912949383,0x1d292524e1cd0764,0x880ce10d0851c005,0xe03da51821400f6,0x444142006e0ed831,0x1194d92e2538d10,0xe0851c00c1e36465,0x210047d823941009,0x7638518803650310,0xb502381e091090c1,0xde143a51120462,0x5080e090e511250,0xc9a40d110a2cc526,0x90a3442cb50c3660,0xe56441ca45044e24,0xa411495004d44b,0x199041ce3d0351a,0x23e429410b2061c,0x35241062000c70a5,0x16451104b64300f9,0x42060850780251e,0x4188142078380964,0xe63140241110cd2,0xc698c5044642432d,0x1e002e40f7e09442,0x1411382c6de40ce0,0x852c1107e03dc022,0x434e1422c4047e03,0xdc09063420511142,0x640e72c81840853b,0x84e40c500f0812f8,0xc49135133262c41,0xcd44132651318010])
  | 2 => (limbs64 [0x86176bc46e13aab0,0xba97482c635a43ef,0xfafaeff8033d0b76,0x83a68f8184ce13df,0xe005a621f1b83c1a,0xc0a3ff003c9c7fc0,0x44be672dbd38e85,0x1d20da0728d7bc24,0x3fe00ff002924b,0xdedfe001c92ff80,0x3906ed954b70bff8,0x1931fe00cbabe2,0xb621011fe00ff004,0xe81422435889a195,0x5ad0f304e6406c02,0xe7ad2debfc8a2c7,0x61a6305c5e79648a,0x98197bae4515fe00,0xff002380cd1cfd2a,0x5a87dff80131be3e,0xb608447f8035da3f,0xe00b36cff80201ad,0xfe00ff001eb17a0d,0xbfe00ff00528d689,0xee52339a14ea1d39,0xd9e60657a29ff802,0x4809a8c70957979d,0xe6da6ca1d7b30c7a,0xcde42a440e382695,0x45dd5a058b76d794,0xe374f6954113b364,0xb9ce5e6afa23097,0x54d29bcd09eec9a0,0x600d25c560a5ab89,0x770a6bb10535993b,0x1523899ebfc0196b,0xa179fe78f5a2a208,0xe081d05180015104,0x20c11f3010000080,0x2b4601501836014,0x15e2860820c4003,0x4c40090040013030,0x910604218a00210,0x10403440160878d0,0x573cbcc6329dc737,0xf7c21b02dbd7ee6,0xbb6d6d68b39ac8da,0xeeeb07aa6e9eea42,0x288f9e6670999ea5,0xda94e24ba906a37b,0x8b32207865e12683,0x320087e11f497add,0xe48772dd1772a5c1,0xa6df1ab868d59e76,0x5e18fb61317895be,0x167c56e552d516d3,0xa74ce9299482916b,0x42e901a3dd8f143b,0x68e3d35b8c8b2f68,0xb3b2a249fc24dc8c,0x521e87d61de46e71,0x9ec5c914f44690f7,0x430909e41e805b40,0x9900244b638b4431])
  | 3 => (limbs64 [0x8a8662a198a8062b,0x698ada62c68891a6,0x146888c42230888c,0x6613004832611888,0x8641218048645218,0x1486662189886660,0x9998260609818060,0x601998a66629998a,0x6062911484662288,0x88a41229148a2522,0x9988a26228886a25,0x1a9986a261e52600,0xe52211651e01650a,0x21e12211452000c5,0xe01450812450611,0x432211422600c220,0xc12221c12000a5,0x2611252211252000,0xa51e01251a112510,0x12251000a50c1223,0x2211222600a22000,0xa21e01221e00a21a,0x11221800a12221a1,0x2012211e01211000,0x852211052000850a,0x2185022185021205,0x211012601012221,0xf70c7fc00190fff0,0x7f8018d39449fff,0x5d8b734ed405f7,0x4362555b9016a919,0x5f22f398df45e874,0xb376e2ccbe0cb2d2,0x70292578bba3d268,0x68ff006537bfc01,0xfe0005218392dd54,0xe8699181dff80328,0xeb8355ff0059d4d3,0x47ffe00ff0030a75,0x8c14cabfff006048,0xe7e6ffe00ff001ba,0x3f4cdfe2128d86ec,0xb828872ea1b9e80b,0x54cea04a46c6ff00,0x29d1408565b5b2d5,0x4cca90fe56565793,0x391ab8bfc013c425,0x2066084490fcc878,0xbc506e49cb0939eb,0x52c6ba607e9dcbcc,0x440127cac2f55df8,0x66bff0047827fc01,0x66077b234746c2a9,0xf0d47b2207921a9c,0xfe3a7bc507ce2ad6,0x431f4db0566e956,0x39729c6986661028,0x758cffe00086daf8,0x43a19b20794476c9,0x32d6917444eff001,0x41ffc00144c7e4d,0xf2aeffc019cca2d5,0x92fab49d0fc963d9,0x67309ab5d2dc2ae2])
  | 4 => (limbs64 [0x3820d002e2d81ae0,0x2b61201822e02800,0x22e2d92028182020,0x18083812e2d808,0x30401022e003606a,0xe008105020403050,0x38083ad842d80898,0x20383089200ad820,0x98300ad83898a000,0x19c008a038282098,0x1009c0a0280810a1,0xc088001cfefefcfc,0x7f6d6f6d6e6f6efd,0xfcfd6dfdfdfcfdfd,0xfcff6fddfdfefcfe,0xffeefdfdfeecffef,0xeefefdfdfdfeeefe,0xfdfefefefefefefe,0xfcfefdfcfcfdfcfc,0xbcfcf5ff9dcc7c7c,0xfcf6fefdfefefefe,0xfefefedefeff6df7,0xdfdfdf9efefefefe,0xfefefefdfdffeefe,0x6fdfeefdfdffeefd,0xfdfdffedefeff5f5,0xfefcfefcfdef7dfe,0x7f7f7dfe6cdfdfef,0xeefefdfdffedefef,0xf5f5fefcfefefdff,0xdfeefefdfdffdefd,0xfdfa61801e610698,0x456629598a506014,0x18056629598a5662,0xaa848aa51ab986a8,0x6042988e46239180,0xe462b918a5860161,0x8a58628084802610,0x118004628118a046,0x28098b28124b9492,0xc624b18128124b18,0x2c120a0482e520a,0x1482c620a1882c60,0xb04826508814224,0x6089048221208048,0x2660891822260881,0x82d060410c8fc602,0x418b2462cf1813c6,0x33986c860321803,0xc601a8c86860ad98,0x8b0622c180b06005,0x9481052051881432,0x48c816620518812,0x6204188122185986,0x1261828480c601f0,0x487a121e0484a21c,0xd04932124c048bc1,0x22e848b812450c91,0x2323c9868e61a218,0x28e62d004872221c,0x4874521d9887262,0x1c1827662ba986ea,0x62a19868660a1982,0x8060a01808060219])
  | 5 => (limbs64 [0x4a51302820385843,0x7028185823709008,0x13702820900018a9,0xb033704838581800,0x3ad0937129303858,0x18282092d37028,0x3ad0002090403130,0x2928203890184030,0x3890183040189038,0x1838389020182818,0x3820903819293278,0x281008183b683058,0x4828282088806838,0xb687028107048,0x8203819b0900040,0x80281008183b6830,0x3368182c00702810,0x301801b020340073,0x6818900031b150a1,0x3a480a60bae04820,0x3ae3681832e36818,0x403042e01801b022,0xe36818300042d090,0x40680032d09042d0,0x90200041c0902880,0x4030109028304040,0x90203031c0184020,0x9041c0304929280a,0x70481259c2d021c0,0x2870102811c37088,0x58c838880b68a0b8,0x48525020a0b93a50,0x20d0a0b8225050c8,0x806a58a360504928,0x8b940a029283818,0x2018204030192038,0x2128287818182879,0x2078283828803820,0x2858384828193028,0x48181820185c0018,0x888a6a50a13858d2,0xe048183ad8102808,0x1848204030481820,0x481ae0281822e008,0x1019384068782838,0x2248202838803360,0x38203870003372d8,0x1833612018203088,0x2371208832d818,0x2020001ad8203808,0x3ad8281023600800,0x4130602009202810,0x182008003b612360,0x3801b83039b83800,0x98085821b8083b60,0x404039b840983808,0x9821b86c03603038,0x4400382361508a52,0x687020a2e2403818,0x68d2e241203ad810,0x28083a40204042d8,0x10280a40203a502a,0x482018303832502a,0x481800203ae02b60])
  | 6 => (limbs64 [0x7899c1e6b595b64b,0x38e2e2ef882618f8,0x2ae00f7cade91762,0xdcf56ec5aa968bd9,0x4f61b57b559a55eb,0x553d4694fa536b4b,0x2524b469d14f41cc,0xf493b3cde935accc,0xf2fd4aad27a49712,0x1ac7cb1cdc5cf13c,0xc3cb0cac28509241,0xcb04a40b0fe9bf48,0xfb33e08f643c90ee,0x23b12e7ab948e33b,0x7e8dda36e8d9bb58,0x6d4ab48ccf2b32ac,0xa2b1e4c6a312cc1a,0xafd2baa2e26b71ad,0x6ab332c0aadbaa96,0xa4b2864a0b27689b,0x9a688981a5a8949a,0x4c891124028fa236,0xa8b32210841a0a68,0x121fca7ca9e8279a,0x9dc87539c6a6f21b,0x4e6999a08664188a,0x5fc96c859195ee54,0x2946450a13a84ca9,0x28a47b91084230fd,0x3b40dce33c0bea2,0xd28aac27a096c229,0x88481f486a818985,0xc615905221428470,0xda82c609a01ee04,0x28066000883831b0,0x4002813f8200819,0xb82058082009bc00,0x30281020083bf818,0x881874005bf84c01,0xc3f9b870588819b0,0x1c03f889b401c1bb,0xf870588c001bf888,0x7400385bfbf01ae0,0x38588ad828209810,0x9c0a0280810a1c0,0x403c0028100ad820,0x5c00883818583043,0x6810280818203b68,0x2810081848882008,0x181373703800a858,0x1823701028092368,0x236808101b70a808,0x3800685b68a81823,0x73603b7058437009,0x303b682810083888,0x2008381370303820,0x181b700020383039,0x20185b7028382030,0x3818436810280838,0x236810280821b090,0x38337368183043,0x701368081b702818,0x206b70281820302a,0x4822505838406b72])
  | 7 => (limbs64 [0xd7f8010e2cff8010,0xc8cada926861040a,0x72058299e63825b6,0x943fe00738bf7e1e,0x9100d0236ff801ce,0x51124637eb83803e,0xceafed1b7fe003cb,0xe698cd2f95fbcbbb,0x8279fe007f801fe0,0x7f801fe004d8cff,0xe007f801c2c1e92a,0xf4252a2245dc45f0,0x45feef7c9c843b0b,0xff8015c5d421c6f7,0x29b199b5ce4ff801,0x34cf132c34c09274,0x1f76a80d2e5fe000,0x3aa5fe0058345dcf,0x59b932c69dd71fbf,0xe007f8008264ff80,0x1fe004817eeec351,0x1522c46541c18537,0x7f801fe006cce7fe,0x358633ec43ec47,0xb04fe5a71cc77252,0x918683618f6b05cb,0x8e5f457608de8aa,0x89b82ec4d3c59360,0xef8bd113fe00373e,0xe6242c932e7f35f2,0x159b8c11298252a1,0x189f84f0d474dfc6,0xc75c07aa248ea7b,0x6c0899b866b05be8,0x5cf44d023ce3e364,0x91f168b6909a65ae,0xbfa9ebace8df87eb,0xa253b52af199c3b,0xe42a6429e34098bd,0xae32e51f7aff00ce,0x923c312ae9c16e36,0xec94165d40f5cb57,0xbecb3e26f10521d3,0xf0261df14c5e10f,0xf800063bff80014c,0x95380a6ca04bb5b8,0x6b1c133f1e479232,0x75020f71bbdf13e6,0x497868bff801fe00,0xd0000292a82862f,0x808981160068804,0x801910140931e38,0x480851d060400,0x60a00f87a0154910,0x1950000002001,0x8280103491100387,0x8000003000c001a6,0x21000708013800c,0x830402080844a3c,0xc7061c18b380020,0x15000600020858b0,0xc440100004106400,0x4006020c38108041,0x800000b000a0c0e6])
  | _ => 0

def word47_1 : Nat → Nat
  | 0 => (limbs64 [0x8a3ffe003b3823e2,0x28948e8631872698,0x2a5df3463e30c725,0xdfe0071969b2b78b,0xaabfe001c931fe00,0x17397ed396398e86,0xad27003fe002138e,0xa92902b2fcede58,0x1d26c4dc127fe005,0x228b107ddf806561,0x27f801d66029854d,0x874669edc2998346,0xa189fff801cc21e0,0x2078a9b3ab7ad51f,0xa881b82dba69de44,0x9c9f39b1617ff800,0x32b4ff8013e445f3,0x21fe0054a347cc7d,0x627cd40d2f90ffe0,0x440f400a533b1df,0xe0037ba66c114706,0xffe004ac9ee884e6,0x86a0afaf704e0c0a,0xd4a4c0c1639aac1e,0x3f8798c1e6ba9b1b,0x1a7d7f8011c4f7f8,0x14a07f6a6152ae7,0xa9b2bc39c5167fe0,0x2fa27fe005904c0,0x2f2ff801fe007f80,0x1fe0077033fe0057,0x93bfe006d89a44ac,0xe1a3fe006b24630,0xb28694e2f3bd70f3,0xc41583d2aa5b784,0xafb90fb09e102d00,0x3100962d96215c05,0xf5b315a809af08fc,0xca36c2a61332d6c5,0xaf440dd23c9683d8,0x1e856d9db2864642,0x231413012cc82198,0x97d0476f91bfc10d,0x74ad920400c1dc42,0x823e41c809f18022,0x20734679470ab3a7,0xf239d5a65e51155e,0x874b7248f67ce49c,0x496dd8029f523f0a,0x8f098147b26494bd,0x1c9da540e290a24e,0x627601918d28a9aa,0x7a816d19f325abe2,0xe73e55e426a22a68,0xf1d80ac8ee0faaeb,0xdca938b0b5c4c576,0xab3c533318d8ec25,0x52ed0b19d71435be,0x39ebcbcca4b6e04a,0xa32bcbc6f879c356,0x58ce3fea8d785057,0xc456d487d884058,0xdd60f1ff801fe007,0x929dfe007bc9d409])
  | 1 => (limbs64 [0xcb98a88600398a84,0x8049988944003988,0x8878039888860039,0x8884400398814084,0x5986944049986140,0x8459828880039828,0x8600398214088794,0x9942887948142887,0x18b04888718a0488,0x8718994288718814,0x2887188140845182,0x1408871819428871,0x4894400314888780,0x31488860030c8140,0x8450499478050489,0x4400304888780504,0x8886003048140886,0x98a0488869889440,0x298888780298888,0x6002988140844986,0x9440029840488869,0x8214088694894400,0x29469440028c9143,0x8048c88868448c81,0x4084488914800288,0x8948002888944002,0x8888860028869440,0x288614084484994,0x7804848887804848,0x1408868480488861,0x8a8c884418a88600,0x218a848886188142,0x8861881408441821,0x4088618094684418,0x888002180886002,0x1808488861808480,0x4814888600214814,0x2886049947804049,0x9428860489478040,0x4888780404888780,0x2048886002048140,0x887fe0077996350d,0xe60289503ff800ac,0x73ab48cd862ff801,0xfe007f801ee5eff8,0x1fe000e0eb00c59,0xa83a6ce29fa4ec05,0x6ff801285c758379,0x12fc500f1ece7f80,0x4004d2b303695bc,0xc03e65dff8006ebb,0x312a8bc2bd4426ca,0x329c150180b5b847,0x7a4bff8002533893,0xf25e14ff801eebc6,0xa21e8219c51effe0,0x7f801fe007f8004,0x646eca36d931e881,0x7fe0053a8ffe007f,0x8005c477c319fe00,0x1b123108a8c8d354,0x8c7f8015e85d837f,0x50fdf52fd1cf6b38,0x5aca7ff8b379c3e2])
  | 2 => (limbs64 [0x3432060e06080c08,0x848480d8e542208,0x400100e05d80c08,0xe0db40bb209f800,0xa080a0807d80848,0xa08100dd80e0e27,0x902827add6eb75bc,0xde6eb63f1f8fdb6d,0xb4db6fa767cd8ff3,0x6bdcdc7d773b9de6,0xf371f3e8fe76bd1f,0x8fd7a3f1fe6c7e3f,0x5eced3e9f4fa7e76,0xbd1fa9e7b3d9ecf6,0x3ebd5e8fc7ebd8fa,0xbe3eaf5ee9f4e773,0xbf4dea3f1fe6d7a3,0xfcdaf47e7b1fd6e3,0xe7d3dde6f379bcb7,0x53f1f6ebd56e7b3d,0xe5c7e3fad8fe3e7d,0x1fcee767bbcde6f3,0x799ecf6f3799bcee,0x769f8fbd57797cbc,0x7cde3f7ae9cbe3e2,0x73884a7147ce28e9,0xc51e382387041424,0x751c02a3948c7014,0xe0281ca50394a67,0x32442448986e5091,0xcc702a424541c0f0,0x91c652058e00a9c,0xcd0091d812070246,0xf948423808472b5c,0xa1571c0ae3995a73,0x150e02b9cc543980,0x212008e6009ccf63,0x81ae60a3ce4461c8,0x3a39072720e4c11d,0x1c04e380f8728dce,0x41b1c83539068723,0x6ca4611c078380f6,0x731e0e6851c0db31,0x136718f4c41e9c63,0xe380c232404435b1,0xcc583981a12038e0,0x5e9cc5f398321206,0x8e00c9cc11090247,0x20ce6051ccca39a,0x2812458a4501c0fd,0x39466608c0c1191c,0x231384e8701dce33,0xb9cc70380d0701ac,0xe5591cc063998a22,0x318e6111cd100922,0x272a78a44e1c09f3,0x95f4523e0a47c9ca,0x2f30458608b82416,0x482e29058520b8e,0x1169c32111244124,0x8024251c90e290d8,0x702e4e5668888911,0x2345229ce3539ca6,0x43810a21a5ce44b9])
  | 3 => (limbs64 [0xa3e7286902aec026,0xe448a29edde69ff8,0x1fe007f8014c137,0xf801fe007f801fe0,0x6782c62557f8001,0x8cbb096400881a2d,0xa98a0e01973ab7a6,0xa2d1a5abe20daa1e,0xb43b7fe0026847b4,0xd7c3a33766b571e6,0x549e85a3e7a0c7f8,0x6979ab3724975,0xf13a142cff801950,0x1ff80106e9ff801f,0xe0001a4cccd5ff80,0x1fe006399360c1f8,0x343ce917f800c64c,0xb30f2fe82bcc1572,0x581ab23fe006718a,0x6e2f9302060830c1,0x1d860c0872e261c0,0x8100648010000188,0x146d38202040042e,0x3000000044010010,0x9840030105220458,0xc045840006245011,0xe04c82028479a001,0x8485001c08100186,0x8204000080004011,0x20420902040002a,0x820208624c41873,0xc614c2084108210,0x423816fc9f0bda79,0x8ea5d1392700e05b,0xc3786f2dc5b5b536,0x70ce598330662ca5,0x90b1a610c31752d8,0x5b8aed502a0542a6,0x14ca90522a2145a7,0x4e09d12aa284528,0x8d0420c3d4760ec1,0xd83b2744e49c2360,0x6c8d099a310620c4,0x9812f05e0bc1782f,0x5e0bc9702e25a0b,0x515a290524a09382,0x704e499919220444,0x849011f43a4708d9,0x1aa2a84c09a11022,0xc398580b01602d04,0x8090124200410720,0xc0180300620a80c0,0x1803006409000000,0x16fefefefcfdfc,0xd9fbfa07fdfbfdfc,0xf6c100e4a4c0604,0x3680606060c0a06,0x9fc1609fc080e06,0xa080e0204060e06,0x60e08000a080406,0xe040402980a0806,0x6cb80ada0806080c,0x608040a08020604,0x10049c1c05b403b4])
  | 4 => (limbs64 [0x1616d561408845c0,0x8d602098033c9177,0xda5f9f94d9a66ff8,0x164858c9705298f,0xb1f55298408d214b,0x5f382ffe007f8007,0xa5f6b9ef6ab48c24,0xecc0d76a42906bb0,0x9364888bfb6b26fb,0x563ff9c89af29d5a,0x17258b7f23df3b73,0xd4d3cb840f4d6dd2,0x2904c7a03cff4813,0x414a2c5a7f801820,0xee1a13fe007f801a,0x6847f801fe001795,0x6e61e7780bfe000f,0x3defee1b812a28ae,0xe539636259024733,0x35c86b3ca9ea01f,0x324bc4a364045df2,0x2aca457f801fe000,0x3b63fe000a9d7fe0,0x19a0ff43aff8000,0x86768634cabd013,0x842cca5770167f,0x801fe001d173c2c4,0xdb00eccb282953ee,0x562a13956c9ab8e6,0xe4b0cd85b5831ca8,0x210668ff8005c7fa,0x133f0ce3b19787c3,0xeff801fe00390331,0x6442f23d2107ff80,0x12257b508bfe007f,0x801f086b6873fe00,0x3087666efc401770,0xc3a214114afc52fe,0x400656c1da404e60,0x4b6a157a253589b9,0x7ab6aceb9891fb27,0x1e084928289ca1ed,0x219c1a30f458ff80,0x1022ee3a01722b81,0xffb89fc69f6f414,0xc495abc239604e66,0xaa4a96a4df9496f,0xd237c69aa8263fd0,0x1de2dbe6a508660d,0x1ae750bb8d2cf1c0,0x95226c6a51852a21,0xcf9c001a3a35d9bd,0x792f8c8a071a1587,0x134969ac5a734af1,0xaa039645d5613ddc,0x36a2c163a8e8d186,0x986de7b176c8e0e1,0xdec6eb7f80196872,0xb107c05ee403ffe0,0x73678621a709bf,0xe0077829546a6e87,0xd301f84843866d6c,0x32a9efbd78235285,0x22148e627a70cace])
  | 5 => (limbs64 [0xf6e14157545f737f,0x88a7291db5a587b2,0x2e6d6998acb8064c,0x57fc07f80494d625,0xe349a2894d3c50af,0xfc07f80b64f2247f,0xc0671bff01fe03fc,0x7f80418f6a8b4da,0xf7aaad1f536f917a,0x5a8380fc22f8437f,0x80d0cedf2f959ff8,0xff000c04316ff80,0xe086d38eee78437f,0x409fe01d868ab2df,0x3ea12c2282044043,0xa6319a5294a5294,0xa5294b38a0000000,0x7589c4b01007f5,0x26c9b26d9326c9ba,0x659946e1b86d1b0e,0xca707e0f6952754d,0x1b8743b1e5594d5a,0x429052c805641542,0xac107588391090e,0x2007106a21241392,0x2090d0734804741,0xe6988f1007883204,0x193a0c38a40a8381,0x41e4208e10068806,0x73212012221a7301,0x2050221a71862050,0x211270860221800a,0x6206205021126086,0x850221a32221850,0x211222662a21800a,0x21a51a51000a1246,0x2812221a12262812,0x221a12261012221a,0x12012651e0121201,0x2221e01212012050,0x221872a32221a110,0x72a1201222187026,0x2812221870262221,0x8008702120122218,0x52660a2180081206,0x221800af9cfaad4,0xed926349a7f8001f,0x1569672e7f66802,0x44a3906ef420b20,0x5ffe0000a4066a7b,0x22fdea2fa91b2c5,0x4632aa3eac87b763,0x867aa225a699ff80,0x1fe007f801fe007f,0x80116e7a810f649d,0xff801ec4b7691394,0x29e6a65a0fdff800,0x2512015dfe00460,0x3dcc50ff801d453d,0xc0eebc80cb2954a9,0x539b1a18788440e0,0x46fec2c7544f812f,0x7fe00470076a38a6,0x8c3240df0346f26f])
  | 6 => (limbs64 [0x25f,0x103549c411304304,0x28110f11dff80c8a])
  | _ => 0

def compactWords47 (i : Nat) : Nat :=
  if i < 15 then (if i < 8 then word47_0 (i % 8) else word47_1 (i % 8)) else 0

def compactCount47 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 9
  | 7 => 89
  | 6 => 158
  | 5 => 132
  | 4 => 26
  | 3 => 1
  | _ => 0

def compactPath47 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords47 (15 + 12*i) 12
  | 7 => let v := readCompactBits compactWords47 (1145 + 16*i) 16
    (readCompactBits compactWords47 (1037 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords47 (15639 + 18*i) 18
    (readCompactBits compactWords47 (14655 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords47 (40953 + 19*i) 19
    (readCompactBits compactWords47 (38325 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 4 => let v := readCompactBits compactWords47 (55491 + 17*i) 17
    (readCompactBits compactWords47 (54435 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | 3 => let v := readCompactBits compactWords47 (57446 + 12*i) 12
    (readCompactBits compactWords47 (57386 + 60*(v >>> 12)) 60) ||| ((v &&& 4095) <<< 60)
  | _ => 0

def compactLive47 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords47 (0 + 5*i) 5
  | 8 => readCompactBits compactWords47 (123 + 6*i) 6
  | 7 => readCompactBits compactWords47 (2569 + 7*i) 7
  | 6 => readCompactBits compactWords47 (18483 + 8*i) 8
  | 5 => readCompactBits compactWords47 (43461 + 9*i) 9
  | 4 => readCompactBits compactWords47 (55933 + 10*i) 10
  | 3 => readCompactBits compactWords47 (57458 + 11*i) 11
  | _ => 0

def compactPoolIDs47 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords47 (11 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords47 (5 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords47 (532 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords47 (177 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords47 (8238 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords47 (3192 + 6*(v &&& 1023)) (6*n)
    compactIDsFromBits bits 6 n
  | 6 => let v := readCompactBits compactWords47 (26467 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords47 (19747 + 8*(v &&& 1023)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords47 (45753 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords47 (44649 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 4 => let v := readCompactBits compactWords47 (56247 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords47 (56193 + 9*(v &&& 7)) (9*n)
    compactIDsFromBits bits 9 n
  | 3 => let v := readCompactBits compactWords47 (57469 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords47 (57469 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket47 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords47 (631 + 4*(i % 7)) 4
    let off := ((i/7 + d) % 27)
    let v := readCompactBits compactWords47 (659 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits compactWords47 (9484 + 6*(i % 77)) 6
    let off := ((i/77 + d) % 277)
    let v := readCompactBits compactWords47 (9946 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 6 => let d := readCompactBits compactWords47 (28679 + 7*(i % 136)) 7
    let off := ((i/136 + d) % 483)
    let v := readCompactBits compactWords47 (29631 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 5 => let d := readCompactBits compactWords47 (47205 + 7*(i % 102)) 7
    let off := ((i/102 + d) % 362)
    let v := readCompactBits compactWords47 (47919 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 4 => let d := readCompactBits compactWords47 (56377 + 4*(i % 16)) 4
    let off := ((i/16 + d) % 63)
    let v := readCompactBits compactWords47 (56441 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits compactWords47 (57471 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords47 (57472 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def samplesP63 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xfbfdd6fffffdd9be,0xffdf33f7ddffef7f,0xdee2f713ffffff7f,0xffdfdf9ff66fdfff,0xb5dff63d3bed070e,0xfa7dd3fff7ec1f1e,0xe7fff7f1eb877fef,0xffffcffe5ff3ffbf,0xf9acff871ffc1e7f,0xfef2ffe4f477fe3f,0x786ffede7a6b7d6b,0x715ff9b97fdfc9fc,0xbfcfba99fe31cff,0x769f4f7ff83df3fb,0x5facb8b1f4be33a7,0xf57f4154ddfdf765]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xee77dbfff7fff77,0xcef9ff9d7fa71fc5,0xf7ddc8fe3ffffbfb,0xfdf7e7ffdff2f3fd,0x6fa47fd3ff37fdfd,0x8ff67f9c7c7be9f3,0x1a1fce0fdc7d8f55,0x7ffefbfbeefff7ee,0x7f57c3fdfe9ff9ba,0x1f9db67f9ffaa3f6,0x8ff807f387df8396,0x9fa83fd7cfa07703,0xfff76f5ef4bdef93,0xfbf9f99e1feb7d2c,0xb957c7ce6be1ecf8,0x3ea1bfbbf65638de]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xffd6be53ff9f6fff,0xf9fe47dfe3f83086,0x3c0b0f47cffffefc,0x7f3bfcfffff7fe01,0xfaff83ce3f78783f,0xf3839dff88423e61,0xfe013f60c27f017,0xbf9ffdffff3ffcf7,0x8ff87cf99fe3e1ef,0xe11e3f8f387ffdc0,0xf18ff803b80bde17,0x823fc61c7030039c,0xf4fbbff707dff0bc,0xbc1ff3ede7ce5d4c,0x1a783f408c2fcf07,0xcbc67be3079b42e1]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xfabb3cbf1ffb7fd,0xff2fb9f9fe19d1b8,0xc17433b84fffff9f,0xcffdff63ff18fe0e,0x7f3f9cf6c09f8ec1,0xfdffee0fb7bdc08e,0xf060fc7873d800e8,0x3fe73e7fffde7ffb,0xf7ff9f3ee0247fd3,0xe3efc7f1db80fe7f,0x1630f97c5df42de8,0x6cc000e380cfbc67,0xbff5ff78e5f35f,0x5fee1df2e1f78eb3,0xe483403f33563179,0xc3dc9f0ce8e8cd1a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xff7acd87fee3ffff,0x3f16fe262e6efe59,0x9d1c219fffefef,0xf7ee3ffced8f21f7,0xc9e1e93bc4f2f7ff,0x747fa3f1cfd2e211,0xe18300819798b318,0xbffbff8db3efbf7f,0xffdbe447e3fb9fdc,0xfcfd781aef8f0db8,0xe05300a1e394b094,0xe1a0c144932f8678,0xbcfffffff5aff60,0xe972aea37e3be3c7,0x2758c8f78cc80c18,0x7bfe6bc23068127]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xdfd6b23fffefecb,0xf7e1cc6a91d7efa2,0x2b22e0cc2ffff5f7,0xbafffbff38fd0dfa,0x965a7fedffcffbf2,0xf887c627b8515ec,0x1c1c290e20624ca2,0x7ffdf7f7fdfdcbdd,0xfea73bfa7d5fe625,0x1f63c9ff67fd53c9,0xf84070c04204269,0x1e573e2a2c507883,0xf4ffdefceb3e0fef,0x87e5f65d9fd4bed0,0xc0a737085311d2c6,0x3b7bfcc318213e98]))
  | _ => 0

def samplesQ63 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x402290020125645,0x120841820001000,0x211108a402846000,0x401c208016982001,0xb7200a0d04928131,0x601ce0000502080,0x800140818208000,0x1060ce02503200b8,0x9ac808100000050,0x12c01434080000,0x79e001223a60a083,0x1360005900104a63,0xc80198031c40,0x36814372000d9148,0x442c8001049003a0,0xb005445e17564]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x118824104c00588,0x910c006200186432,0x23601484a4812,0x20010e4821480480,0x80694084100e26a6,0xa00908a525000006,0x870821400100218a,0x82c4914b08892126,0x44002a24ca050022,0x508810418242010a,0x451a4484900249a4,0x48e0940829840142,0x4262050844b18992,0xcb11100815232920,0x281244c062608840,0xaca0b132f4162892]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xf02941ac10e49801,0xa4118004c23ef59,0xc5e4e0282d811280,0x85425b1d00824256,0x3c6642249cd01c1,0x8a470118caccc0d,0x341d081283c93361,0x4f1b09949c2c54c3,0x10511f487c83aa08,0xe5a43a804095b000,0xe03288044853f08,0x838d00a5ec629a88,0x25b333b407447034,0x282ca38ce6445ca4,0x38d03910830bc40b,0xc3c45bc3031a4241]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x544c344700c852,0x10d0408404e66744,0x7e8a4841b3128028,0xbc20b0f48111abd,0x888052913503808,0x3e1430d8490e5f35,0x42c488785807545,0x270a267522106e40,0xf1130b406c69f889,0x62e01e0248017654,0x59196616122c,0x800318d2d275d08c,0x56bf21e711c4a24f,0x116a28d0a1f002b5,0xa890103a9306e018,0xc3d41f0ca8c88418]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xf085327a01170082,0xc27811d0f18b01e6,0xce20c3de00750770,0x88726401e6606a58,0x14038fd04d200a0a,0x80a6005a708506f2,0x3a61ff12bc0bcc69,0xfc98201883c39e19,0x1e09e44b81dc2ba9,0x6278a9f809a1c7d,0x90242e2b00a58009,0xfc05c7021282950c,0x25ccfedee3186204,0x4032ac23785ac0c7,0x8708c956d81206ca,0xf3fe6a802048127]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x20294dc8221031c,0x483a32d166a90249,0x545d5512d428a235,0x9910e52465231632,0x2804a45203219454,0x101e863690484ab3,0x7aa775305c9dd438,0xf9ad50b065448504,0xb298a519a4cc86a5,0x2e0681b7c1bb24db,0xa2dd1a148854440a,0xa40b4b2405019429,0x14ddde78292a25ad,0x84e474052ac02681,0x8489db42511056c6,0x5f7bec8118211a88]))
  | _ => 0

def compactPerms63 : Array (List Nat) := ([[], [84], [50], [50, 84]] : List (List Nat)).toArray

def compactDomains63 : Array (Sig × Nat) := ([(subcube 16 0, 10)] : List (Sig × Nat)).toArray

def compactWords63 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount63 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath63 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive63 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords63 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs63 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords63 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords63 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket63 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid556 : CompactGrid := (556, 3, samplesP556, samplesQ556)
def tab556 : CompactTable := (compactCount556, compactPath556, compactLive556, compactPoolIDs556, compactBucket556)
def check556 (k : Nat) := compactNode grid556 tab556 compactDomains556 compactPerms556 k
def sliceSpecs556 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains556 : ∀ d ∈ compactDomains556, Slice true (vars 556) (graphGoal 556) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs556)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs556 : properPairs (graphGoal 556) (asRow samplesP556) (asRow samplesQ556) :=
  compactPairs (g := grid556) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos556 : ∀ p ∈ compactPerms556, autoOK (graphGoal 556) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c556k3p0 : chartBlock (check556 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev556k3 : chartBlock (check556 3) 0 1 = true :=
  c556k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded556 : Impossible true (graphGoal 556) 3 (vars 556).toFinset := by
  apply compactRoot (g := grid556) (t := tab556) (dom := compactDomains556) (perms := compactPerms556) pairs556 domains556 autos556
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev556k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound556 : Lower true (vars 556) (graphGoal 556) 4 :=
  plain_low (hints := 4296048640) (by decide +kernel) excluded556

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound554 : Lower true (vars 554) (graphGoal 554) 4 :=
  carry_of (old := 554) (rep := 556) (swaps := [33]) (by decide +kernel) bound556

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound550 : Lower true (vars 550) (graphGoal 550) 4 :=
  carry_of (old := 550) (rep := 556) (swaps := [33, 50]) (by decide +kernel) bound556

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound526 : Lower true (vars 526) (graphGoal 526) 4 :=
  carry_of (old := 526) (rep := 556) (swaps := [33, 50, 83]) (by decide +kernel) bound556

def grid558 : CompactGrid := (558, 6, samplesP558, samplesQ558)
def tab558 : CompactTable := (compactCount558, compactPath558, compactLive558, compactPoolIDs558, compactBucket558)
def check558 (k : Nat) := compactNode grid558 tab558 compactDomains558 compactPerms558 k
def sliceSpecs558 : List SliceSpec := [(2, 0, 556, 0, 0, 4, 4), (4, 0, 554, 0, 0, 4, 4), (8, 0, 550, 0, 0, 4, 4), (32, 0, 526, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains558 : ∀ d ∈ compactDomains558, Slice true (vars 558) (graphGoal 558) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(556, 4), (554, 4), (550, 4), (526, 4)]) (specs := sliceSpecs558)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound556
    · exact bound554
    · exact bound550
    · exact bound526
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs558 : properPairs (graphGoal 558) (asRow samplesP558) (asRow samplesQ558) :=
  compactPairs (g := grid558) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos558 : ∀ p ∈ compactPerms558, autoOK (graphGoal 558) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c558k3p0 : chartBlock (check558 3) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev558k3 : chartBlock (check558 3) 0 2 = true :=
  c558k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c558k4p0 : chartBlock (check558 4) 0 3 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev558k4 : chartBlock (check558 4) 0 3 = true :=
  c558k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c558k5p0 : chartBlock (check558 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev558k5 : chartBlock (check558 5) 0 1 = true :=
  c558k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c558k6p0 : chartBlock (check558 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev558k6 : chartBlock (check558 6) 0 1 = true :=
  c558k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded558 : Impossible true (graphGoal 558) 6 (vars 558).toFinset := by
  apply compactRoot (g := grid558) (t := tab558) (dom := compactDomains558) (perms := compactPerms558) pairs558 domains558 autos558
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev558k3
    · exact lev558k4
    · exact lev558k5
    · exact lev558k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound558 : Lower true (vars 558) (graphGoal 558) 7 :=
  plain_low (hints := 2148016384) (by decide +kernel) excluded558

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound1065 : Lower true (vars 1065) (graphGoal 1065) 4 :=
  carry_of (old := 1065) (rep := 556) (swaps := [32]) (by decide +kernel) bound556

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4131 : Lower true (vars 4131) (graphGoal 4131) 4 :=
  carry_of (old := 4131) (rep := 556) (swaps := [32, 49]) (by decide +kernel) bound556

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16395 : Lower true (vars 16395) (graphGoal 16395) 4 :=
  carry_of (old := 16395) (rep := 556) (swaps := [32, 49, 83]) (by decide +kernel) bound556

def grid43 : CompactGrid := (43, 6, samplesP43, samplesQ43)
def tab43 : CompactTable := (compactCount43, compactPath43, compactLive43, compactPoolIDs43, compactBucket43)
def check43 (k : Nat) := compactNode grid43 tab43 compactDomains43 compactPerms43 k
def sliceSpecs43 : List SliceSpec := [(0, 1, 554, 0, 0, 4, 4), (0, 2, 1065, 0, 0, 4, 4), (0, 8, 4131, 0, 0, 4, 4), (0, 32, 16395, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains43 : ∀ d ∈ compactDomains43, Slice true (vars 43) (graphGoal 43) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(554, 4), (1065, 4), (4131, 4), (16395, 4)]) (specs := sliceSpecs43)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound554
    · exact bound1065
    · exact bound4131
    · exact bound16395
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs43 : properPairs (graphGoal 43) (asRow samplesP43) (asRow samplesQ43) :=
  compactPairs (g := grid43) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos43 : ∀ p ∈ compactPerms43, autoOK (graphGoal 43) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c43k3p0 : chartBlock (check43 3) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev43k3 : chartBlock (check43 3) 0 2 = true :=
  c43k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c43k4p0 : chartBlock (check43 4) 0 3 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev43k4 : chartBlock (check43 4) 0 3 = true :=
  c43k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c43k5p0 : chartBlock (check43 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev43k5 : chartBlock (check43 5) 0 1 = true :=
  c43k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c43k6p0 : chartBlock (check43 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev43k6 : chartBlock (check43 6) 0 1 = true :=
  c43k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded43 : Impossible true (graphGoal 43) 6 (vars 43).toFinset := by
  apply compactRoot (g := grid43) (t := tab43) (dom := compactDomains43) (perms := compactPerms43) pairs43 domains43 autos43
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev43k3
    · exact lev43k4
    · exact lev43k5
    · exact lev43k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound43 : Lower true (vars 43) (graphGoal 43) 7 :=
  plain_low (hints := 3222012490) (by decide +kernel) excluded43

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound39 : Lower true (vars 39) (graphGoal 39) 7 :=
  carry_of (old := 39) (rep := 43) (swaps := [50]) (by decide +kernel) bound43

def grid1069 : CompactGrid := (1069, 4, samplesP1069, samplesQ1069)
def tab1069 : CompactTable := (compactCount1069, compactPath1069, compactLive1069, compactPoolIDs1069, compactBucket1069)
def check1069 (k : Nat) := compactNode grid1069 tab1069 compactDomains1069 compactPerms1069 k
def sliceSpecs1069 : List SliceSpec := [(4, 0, 1065, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains1069 : ∀ d ∈ compactDomains1069, Slice true (vars 1069) (graphGoal 1069) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(1065, 4)]) (specs := sliceSpecs1069)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound1065
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs1069 : properPairs (graphGoal 1069) (asRow samplesP1069) (asRow samplesQ1069) :=
  compactPairs (g := grid1069) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos1069 : ∀ p ∈ compactPerms1069, autoOK (graphGoal 1069) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c1069k4p0 : chartBlock (check1069 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev1069k4 : chartBlock (check1069 4) 0 1 = true :=
  c1069k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded1069 : Impossible true (graphGoal 1069) 4 (vars 1069).toFinset := by
  apply compactRoot (g := grid1069) (t := tab1069) (dom := compactDomains1069) (perms := compactPerms1069) pairs1069 domains1069 autos1069
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev1069k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound1069 : Lower true (vars 1069) (graphGoal 1069) 5 :=
  plain_low (hints := 1074008068) (by decide +kernel) excluded1069

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound2083 : Lower true (vars 2083) (graphGoal 2083) 4 :=
  carry_of (old := 2083) (rep := 556) (swaps := [32, 49]) (by decide +kernel) bound556

def grid2091 : CompactGrid := (2091, 4, samplesP2091, samplesQ2091)
def tab2091 : CompactTable := (compactCount2091, compactPath2091, compactLive2091, compactPoolIDs2091, compactBucket2091)
def check2091 (k : Nat) := compactNode grid2091 tab2091 compactDomains2091 compactPerms2091 k
def sliceSpecs2091 : List SliceSpec := [(8, 0, 2083, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains2091 : ∀ d ∈ compactDomains2091, Slice true (vars 2091) (graphGoal 2091) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(2083, 4)]) (specs := sliceSpecs2091)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound2083
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs2091 : properPairs (graphGoal 2091) (asRow samplesP2091) (asRow samplesQ2091) :=
  compactPairs (g := grid2091) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos2091 : ∀ p ∈ compactPerms2091, autoOK (graphGoal 2091) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c2091k4p0 : chartBlock (check2091 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev2091k4 : chartBlock (check2091 4) 0 1 = true :=
  c2091k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded2091 : Impossible true (graphGoal 2091) 4 (vars 2091).toFinset := by
  apply compactRoot (g := grid2091) (t := tab2091) (dom := compactDomains2091) (perms := compactPerms2091) pairs2091 domains2091 autos2091
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev2091k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound2091 : Lower true (vars 2091) (graphGoal 2091) 5 :=
  plain_low (hints := 1074004034) (by decide +kernel) excluded2091

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4135 : Lower true (vars 4135) (graphGoal 4135) 5 :=
  carry_of (old := 4135) (rep := 2091) (swaps := [50]) (by decide +kernel) bound2091

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16399 : Lower true (vars 16399) (graphGoal 16399) 5 :=
  carry_of (old := 16399) (rep := 1069) (swaps := [81]) (by decide +kernel) bound1069

def grid45 : CompactGrid := (45, 4, samplesP45, samplesQ45)
def tab45 : CompactTable := (compactCount45, compactPath45, compactLive45, compactPoolIDs45, compactBucket45)
def check45 (k : Nat) := compactNode grid45 tab45 compactDomains45 compactPerms45 k
def sliceSpecs45 : List SliceSpec := [(0, 1, 556, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains45 : ∀ d ∈ compactDomains45, Slice true (vars 45) (graphGoal 45) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(556, 4)]) (specs := sliceSpecs45)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound556
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs45 : properPairs (graphGoal 45) (asRow samplesP45) (asRow samplesQ45) :=
  compactPairs (g := grid45) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos45 : ∀ p ∈ compactPerms45, autoOK (graphGoal 45) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c45k4p0 : chartBlock (check45 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev45k4 : chartBlock (check45 4) 0 1 = true :=
  c45k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded45 : Impossible true (graphGoal 45) 4 (vars 45).toFinset := by
  apply compactRoot (g := grid45) (t := tab45) (dom := compactDomains45) (perms := compactPerms45) pairs45 domains45 autos45
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev45k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 5 :=
  plain_low (hints := 5370056716) (by decide +kernel) excluded45

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound15 : Lower true (vars 15) (graphGoal 15) 5 :=
  carry_of (old := 15) (rep := 45) (swaps := [33, 50, 83]) (by decide +kernel) bound45

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound1061 : Lower true (vars 1061) (graphGoal 1061) 4 :=
  carry_of (old := 1061) (rep := 556) (swaps := [32, 50]) (by decide +kernel) bound556

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16391 : Lower true (vars 16391) (graphGoal 16391) 4 :=
  carry_of (old := 16391) (rep := 556) (swaps := [32, 49, 82, 83]) (by decide +kernel) bound556

def grid47 : CompactGrid := (47, 9, samplesP47, samplesQ47)
def tab47 : CompactTable := (compactCount47, compactPath47, compactLive47, compactPoolIDs47, compactBucket47)
def check47 (k : Nat) := compactNode grid47 tab47 compactDomains47 compactPerms47 k
def sliceSpecs47 : List SliceSpec := [(0, 1, 558, 0, 0, 7, 7), (4, 0, 43, 0, 0, 7, 7), (8, 0, 39, 0, 0, 7, 7), (0, 2, 1069, 0, 0, 5, 5), (0, 4, 2091, 0, 0, 5, 5), (0, 8, 4135, 0, 0, 5, 5), (0, 32, 16399, 0, 0, 5, 5), (2, 0, 45, 0, 0, 5, 5), (32, 0, 15, 0, 0, 5, 5), (2, 1, 556, 0, 0, 4, 4), (4, 1, 554, 0, 0, 4, 4), (4, 2, 1065, 0, 0, 4, 4), (4, 8, 4131, 0, 0, 4, 4), (4, 32, 16395, 0, 0, 4, 4), (8, 2, 1061, 0, 0, 4, 4), (8, 4, 2083, 0, 0, 4, 4), (8, 32, 16391, 0, 0, 4, 4), (32, 1, 526, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains47 : ∀ d ∈ compactDomains47, Slice true (vars 47) (graphGoal 47) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(558, 7), (43, 7), (39, 7), (1069, 5), (2091, 5), (4135, 5), (16399, 5), (45, 5), (15, 5), (556, 4), (554, 4), (1065, 4), (4131, 4), (16395, 4), (1061, 4), (2083, 4), (16391, 4), (526, 4)]) (specs := sliceSpecs47)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound558
    · exact bound43
    · exact bound39
    · exact bound1069
    · exact bound2091
    · exact bound4135
    · exact bound16399
    · exact bound45
    · exact bound15
    · exact bound556
    · exact bound554
    · exact bound1065
    · exact bound4131
    · exact bound16395
    · exact bound1061
    · exact bound2083
    · exact bound16391
    · exact bound526
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs47 : properPairs (graphGoal 47) (asRow samplesP47) (asRow samplesQ47) :=
  compactPairs (g := grid47) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos47 : ∀ p ∈ compactPerms47, autoOK (graphGoal 47) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k3p0 : chartBlock (check47 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k3 : chartBlock (check47 3) 0 1 = true :=
  c47k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k4p0 : chartBlock (check47 4) 0 26 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k4 : chartBlock (check47 4) 0 26 = true :=
  c47k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p0 : chartBlock (check47 5) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p1 : chartBlock (check47 5) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p2 : chartBlock (check47 5) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p3 : chartBlock (check47 5) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p4 : chartBlock (check47 5) 128 4 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k5 : chartBlock (check47 5) 0 132 = true :=
  (chartBlock_join (a := 64) (b := 68) (chartBlock_join (a := 32) (b := 32) c47k5p0 c47k5p1) (chartBlock_join (a := 32) (b := 36) c47k5p2 (chartBlock_join (a := 32) (b := 4) c47k5p3 c47k5p4)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k6p0 : chartBlock (check47 6) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k6p1 : chartBlock (check47 6) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k6p2 : chartBlock (check47 6) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k6p3 : chartBlock (check47 6) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k6p4 : chartBlock (check47 6) 128 30 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k6 : chartBlock (check47 6) 0 158 = true :=
  (chartBlock_join (a := 64) (b := 94) (chartBlock_join (a := 32) (b := 32) c47k6p0 c47k6p1) (chartBlock_join (a := 32) (b := 62) c47k6p2 (chartBlock_join (a := 32) (b := 30) c47k6p3 c47k6p4)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k7p0 : chartBlock (check47 7) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k7p1 : chartBlock (check47 7) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k7p2 : chartBlock (check47 7) 64 25 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k7 : chartBlock (check47 7) 0 89 = true :=
  (chartBlock_join (a := 32) (b := 57) c47k7p0 (chartBlock_join (a := 32) (b := 25) c47k7p1 c47k7p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k8p0 : chartBlock (check47 8) 0 9 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k8 : chartBlock (check47 8) 0 9 = true :=
  c47k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k9p0 : chartBlock (check47 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k9 : chartBlock (check47 9) 0 1 = true :=
  c47k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded47 : Impossible true (graphGoal 47) 9 (vars 47).toFinset := by
  apply compactRoot (g := grid47) (t := tab47) (dom := compactDomains47) (perms := compactPerms47) pairs47 domains47 autos47
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev47k3
    · exact lev47k4
    · exact lev47k5
    · exact lev47k6
    · exact lev47k7
    · exact lev47k8
    · exact lev47k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound47 : Lower true (vars 47) (graphGoal 47) 10 :=
  plain_low (hints := 3222024518) (by decide +kernel) excluded47

def projectedWire (points : Row → X) (f : F) : Wire Row := fun r => f (points r)

theorem projectedAvailable {points : Row → X} {s : Set F} {bank : List (Wire Row)} {f : F}
    (all : ∀ u ∈ s, Available true bank (projectedWire points u)) (h : Av s f) :
    Available true bank (projectedWire points f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact all _ hu
  · exact avail_inv rfl (all _ hu)

theorem projectedProgram (points : Row → X) (roots : List (Wire Row)) {s : Set F} {f : F} {k : Nat}
    (program : Prog s f k) :
    ∀ {spent : Nat} {bank : List (Wire Row)}, Reach true roots spent bank →
      (∀ u ∈ s, Available true bank (projectedWire points u)) →
      ∃ result, Reach true roots (spent + k) result ∧ Available true result (projectedWire points f) := by
  induction program with
  | done h =>
    intro spent bank built all
    exact ⟨bank, built, projectedAvailable all h⟩
  | @gate s f a b k tag ha hb rest ih =>
    intro spent bank built all
    let left := projectedWire points a
    let right := projectedWire points b
    have e : projectedWire points (PEqualNP.Outside.L_meta_49153.comb tag a b) = combine (!tag) left right := by
      cases tag <;> rfl
    have next := Reach.two (!tag) built (projectedAvailable all ha) (projectedAvailable all hb)
    obtain ⟨result, run, hit⟩ := ih next (by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact Or.inl (by rw [e]; exact List.mem_cons_self)
      · exact available_cons _ (all _ hu))
    exact ⟨result, by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using run, hit⟩

end Evidence
end PEqualNP.Outside.L_meta_49153

namespace PEqualNP.Outside.L_meta_49153.ReadFour
open PEqualNP.Outside.L_meta_49153.Evidence

structure Binary (R : Type) where
  disj : Bool
  left : Wire R
  right : Wire R

def Binary.result (g : Binary R) : Wire R := combine g.disj g.left g.right

def stock (B : List (Wire R)) : List (Binary R) → List (Wire R)
  | [] => B
  | g::gs => stock (g.result :: B) gs

def Valid (B : List (Wire R)) : List (Binary R) → Prop
  | [] => True
  | g::gs => Available true B g.left ∧ Available true B g.right ∧ Valid (g.result::B) gs

theorem stock_append (B : List (Wire R)) (xs ys : List (Binary R)) :
    stock B (xs ++ ys) = stock (stock B xs) ys := by
  induction xs generalizing B with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem valid_append (B : List (Wire R)) (xs ys : List (Binary R)) :
    Valid B (xs ++ ys) ↔ Valid B xs ∧ Valid (stock B xs) ys := by
  induction xs generalizing B with
  | nil => simp [Valid, stock]
  | cons g gs ih =>
    simp only [List.cons_append, Valid, stock, ih]
    tauto

theorem stock_mem {B : List (Wire R)} {gs : List (Binary R)} {v : Wire R} :
    v ∈ stock B gs ↔ v ∈ B ∨ ∃ g ∈ gs, g.result = v := by
  induction gs generalizing B with
  | nil => simp [stock]
  | cons g gs ih =>
    simp only [stock, ih, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((same | inBase) | inTail)
      · exact Or.inr (Or.inl same.symm)
      · exact Or.inl inBase
      · exact Or.inr (Or.inr inTail)
    · rintro (inBase | (same | inTail))
      · exact Or.inl (Or.inr inBase)
      · exact Or.inl (Or.inl same.symm)
      · exact Or.inr inTail

theorem trace_of_reach {base bank : List (Wire R)} {n : Nat}
    (h : Reach true base n bank) :
    ∃ steps : List (Binary R), steps.length = n ∧ Valid base steps ∧ stock base steps = bank := by
  induction h using Reach.ind with
  | start => exact ⟨[],rfl,trivial,rfl⟩
  | @two k bank a b op hr ha hb ih =>
    obtain ⟨gs,hk,hg,hB⟩ := ih
    refine ⟨gs ++ [⟨op,a,b⟩],by simp [hk],?_,?_⟩
    · rw [valid_append, hB]
      exact ⟨hg,ha,hb,trivial⟩
    · rw [stock_append, hB]
      rfl

theorem avail_weaken {B C : List (Wire R)} {v : Wire R} (sub : ∀ w ∈ B, w ∈ C)
    (h : Available true B v) : Available true C v := by
  rcases h with q | q | ⟨_,q⟩
  · exact Or.inl (sub _ q)
  · exact Or.inr (Or.inl q)
  · exact Or.inr (Or.inr ⟨rfl,sub _ q⟩)

theorem reach_includes {B C : List (Wire R)} {n : Nat}
    (h : Reach true B n C) : ∀ w ∈ B, w ∈ C := by
  induction h using Reach.ind with
  | start => exact fun _ h => h
  | two _ _ _ _ ih => exact fun _ h => List.mem_cons_of_mem _ (ih _ h)

def pull (f : S → R) (v : Wire R) : Wire S := fun x => v (f x)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pull_available {B : List (Wire R)} {C : List (Wire S)} {f : S→R} {v : Wire R}
    (haveAll : ∀ a ∈ B, Available true C (pull f a)) (h : Available true B v) :
    Available true C (pull f v) := by
  rcases h with q | ⟨c,rfl⟩ | ⟨_,q⟩
  · exact haveAll _ q
  · exact Or.inr (Or.inl ⟨c,rfl⟩)
  · have e : inv (pull f (inv v)) = pull f v := by
      funext x
      simp [inv,pull]
    rw [← e]
    exact avail_inv rfl (haveAll _ q)

def Cheap (f : S→R) (B : List (Wire S)) (g : Binary R) : Prop :=
  Constant (pull f g.left) ∨ Constant (pull f g.right) ∨ Available true B (pull f g.result)

noncomputable def dropCount (f : S→R) (B : List (Wire S)) (gs : List (Binary R)) : Nat := by
  classical exact gs.countP (fun g => decide (Cheap f B g))

theorem pull_result (f : S→R) (g : Binary R) :
    pull f g.result = combine g.disj (pull f g.left) (pull f g.right) := by
  funext x
  cases eq : g.disj <;> simp [pull, Binary.result, combine, eq]

theorem discard {f : S→R} {B C : List (Wire S)} {g : Binary R}
    (sub : ∀ w ∈ B, w ∈ C)
    (ha : Available true C (pull f g.left))
    (hb : Available true C (pull f g.right))
    (h : Cheap f B g) : Available true C (pull f g.result) := by
  rcases h with h | h | h
  · rw [pull_result]
    exact from_constant _ (Or.inl h) ha hb
  · rw [pull_result]
    exact from_constant _ (Or.inr h) ha hb
  · exact avail_weaken sub h

theorem project_steps {f : S→R} {base : List (Wire S)} {src : List (Wire R)}
    {gs : List (Binary R)} (hv : Valid src gs)
    {k : Nat} {bank : List (Wire S)} (hr : Reach true base k bank)
    (supply : ∀ v ∈ src, Available true bank (pull f v)) :
    ∃ n C, n + dropCount f base gs = k + gs.length ∧ Reach true base n C ∧
      ∀ v ∈ stock src gs, Available true C (pull f v) := by
  classical
  induction gs generalizing src k bank with
  | nil => exact ⟨k,bank,by simp [dropCount],hr,supply⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,hv⟩ := hv
    have ha := pull_available supply ha
    have hb := pull_available supply hb
    by_cases cheap : Cheap f base g
    · have out := discard (reach_includes hr) ha hb cheap
      have next : ∀ v ∈ g.result :: src, Available true bank (pull f v) := by
        intro v h
        rcases List.mem_cons.mp h with rfl | q
        · exact out
        · exact supply _ q
      obtain ⟨n,C,eq,reach,sup⟩ := ih hv hr next
      refine ⟨n,C,?_,reach,sup⟩
      simp only [dropCount, List.countP_cons, decide_eq_true_eq, cheap, ite_true, List.length_cons] at eq ⊢
      omega
    · have nextReach := Reach.two g.disj hr ha hb
      rw [← pull_result] at nextReach
      have next : ∀ v ∈ g.result :: src, Available true (pull f g.result :: bank) (pull f v) := by
        intro v h
        rcases List.mem_cons.mp h with rfl | q
        · exact Or.inl List.mem_cons_self
        · exact available_cons _ (supply _ q)
      obtain ⟨n,C,eq,reach,sup⟩ := ih hv nextReach next
      refine ⟨n,C,?_,reach,sup⟩
      simp only [dropCount, List.countP_cons, decide_eq_true_eq, cheap, ite_false, List.length_cons] at eq ⊢
      omega


def SignedIn (B : List (Wire R)) (v : Wire R) : Prop := v ∈ B ∨ inv v ∈ B

def Reads (B : List (Wire R)) (g : Binary R) : Prop :=
  SignedIn B g.left ∨ SignedIn B g.right

def Agrees (r s : R) (a : Wire R) : Prop := a r = a s

def AgreesOutside (r s : R) (skip bank : List (Wire R)) : Prop :=
  ∀ a ∈ bank, a ∉ skip → Agrees r s a

theorem literal_agrees {r s : R} {skip bank : List (Wire R)} {a : Wire R}
    (all : AgreesOutside r s skip bank) (ha : Available true bank a)
    (avoid : ¬ SignedIn skip a) : Agrees r s a := by
  rcases ha with h | ⟨b,rfl⟩ | ⟨_,h⟩
  · exact all _ h (fun q => avoid (Or.inl q))
  · rfl
  · simpa [Agrees, inv] using (all _ h (fun q => avoid (Or.inr q)))

theorem result_agrees {r s : R} {g : Binary R}
    (a : Agrees r s g.left) (b : Agrees r s g.right) :
    Agrees r s g.result := by
  cases eq : g.disj <;> simp [Binary.result,combine,Agrees,eq,show g.left r = g.left s from a,show g.right r = g.right s from b]

theorem quiet {r s : R} {skip bank : List (Wire R)} {gs : List (Binary R)}
    (h : Valid bank gs) (base : AgreesOutside r s skip bank)
    (noRead : ∀ g ∈ gs, ¬ Reads skip g) :
    (∀ g ∈ gs, Agrees r s g.result) ∧ AgreesOutside r s skip (stock bank gs) := by
  induction gs generalizing bank with
  | nil => exact ⟨by simp,base⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,h⟩ := h
    have no := noRead g List.mem_cons_self
    have eq := result_agrees (literal_agrees base hl (fun h => no (Or.inl h)))
      (literal_agrees base hr (fun h => no (Or.inr h)))
    have next : AgreesOutside r s skip (g.result::bank) := by
      intro v has outside
      rcases List.mem_cons.mp has with rfl | inTail
      · exact eq
      · exact base _ inTail outside
    obtain ⟨agreeTail,agreeBank⟩ := ih h next (fun g h => noRead g (List.mem_cons_of_mem _ h))
    refine ⟨?_,agreeBank⟩
    intro v h
    rcases List.mem_cons.mp h with rfl | q
    · exact eq
    · exact agreeTail _ q

theorem saturated {r s : R} {g : Binary R} {a : Wire R}
    (side : a = g.left ∨ a = g.right)
    (ha : a r = g.disj) (hb : a s = g.disj) :
    Agrees r s g.result := by
  rcases side with rfl | rfl
  · cases eq : g.disj <;> simp [Agrees, Binary.result, combine, eq, ha.trans eq, hb.trans eq]
  · cases eq : g.disj <;> simp [Agrees, Binary.result, combine, eq, ha.trans eq, hb.trans eq]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem quiet_split {r s : R} {skip bank : List (Wire R)} {pre suf : List (Binary R)} {g : Binary R} {F : Wire R}
    (h : Valid bank (pre ++ g::suf)) (base : AgreesOutside r s skip bank)
    (noPre : ∀ y ∈ pre, ¬ Reads skip y) (noSuf : ∀ y ∈ suf, ¬ Reads skip y)
    (center : Agrees r s g.result)
    (out : Available true (stock bank (pre ++ g::suf)) F)
    (notRaw : ¬ SignedIn skip F) : Agrees r s F := by
  rw [valid_append] at h
  obtain ⟨validPre, _, _, validSuf⟩ := h
  have before := (quiet validPre base noPre).2
  have after : AgreesOutside r s skip (g.result :: stock bank pre) := by
    intro a ha nmem
    rcases List.mem_cons.mp ha with rfl | q
    · exact center
    · exact before _ q nmem
  have eqTail := (quiet validSuf after noSuf).2
  rw [stock_append] at out
  exact literal_agrees eqTail out notRaw

noncomputable def tally (P : T → Prop) (gs : List T) : Nat := by
  classical exact gs.countP (fun g => decide (P g))

theorem tally_append (P : T → Prop) (ls rs : List T) :
    tally P (ls++rs) = tally P ls + tally P rs := by
  classical
  simp [tally, List.countP_append]

theorem tally_cons_yes (P : T → Prop) {a : T} (h : P a) (gs : List T) :
    tally P (a::gs) = tally P gs + 1 := by
  classical
  simp [tally, h]

theorem tally_cons_no (P : T → Prop) {a : T} (h : ¬ P a) (gs : List T) :
    tally P (a::gs) = tally P gs := by
  classical
  simp [tally, h]

theorem tally_one {P : T → Prop} {a : T} {gs : List T} (hi : a ∈ gs) (hp : P a) :
    1 ≤ tally P gs := by
  induction gs with
  | nil => simp at hi
  | cons x xs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [tally_cons_yes P hp]
      omega
    · have z := ih hi
      by_cases q : P x
      · rw [tally_cons_yes P q]
        omega
      · simpa [tally_cons_no P q] using z

theorem tally_disjoint_le {P Q L : T → Prop} (left : ∀ x, P x → L x)
    (right : ∀ x, Q x → L x) (disjoint : ∀ x, P x → ¬ Q x) (gs : List T) :
    tally P gs + tally Q gs ≤ tally L gs := by
  induction gs with
  | nil => simp [tally]
  | cons g gs ih =>
    by_cases a : P g
    · rw [tally_cons_yes P a, tally_cons_no Q (disjoint _ a), tally_cons_yes L (left _ a)]
      omega
    · rw [tally_cons_no P a]
      by_cases b : Q g
      · rw [tally_cons_yes Q b, tally_cons_yes L (right _ b)]
        omega
      · rw [tally_cons_no Q b]
        by_cases c : L g
        · rw [tally_cons_yes L c]
          omega
        · simpa [tally_cons_no L c] using ih

theorem read_once {A : List (Wire R)} {pre suf : List (Binary R)} {g : Binary R}
    (num : tally (Reads A) (pre ++ g::suf) ≤ 1) (h : Reads A g) :
    (∀ w ∈ pre, ¬ Reads A w) ∧ ∀ w ∈ suf, ¬ Reads A w := by
  rw [tally_append, tally_cons_yes _ h] at num
  constructor
  · intro w hw yes
    have := tally_one hw yes
    omega
  · intro w hw yes
    have := tally_one hw yes
    omega



def ix (p : Fin 4) : Fin 6 := ![0,3,4,5] p

def var (i : Fin 6) : Wire Row := observe (inputs.getD i.val Evidence.zero)

def rawBase : List (Wire Row) := List.ofFn var

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem raw_included (i : Fin 6) : var i ∈ rawBase := List.mem_ofFn.mpr ⟨i,rfl⟩

def whole (r : Row) : Bool := (3941132416 * 2 ^ 32 + 3900735616 : Nat).testBit (r.val % 64)



def coValue (_ : Fin 4) : Bool := true

def coIndex (p : Fin 4) (i : Fin 6) : Nat :=
  let j := if i.val < (ix p).val then i.val else i.val - 1
  if p=0 then j else ([0,1,5,2,3] : List Nat).getD j 0

def coRow (p : Fin 4) (r : Row) : Row :=
  ⟨(List.range 6).foldl (fun n i =>
    let j : Fin 6 := Fin.ofNat 6 i
    let c := bit r (inputs.getD (coIndex p j) Evidence.zero)
    if j = ix p || c then n + (1 <<< i) else n) 0 % 64,
    Nat.lt_trans (Nat.mod_lt _ (by decide : 0<64)) (by decide)⟩

def coRoots (p : Fin 4) : List Sig :=
  if p=0 then inputs.take 5 else vars 47

def coBase (p : Fin 4) : List (Wire Row) := (coRoots p).map observe

def atlasWord (r : Row) : Bool :=
  (4276676744 : Nat).testBit (r.val % 32)

def coGoal (p : Fin 4) : Wire Row :=
  if p=0 then atlasWord else observe (graphGoal 47)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem var_co_value : ∀ p : Fin 4, ∀ r : Row, var (ix p) (coRow p r) = coValue p := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coTarget : ∀ p : Fin 4, ∀ r : Row, whole (coRow p r) = coGoal p r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coRoot (p : Fin 4) {v : Wire Row} (member : v ∈ rawBase) :
    Available true (coBase p) (pull (coRow p) v) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  by_cases pin : i=ix p
  · subst i
    exact Or.inr (Or.inl ⟨coValue p, funext (var_co_value p)⟩)
  · let col := inputs.getD (coIndex p i) Evidence.zero
    have valid : ∀ (p : Fin 4) (i : Fin 6), i ≠ ix p →
        inputs.getD (coIndex p i) Evidence.zero ∈ coRoots p := by
      decide +kernel
    have eval : ∀ (p : Fin 4) (i : Fin 6), i ≠ ix p → ∀ r : Row,
        var i (coRow p r) = bit r (inputs.getD (coIndex p i) Evidence.zero) := by
      decide +kernel
    have eq : pull (coRow p) (var i) = observe col := funext (eval p i pin)
    exact Or.inl (eq.symm ▸ List.mem_map_of_mem (valid p i pin))

def embedAtlas (r : Atlas.Model.Row) : Row := ⟨r.val,by omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem atlasPoint : ∀ (p : Fin 5) (r : Atlas.Model.Row),
    observe (inputs.getD p.val Evidence.zero) (embedAtlas r) =
      Atlas.Model.observe (Atlas.B30.R.getD p.val 0) r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem atlasRoots : (coBase 0).map (pull embedAtlas) =
    Atlas.B30.R.map Atlas.Model.observe := by
  have source : coBase 0 = List.ofFn (fun j : Fin 5 =>
      observe (inputs.getD j.val Evidence.zero)) := rfl
  have dest : Atlas.B30.R.map Atlas.Model.observe = List.ofFn (fun j : Fin 5 =>
      Atlas.Model.observe (Atlas.B30.R.getD j.val 0)) := rfl
  rw [source,dest,List.map_ofFn]
  apply congrArg List.ofFn
  funext j r
  exact atlasPoint j r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem atlasBits : ∀ r : Atlas.Model.Row,
    atlasWord (embedAtlas r) = Atlas.Model.observe Atlas.B30.T r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pull_to_atlas {base bank : List (Wire Row)} {n : Nat}
    (h : Reach true base n bank) :
    Atlas.Model.Reach true (base.map (pull embedAtlas)) n (bank.map (pull embedAtlas)) := by
  induction h using Reach.ind with
  | start => exact Atlas.Model.Reach.start
  | @two n bank a b op h ha hb ih =>
    have stock : ∀ v ∈ bank, Available true (bank.map (pull embedAtlas)) (pull embedAtlas v) :=
      fun _ h => Or.inl (List.mem_map_of_mem h)
    have next := Atlas.Model.Reach.two op ih (pull_available stock ha) (pull_available stock hb)
    have eq : pull embedAtlas (combine op a b) = combine op (pull embedAtlas a) (pull embedAtlas b) :=
      pull_result embedAtlas ⟨op,a,b⟩
    rw [List.map_cons,eq]
    exact next

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem co_floor (p : Fin 4) {n : Nat} {B : List (Wire Row)}
    (run : Reach true (coBase p) n B) (hit : Available true B (coGoal p)) : 10 ≤ n := by
  by_cases side : p=0
  · subst p
    have pos : Available true B atlasWord := hit
    have proof := pull_to_atlas run
    rw [atlasRoots] at proof
    have filtered := pull_available (f:=embedAtlas) (fun _ k => Or.inl (List.mem_map_of_mem k)) pos
    rw [show pull embedAtlas atlasWord = Atlas.Model.observe Atlas.B30.T from funext atlasBits] at filtered
    exact Atlas.B30.low _ _ proof filtered
  · exact bound47 n B
      (by simpa only [coBase,coRoots,ite_eq_right side] using run)
      (by simpa only [coGoal,ite_eq_right side] using hit)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pin_budget (h : Valid rawBase gs) (out : Available true (stock rawBase gs) whole)
    (p : Fin 4) : 10 + dropCount (coRow p) (coBase p) gs ≤ gs.length := by
  obtain ⟨n,B,e,reach,cover⟩ := project_steps h Reach.start (fun _ m => coRoot p m)
  have output := pull_available cover out
  have eq : pull (coRow p) whole = coGoal p := funext (coTarget p)
  rw [eq] at output
  have lb := co_floor p reach output
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem raw_free_one : ∀ p : Fin 4, (1 : Fin 6) ≠ ix p := by decide +kernel

def fullRows : List Nat := [6, 0, 28, 6, 26, 6, 6, 14, 6, 22, 6, 38, 22, 19, 21, 19, 19, 21, 19, 0, 35, 19, 19, 35, 14, 11, 13, 11, 11, 13, 35, 11, 11, 0, 11, 35, 14, 11, 13, 11, 11, 13, 19, 11, 11, 19, 11, 0]
theorem cheap_pivot {g : Binary Row} (p : Fin 4) (read : Reads [var (ix p)] g) :
    Cheap (coRow p) (coBase p) g := by
  have constant {v} (h : SignedIn [var (ix p)] v) : Constant (pull (coRow p) v) := by
    simp only [SignedIn,List.mem_singleton] at h
    rcases h with rfl | z
    · exact ⟨coValue p, funext (var_co_value p)⟩
    · have eq : v = inv (var (ix p)) := (inv_inv' v).symm.trans (congrArg inv z)
      rw [eq]
      exact inv_constant (⟨coValue p, funext (var_co_value p)⟩)
  exact read.elim (fun h => Or.inl (constant h)) (fun h => Or.inr (Or.inl (constant h)))


theorem pivot_once (h : Valid rawBase gs) (out : Available true (stock rawBase gs) whole)
    (cap : gs.length≤11) (p : Fin 4) : tally (Reads [var (ix p)]) gs ≤ 1 := by
  have subset := tally_disjoint_le (P:=Reads [var (ix p)]) (Q:=fun _ => False)
    (L:=Cheap (coRow p) (coBase p)) (fun _ h => cheap_pivot p h)
    (fun _ => False.elim) (by simp) gs
  have lem : tally (Reads [var (ix p)]) gs ≤ dropCount (coRow p) (coBase p) gs := by
    simpa [tally,dropCount] using subset
  have k := pin_budget h out p
  omega
def samplePair (rows : List Nat) (p : Fin 4) (q : Fin 6) (b : Bool) : Row × Row :=
  let n := rows.getD (p.val * 12 + q.val * 2 + b.toNat) 0
  (Fin.ofNat 512 n, Fin.ofNat 512 (n + (1 <<< (ix p).val)))

def Apart (p : Fin 4) (l r : Row) : Prop :=
  ∀ i : Fin 6, i ≠ ix p → var i l = var i r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem full_pair : ∀ (p : Fin 4) (q : Fin 6) (b : Bool), q ≠ ix p →
    let w := samplePair fullRows p q b
    Apart p w.1 w.2 ∧ var q w.1 = b ∧ var q w.2 = b ∧ whole w.1 ≠ whole w.2 := by
  unfold Apart
  decide +kernel

theorem apart_agree {p : Fin 4} {l r : Row} (h : Apart p l r) :
    AgreesOutside l r [var (ix p)] rawBase := by
  intro a ha hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  apply h
  intro q
  exact hx (List.mem_singleton.mpr (congrArg var q))

def lonely (i : Fin 6) : Row := Fin.ofNat 512 (1 <<< i.val)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem var_zero : ∀ i : Fin 6, var i 0 = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem var_lonely : ∀ i : Fin 6, var i (lonely i) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem whole_raw : ∀ i : Fin 6, whole (lonely i) = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem not_signed_whole (L : List (Wire Row))
    (sub : ∀ a ∈ L, ∃ i : Fin 6, a = var i) : ¬ SignedIn L whole := by
  intro h
  rcases h with h | h
  · obtain ⟨i,e⟩ := sub _ h
    have bad := congrFun e (lonely i)
    simp [whole_raw,var_lonely] at bad
  · obtain ⟨i,e⟩ := sub _ h
    have bad := congrFun e 0
    have wzero : whole 0 = false := by decide
    simp [inv,wzero,var_zero] at bad

theorem not_signed_root (i : Fin 6) : ¬ SignedIn [var i] whole := by
  apply not_signed_whole
  intro a ha
  exact ⟨i,List.mem_singleton.mp ha⟩

theorem first_split {P : T → Prop} {steps : List T} (hit : ∃ g ∈ steps, P g) :
    ∃ pre g suf, steps = pre ++ g::suf ∧ P g ∧ ∀ a ∈ pre, ¬ P a := by
  classical
  induction steps with
  | nil => simp at hit
  | cons g gs ih =>
    by_cases already : P g
    · exact ⟨[],g,gs,rfl,already,by simp⟩
    · obtain ⟨w,haveW,hitW⟩ := hit
      rcases List.mem_cons.mp haveW with rfl | left
      · exact (already hitW).elim
      · obtain ⟨pre,g',suf,shape,hg,noPrev⟩ := ih ⟨w,left,hitW⟩
        refine ⟨g::pre,g',suf,?_,hg,?_⟩
        · rw [shape]
          rfl
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | q
          · exact already
          · exact noPrev _ q

theorem read_as_phase {B : List (Wire R)} {x : Wire R} :
    SignedIn B x ↔ ∃ w ∈ B, x = w ∨ x = inv w := by
  constructor
  · rintro (h | h)
    · exact ⟨x,h,Or.inl rfl⟩
    · exact ⟨inv x,h,Or.inr (inv_inv' x).symm⟩
  · rintro ⟨w,h,rfl|rfl⟩
    · exact Or.inl h
    · exact Or.inr ((inv_inv' w).symm ▸ h)

theorem signed_mono {K L : List (Wire R)} {v : Wire R}
    (subset : ∀ a ∈ K, a ∈ L) (h : SignedIn K v) : SignedIn L v :=
  h.elim (fun q => Or.inl (subset _ q)) (fun q => Or.inr (subset _ q))

theorem reads_mono {K L : List (Wire R)} {g : Binary R}
    (subset : ∀ a ∈ K, a ∈ L) (h : Reads K g) : Reads L g :=
  h.elim (fun q => Or.inl (signed_mono subset q)) (fun q => Or.inr (signed_mono subset q))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem raw_other {gs : List (Binary Row)} (h : Valid rawBase gs)
    (done : Available true (stock rawBase gs) whole) (cap : gs.length≤11)
    {g : Binary Row} (gm : g ∈ gs) (p : Fin 4) (q : Fin 6) (ne : q≠ix p)
    (hp : Reads [var (ix p)] g)
    {v : Wire Row} (side : v=g.left ∨ v=g.right) (how : v = var q ∨ v = inv (var q)) : False := by
  obtain ⟨pre,g',suf,split,hg,_⟩ := first_split (P:=fun x => x=g) ⟨g,gm,rfl⟩
  subst g'
  rw [split] at h done cap
  have count := pivot_once h done cap p
  obtain ⟨noPre,noSuf⟩ := read_once count hp
  rcases how with normal | negated
  · let w := samplePair fullRows p q g.disj
    obtain ⟨apart,left,right,hd⟩ := full_pair p q g.disj ne
    have center := saturated side (normal.symm ▸ left) (normal.symm ▸ right)
    exact hd (quiet_split h (apart_agree apart) noPre noSuf center done (not_signed_root _))
  · let w := samplePair fullRows p q (!g.disj)
    obtain ⟨apart,left,right,hd⟩ := full_pair p q (!g.disj) ne
    have a : v w.1 = g.disj := by simp [negated,inv,w,left]
    have b : v w.2 = g.disj := by simp [negated,inv,w,right]
    exact hd (quiet_split h (apart_agree apart) noPre noSuf (saturated side a b) done (not_signed_root _))


def Phase (u a : Wire R) : Prop := u=a ∨ u=inv a

theorem phase_in {B : List (Wire R)} {w v : Wire R} (ha : w ∈ B) (h : Phase v w) :
    SignedIn B v := read_as_phase.mpr ⟨w,ha,h⟩

theorem raw_other_read {gs : List (Binary Row)} (h : Valid rawBase gs)
    (done : Available true (stock rawBase gs) whole) (cap : gs.length≤11)
    {g : Binary Row} (gm : g ∈ gs) (p : Fin 4) (q : Fin 6) (ne : q≠ix p)
    (hp : Reads [var (ix p)] g) : ¬ Reads [var q] g := by
  intro hq
  rcases hq with l | r
  · have z := read_as_phase.mp l
    obtain ⟨v,ev,hv⟩ := z
    rw [List.mem_singleton.mp ev] at hv
    exact raw_other h done cap gm p q ne hp (Or.inl rfl) hv
  · have z := read_as_phase.mp r
    obtain ⟨v,ev,hv⟩ := z
    rw [List.mem_singleton.mp ev] at hv
    exact raw_other h done cap gm p q ne hp (Or.inr rfl) hv


theorem pivot_used (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) (p : Fin 4) :
    ∃ g ∈ gs, Reads [var (ix p)] g := by
  classical
  by_contra no
  obtain ⟨hapart,_,_,dif⟩ := full_pair p 1 true (raw_free_one p)
  have eq := quiet h (apart_agree hapart) (fun g mem use => no ⟨g,mem,use⟩)
  exact dif (literal_agrees eq.2 done (not_signed_root _))


theorem trace_eleven (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) :
    11 ≤ gs.length := by
  obtain ⟨g,m,use⟩ := pivot_used h done 0
  have k := tally_one (P:=Cheap (coRow 0) (coBase 0)) m (cheap_pivot 0 use)
  have lb := pin_budget h done 0
  change 1 ≤ dropCount (coRow 0) (coBase 0) gs at k
  omega
def signed (b : Bool) (f : Wire R) : Wire R := fun r => if b then !(f r) else f r

theorem signed_choice {a z : Wire R} (h : SignedIn [z] a) :
    ∃ b : Bool, a = signed b z := by
  obtain ⟨w,mem,phase⟩ := read_as_phase.mp h
  rw [List.mem_singleton.mp mem] at phase
  rcases phase with eq | eq
  · exact ⟨false,eq⟩
  · exact ⟨true,eq⟩

theorem sign_available {B : List (Wire R)} {z : Wire R} (b : Bool)
    (h : Available true B z) : Available true B (signed b z) := by
  cases b
  · exact h
  · exact avail_inv rfl h

theorem stock_contains {B : List (Wire R)} {xs : List (Binary R)} {v : Wire R}
    (m : v ∈ B) : v ∈ stock B xs := stock_mem.mpr (Or.inl m)

theorem replay_same {src dest : List (Wire R)} {xs : List (Binary R)}
    (h : Valid src xs) (supply : ∀ v ∈ src, Available true dest v) :
    Valid dest xs ∧ (∀ v ∈ stock src xs, Available true (stock dest xs) v) := by
  induction xs generalizing src dest with
  | nil => exact ⟨trivial,supply⟩
  | cons g xs ih =>
    obtain ⟨l,r,tail⟩ := h
    have carried : ∀ v ∈ g.result::src, Available true (g.result::dest) v := by
      intro v m
      rcases List.mem_cons.mp m with rfl|m
      · exact Or.inl List.mem_cons_self
      · exact available_cons _ (supply _ m)
    obtain ⟨tail,cov⟩ := ih tail carried
    exact ⟨⟨pull_available (f:=id) supply l,pull_available (f:=id) supply r,tail⟩,cov⟩

theorem result_fresh {pre suf : List (Binary Row)} {g : Binary Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) : ¬ Available true (stock rawBase pre) g.result := by
  intro duplicate
  have sp := (valid_append _ _ _).mp h
  have cover : ∀ v ∈ g.result :: stock rawBase pre, Available true (stock rawBase pre) v := by
    intro v m
    rcases List.mem_cons.mp m with rfl|m
    · exact duplicate
    · exact Or.inl m
  obtain ⟨valid,mapped⟩ := replay_same sp.2.2.2 cover
  rw [stock_append] at done
  have target := pull_available (f:=id) mapped done
  change Available true (stock (stock rawBase pre) suf) whole at target
  have lb := trace_eleven ((valid_append rawBase pre suf).mpr ⟨sp.1,valid⟩)
    (by simpa only [stock_append] using target)
  simp only [List.length_append,List.length_cons] at cap lb
  omega

theorem combine_phases {B : List (Wire R)} {z : Wire R} (mz : z ∈ B) (l r tag : Bool) :
    Available true B (combine tag (signed l z) (signed r z)) := by
  cases l <;> cases r
  · have eq : combine tag (signed false z) (signed false z) = z := by
      funext a; cases tag <;> simp [signed,combine]
    exact eq.symm ▸ Or.inl mz
  · exact Or.inr (Or.inl ⟨tag,by funext a; cases tag <;> cases hr : z a <;> simp [signed,combine,hr]⟩)
  · exact Or.inr (Or.inl ⟨tag,by funext a; cases tag <;> cases hr : z a <;> simp [signed,combine,hr]⟩)
  · have eq : combine tag (signed true z) (signed true z) = signed true z := by
      funext a; cases tag <;> simp [signed,combine]
    exact eq.symm ▸ sign_available true (Or.inl mz)


def Matched (g : Binary R) (a b : Wire R) : Prop :=
  (g.left=a ∧ g.right=b) ∨ (g.left=b ∧ g.right=a)

theorem matched_comm {g : Binary R} {a b : Wire R} (h : Matched g a b) : Matched g b a :=
  h.elim Or.inr Or.inl

theorem matched_side {g : Binary R} {a b : Wire R} (h : Matched g a b) :
    a = g.left ∨ a = g.right :=
  h.elim (fun e => Or.inl e.1.symm) (fun e => Or.inr e.2.symm)

theorem matched_res {g : Binary R} {a b : Wire R} (h : Matched g a b) :
    g.result = combine g.disj a b := by
  rcases h with ⟨l,r⟩|⟨l,r⟩
  · simp only [Binary.result,l,r]
  · funext x
    cases tag : g.disj <;> simp [Binary.result,combine,l,r,tag,Bool.or_comm,Bool.and_comm]

theorem matched_available {g : Binary R} {a b : Wire R} {bank : List (Wire R)}
    (h : Matched g a b) (l : Available true bank g.left) (r : Available true bank g.right) :
    Available true bank b :=
  h.elim (fun e=>e.2 ▸ r) (fun e=>e.1 ▸ l)

theorem matched_reads {g : Binary R} {a b : Wire R} {bank : List (Wire R)}
    (h : Matched g a b) (seen : SignedIn bank a) : Reads bank g :=
  h.elim (fun e=>Or.inl (e.1.symm ▸ seen)) (fun e=>Or.inr (e.2.symm ▸ seen))

theorem operand_choice {g : Binary R} {z : Wire R} (h : Reads [z] g) :
    ∃ (sg : Bool) (other : Wire R), Matched g (signed sg z) other := by
  rcases h with l|r
  · obtain ⟨b,eq⟩ := signed_choice l
    exact ⟨b,g.right,Or.inl ⟨eq,rfl⟩⟩
  · obtain ⟨b,eq⟩ := signed_choice r
    exact ⟨b,g.left,Or.inr ⟨rfl,eq⟩⟩

def controls : List (Wire Row) := List.ofFn fun p : Fin 4 => var (ix p)

theorem control_mem (p : Fin 4) : var (ix p) ∈ controls := List.mem_ofFn.mpr ⟨p,rfl⟩

theorem no_ctrl_signed {v : Wire Row}
    (no : ∀ p : Fin 4, ¬ SignedIn [var (ix p)] v) : ¬ SignedIn controls v := by
  intro h
  obtain ⟨r,m,sg⟩ := read_as_phase.mp h
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp m
  exact no _ (phase_in List.mem_cons_self sg)

theorem has_ctrl {g : Binary Row} (see : Reads controls g) :
    ∃ p : Fin 4, Reads [var (ix p)] g := by
  classical
  by_contra no
  push Not at no
  exact see.elim
    (no_ctrl_signed (fun p hs=>no p (Or.inl hs)))
    (no_ctrl_signed (fun p hs=>no p (Or.inr hs)))

theorem control_reads {g : Binary Row} {p : Fin 4} (single : Reads [var (ix p)] g) :
    Reads controls g :=
  reads_mono (fun _ m=>(List.mem_singleton.mp m).symm ▸ control_mem p) single

def testRows : List Nat := [56, 26, 28, 6, 49, 19, 21, 22, 41, 11, 13, 14, 25, 11, 13, 14]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem contr_ix : ∀ (p q : Fin 4), ix p = ix q → p=q := by decide +kernel

def testPair (p : Fin 4) (r : Row) : Row × Row :=
  let n := testRows.getD (p.val*4 + (r.val/2)%4) 0
  (Fin.ofNat 512 n, Fin.ofNat 512 (n + (1 <<< (ix p).val)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row_tests : ∀ (p : Fin 4) (r : Row),
    let s := testPair p r
    Apart p s.1 s.2 ∧ (whole s.1 ≠ whole s.2) ∧
      (var 1 s.1 = var 1 r ∧ var 1 s.2 = var 1 r) ∧
      (var 2 s.1 = var 2 r ∧ var 2 s.2 = var 2 r) := by
  unfold Apart
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem only_free : ∀ i : Fin 6, (∀ p : Fin 4, i ≠ ix p) → i = 1 ∨ i = 2 := by
  decide +kernel

theorem same_free (p : Fin 4) (r : Row) :
    AgreesOutside (testPair p r).1 r controls rawBase ∧
    AgreesOutside (testPair p r).2 r controls rawBase := by
  obtain ⟨_,_,b,c⟩ := row_tests p r
  have only {i : Fin 6} (avoid : var i ∉ controls) : i=1 ∨ i=2 := by
    apply only_free
    intro q e
    exact avoid (e.symm ▸ control_mem q)
  constructor
  · intro w wm outside
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp wm
    rcases only outside with rfl|rfl
    · exact b.1
    · exact c.1
  · intro w wm outside
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp wm
    rcases only outside with rfl|rfl
    · exact b.2
    · exact c.2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem trace_twelve (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) :
    12 ≤ gs.length := by
  by_contra! tooSmall
  have cap : gs.length≤11 := by omega
  obtain ⟨reader,mem,seen⟩ := pivot_used h done 0
  obtain ⟨pre,g,suf,shape,rd,noPre⟩ := first_split ⟨reader,mem,control_reads seen⟩
  subst gs
  obtain ⟨p,hp⟩ := has_ctrl rd
  have gmem : g ∈ pre ++ g::suf := List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ledger := (valid_append _ _ _).mp h
  obtain ⟨sig,w,operands⟩ := operand_choice hp
  have av := matched_available operands ledger.2.1 ledger.2.2.1
  have existsNew := result_fresh h done cap
  have wQuiet : ¬ SignedIn controls w := by
    apply no_ctrl_signed
    intro q asRaw
    by_cases eq : q=p
    · subst q
      obtain ⟨b,hw⟩ := signed_choice asRaw
      have inBase := combine_phases (stock_contains (xs:=pre) (raw_included (ix p))) sig b g.disj
      rw [← hw, ← matched_res operands] at inBase
      exact existsNew inBase
    · exact raw_other_read h done cap gmem p (ix q) (fun e=>eq (contr_ix q p e)) hp
        (matched_reads (matched_comm operands) asRaw)
  obtain ⟨avoidPre,avoidSuf⟩ := read_once (pivot_once h done cap p) hp
  have neverAbsorbs (r : Row) : w r ≠ g.disj := by
    intro equals
    have preserve := same_free p r
    have e₁ := literal_agrees (quiet ledger.1 preserve.1 noPre).2 av wQuiet
    have e₂ := literal_agrees (quiet ledger.1 preserve.2 noPre).2 av wQuiet
    obtain ⟨apart,dif,_,_⟩ := row_tests p r
    have sat := saturated (matched_side (matched_comm operands)) (e₁.trans equals) (e₂.trans equals)
    exact dif (quiet_split h (apart_agree apart) avoidPre avoidSuf sat done (not_signed_root _))
  have constant : Constant w := by
    refine ⟨!g.disj,funext (fun r=> ?_)⟩
    have hd := neverAbsorbs r
    cases ht : g.disj <;> cases hw : w r <;> simp_all
  apply existsNew
  rw [matched_res operands]
  exact from_constant _ (Or.inr constant)
    (sign_available _ (Or.inl (stock_contains (raw_included (ix p))))) av

def evalPoint (r : Row) (i : Fin 6) : Bool := var i r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem evalWhole : ∀ r : Row, projectedWire evalPoint sixTarget r = whole r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem highFloor : Low 12 sixTarget := by
  intro n program
  obtain ⟨bank,reach,out⟩ := projectedProgram evalPoint rawBase program
    (spent:=0) Reach.start (by
      rintro u ⟨i,rfl⟩
      exact Or.inl (raw_included i))
  rw [show projectedWire evalPoint sixTarget = whole from funext evalWhole] at out
  obtain ⟨gs,len,valid,stockEq⟩ := trace_of_reach reach
  rw [←stockEq] at out
  have deep := trace_twelve valid out
  omega

end PEqualNP.Outside.L_meta_49153.ReadFour

namespace PEqualNP.Outside.L_meta_49153
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sixWitness : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [12, 17]⟩], 18⟩

theorem basis : Monotone2 sixWitness := by simp [Monotone2, sixWitness]

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem correct : ∀ x : X, sixWitness.eval (List.ofFn x) = sixTarget x := by decide +kernel

end PEqualNP.Outside.L_meta_49153

open PEqualNP.Outside.L_meta_49153 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_49153 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132416 * 2 ^ 32 + 3900735616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132416 * 2 ^ 32 + 3900735616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  by_cases enough : 13 ≤ s
  · exact ⟨sixWitness, basis, enough, correct⟩
  obtain ⟨⟨gs,o⟩, fit, size, computes⟩ := h
  have hf : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa using (fit g hg).1, (fit g hg).2⟩
  change gs.length ≤ s at size
  exact ⟨⟨gs,o⟩, all_not_not ReadFour.highFloor gs o hf (by omega) computes, size, computes⟩

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38539.Model
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
abbrev Pool (raw : List Sig) (T : Sig) := { c : BoundPool // ValidPool true raw T c }

def checkedPool {raw T dom n} (slice : Slice true raw T dom n)
    (cs : List Choice) (c : BoundPool) (ok : materialize true raw cs dom n = some c) : Pool raw T :=
  ⟨c, materialize_sound slice ok⟩

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

end PEqualNP.Outside.L_meta_38539.Model
namespace PEqualNP.Outside.L_meta_38539
open PEqualNP.Outside.L_meta_38539.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
def R : List Sig := vars 11
def T : Sig := 0xaa88aa88aa88aa88
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xff00ff00ff00ff00, 1, 9)] (by decide +kernel)
end B1

namespace B2
def R : List Sig := vars 11
def T : Sig := 0xeecceecceecceecc
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 8, 9), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 1, 9)] (by decide +kernel)
end B2

namespace B3
def R : List Sig := vars 15
def T : Sig := 0xeac8eac8eac8eac8
theorem low : Lower true R T 4 := by
  exact lower_cubes_two (u := true) (j := 2) (r := 2) (s := 6) (L := 2)
    (z0 := 4) (o0 := 0) (z1 := 0) (o1 := 4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide)) (proper_of _ (by decide)) (proper_of _ (by decide))
    (lower_weaken B1.low (by decide))
    (lower_weaken B2.low (by decide))
end B3

namespace B4
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B4

namespace B5
def R : List Sig := vars 31
def T : Sig := 0xeac8e888eac8e888
def P : Nat → Bits
  | 0 => ((0xfffffdf81ffffc7 : BitVec 64) ++ (0xfe3ffff83cfccff9 : BitVec 64))
  | 1 => ((0xf07fffeffe07c7ff : BitVec 64) ++ (0xffc7ffc7cf27f3f6 : BitVec 64))
  | 2 => ((0xff80fe33fff807f8 : BitVec 64) ++ (0x3ff87807f3c73cc7 : BitVec 64))
  | 3 => ((0xffff0033fffff800 : BitVec 64) ++ (0x3fff8038f3f83f0b : BitVec 64))
  | 4 => ((0x3ffffffff : BitVec 64) ++ (0xc000003f03ffc00c : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x2212242480594942 : BitVec 64) ++ (0x4a08ca89184c4559 : BitVec 64))
  | 1 => ((0x412448191602828c : BitVec 64) ++ (0x94451512452192a6 : BitVec 64))
  | 2 => ((0xa40e9056aaa804d2 : BitVec 64) ++ (0x269060adb6c62cc6 : BitVec 64))
  | 3 => ((0x9481cab4d34d004 : BitVec 64) ++ (0x39260136ebb03b09 : BitVec 64))
  | 4 => ((0xce70e10ff1c72727 : BitVec 64) ++ (0x4463ff3ffc000 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
def w5 := combineObserved 0 w0 w1
def w6 := combineObserved 3 w5 w2
def v0 : Closed T 4 := closeState (raw := R) properPN 4 [w6, w0, w1, w3, w4]
  (fun _ => ([], [])) (by decide +kernel)
def w7 := combineObserved 1 w0 w1
def w8 := combineObserved 0 w7 w2
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w8, w3, w4]
  (fun _ => ([], [])) (by decide +kernel)
theorem s0 : Slice true R T 0xf0f00000f0f0 4 :=
  slice_correct (ms := fixRows 16 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p0 : Pool R T := checkedPool s0 []
  (0xf0f00000f0f0, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]) (by decide +kernel)
theorem s1 : Slice true R T 0xff000000ff00 4 :=
  slice_correct (ms := fixRows 16 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := checkedPool s1 []
  (0xff000000ff00, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]) (by decide +kernel)
theorem s2 : Slice true R T 0xffff0000ffff0000 4 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B3.low
def p2 : Pool R T := checkedPool s2 []
  (0xffff0000ffff0000, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]) (by decide +kernel)
def a0 : List Move := [swapRows 50, swapRows 16]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 4 :=
  ⟨v0.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v0.property⟩
def v2 : Closed T 5 := closeState (raw := R) properPN 5 [w5, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[v0, r0] ((((0x20001021c : Nat) >>> ((h % 13) * 3)) &&& 7))) (by decide +kernel)
def r1 : Closed T 4 :=
  ⟨v1.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v1.property⟩
def v3 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w7, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[v1, r1] ((((0x214019 : Nat) >>> ((h % 11) * 3)) &&& 7))) (by decide +kernel)
def w9 := combineObserved 2 w0 w1
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w9, w0, w1, w2, w3, w4]
  (fun _ => ([], [])) (by decide +kernel)
def r2 : Closed T 5 :=
  ⟨v4.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v4.property⟩
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1)] #[v4, r2, v2, v3] ((((((0x202c924820000 : Nat) <<< 64) ||| 0x200051001349248) >>> (((h / 14 + (((0x30804336010001 : Nat) >>> ((h % 14) * 4)) &&& 15)) % 41) * 3)) &&& 7))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 9, 13), (0xff00ff00ff00ff00, 5, 13), (0xffff0000ffff0000, 6, 22)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B5

namespace B6
def R : List Sig := vars 55
def T : Sig := 0xeaeae0e0e8e8a0a0
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 84, swapRows 67, swapRows 33]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B5.low
end B6

namespace B7
def R : List Sig := vars 15
def T : Sig := 0xeae8eae8eae8eae8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B7

namespace B8
def R : List Sig := vars 39
def T : Sig := 0xeaeaeaeae8e8e8e8
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 83]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B7.low
end B8

namespace B9
def R : List Sig := vars 59
def T : Sig := 0xeeaaee00ee88aa00
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 84, swapRows 66, swapRows 49, swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B5.low
end B9

namespace B10
def R : List Sig := vars 27
def T : Sig := 0xeeaaee00eeaaee00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 66, swapRows 49, swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B3.low
end B10

namespace B11
def R : List Sig := vars 43
def T : Sig := 0xeeaaeeaaee88ee88
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 83, swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B7.low
end B11

namespace B12
def R : List Sig := vars 31
def T : Sig := 0xeee0e8e0eee0e8e0
theorem low : Lower true R T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 16 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 3, 11), (0xffff0000ffff0000, 9, 25)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 3, 11), (0xffff0000ffff0000, 9, 25)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide
  rw [he] at h
  exact h
end B12

namespace B13
def R : List Sig := vars 47
def T : Sig := 0xeee0eee0eaa0eaa0
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 84, swapRows 49, swapRows 32]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B12.low
end B13

namespace B14
def R : List Sig := vars 15
def T : Sig := 0xe8a8e8a8e8a8e8a8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 6, 14)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 6, 14)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B14

namespace B15
def R : List Sig := vars 15
def T : Sig := 0xeaa0eaa0eaa0eaa0
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B14.low
end B15

namespace B16
def R : List Sig := vars 15
def T : Sig := 0xeee8eee8eee8eee8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B16

namespace B17
def R : List Sig := vars 31
def T : Sig := 0xeee8eaa0eee8eaa0
theorem low : Lower true R T 7 := by
  exact lower_cubes_two (u := true) (j := 4) (r := 3) (s := 19) (L := 5)
    (z0 := 16) (o0 := 0) (z1 := 0) (o1 := 16)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide)) (proper_of _ (by decide)) (proper_of _ (by decide))
    (lower_weaken B15.low (by decide))
    (lower_weaken B16.low (by decide))
end B17

namespace B18
def R : List Sig := vars 29
def T : Sig := 0xaaaaaaa0aaaaaaa0
theorem low : Lower true R T 3 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 4, 5), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9), (0xffff0000ffff0000, 1, 17)] (by decide +kernel)
end B18

namespace B19
def R : List Sig := vars 29
def T : Sig := 0xfffafff0fffafff0
theorem low : Lower true R T 3 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 16, 17), (0xf0f0f0f0f0f0f0f0, 0, 4), (0xff00ff00ff00ff00, 0, 8), (0xffff0000ffff0000, 1, 17)] (by decide +kernel)
end B19

namespace B20
def R : List Sig := vars 31
def T : Sig := 0xeeeaeee0eeeaeee0
theorem low : Lower true R T 5 := by
  exact lower_cubes_two (u := true) (j := 1) (r := 4) (s := 6) (L := 3)
    (z0 := 2) (o0 := 0) (z1 := 0) (o1 := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide)) (proper_of _ (by decide)) (proper_of _ (by decide))
    (lower_weaken B18.low (by decide))
    (lower_weaken B19.low (by decide))
end B20

namespace B21
def R : List Sig := vars 55
def T : Sig := 0xeeeeeeeeeeeeeaea
theorem low : Lower true R T 4 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 4, 6), (0xf0f0f0f0f0f0f0f0, 2, 6), (0xffff0000ffff0000, 2, 18), (0xffffffff00000000, 2, 34)] (by decide +kernel)
end B21

namespace B22
def R : List Sig := vars 59
def T : Sig := 0xeeeeeeeeeeeeeeaa
theorem low : Lower true R T 4 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 8, 10), (0xff00ff00ff00ff00, 2, 10), (0xffff0000ffff0000, 2, 18), (0xffffffff00000000, 2, 34)] (by decide +kernel)
end B22

namespace B23
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B23

namespace B24
def R : List Sig := vars 21
def T : Sig := 0xfafaa0a0fafaa0a0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B24

namespace B25
def R : List Sig := vars 25
def T : Sig := 0xffaaaa00ffaaaa00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50, swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B25

namespace B26
def R : List Sig := vars 28
def T : Sig := 0xfff0f000fff0f000
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B26

namespace B27
def R : List Sig := vars 44
def T : Sig := 0xfff0fff0f000f000
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49, swapRows 80]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B27

namespace B28
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B28

namespace B29
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
    (by decide +kernel) (proper_of _ (by decide)) B28.low
def p0 : Pool R T := checkedPool s0 []
  (0x5555555555555555, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := checkedPool s1 []
  (0xff00ff00ff00ff, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
theorem s2 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B23.low
def p2 : Pool R T := checkedPool s2 []
  (0x3333333333333333, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[] ((((0x1442120181102 : Nat) >>> (((h / 8 + (((0xc189 : Nat) >>> ((h % 8) * 2)) &&& 3)) % 25) * 2)) &&& 3))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B29

namespace B30
def R : List Sig := vars 29
def T : Sig := 0xfffafaa0fffafaa0
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B29.low
end B30

namespace B31
def R : List Sig := vars 11
def T : Sig := 0xffeeffeeffeeffee
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
end B31

namespace B32
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
def p0 : Pool R T := checkedPool s0 []
  (0xff00ff00ff00ff, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
theorem s1 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B23.low
def p1 : Pool R T := checkedPool s1 []
  (0x3333333333333333, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def w4 := combineObserved 1 w2 w1
def w5 := combineObserved 1 w3 w1
def w6 := combineObserved 1 w3 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w4, w5, w6]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B28.low
def p2 : Pool R T := checkedPool s2 []
  (0x5555555555555555, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def w7 := combineObserved 1 w3 w0
def a0 : List Move := [swapRows 32]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 :=
  ⟨v0.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v0.property⟩
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w7, w5]
  (fun h => chooseRoute #[(usePool p2), (usePool p1)] #[r0] ((((0x408 : Nat) >>> ((h % 6) * 2)) &&& 3))) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p3 : Pool R T := checkedPool s3 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xfefefefefefefefe, 0xff00ff00ff00ff00)]
  (0xf0f0f0f0f0f0f0f, 4, 2, [0xfe00fe00fe00fe, 0xeeeeeeeeeeeeeeee, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 2 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B31.low
def p4 : Pool R T := checkedPool s4 []
  (0xf0f0f0f0f0f0f0f0, 2, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def w8 := combineObserved 1 w0 w1
def w9 := combineObserved 1 w8 w2
def v2 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w9, w3]
  (fun _ => ([(usePool p0), (joinPools p3 p4)], [])) (by decide +kernel)
def w10 := combineObserved 2 w8 w3
def v3 : Closed T 4 := closeState (raw := R) properPN 4 [w10, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def p5 : Pool R T := checkedPool s3 []
  (0xf0f0f0f0f0f0f0f, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00]) (by decide +kernel)
def a1 : List Move := [swapRows 50]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 :=
  ⟨v3.val.map (movedWord a1.reverse), reflectState _ a1 a1ok v3.property⟩
def r2 : Closed T 4 :=
  ⟨v2.val.map (movedWord a1.reverse), reflectState _ a1 a1ok v2.property⟩
def a2 : List Move := [swapRows 48]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r3 : Closed T 4 :=
  ⟨v1.val.map (movedWord a2.reverse), reflectState _ a2 a2ok v1.property⟩
def a3 : List Move := [swapRows 49]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 4 :=
  ⟨v1.val.map (movedWord a3.reverse), reflectState _ a3 a3ok v1.property⟩
def a4 : List Move := [swapRows 50, swapRows 32]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 4 :=
  ⟨v1.val.map (movedWord a4.reverse), reflectState _ a4 a4ok v1.property⟩
def a5 : List Move := [swapRows 50, swapRows 33]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r6 : Closed T 4 :=
  ⟨v1.val.map (movedWord a5.reverse), reflectState _ a5 a5ok v1.property⟩
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w8, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v3, r1, v2, r2, r3, r4, r5, r6] ((((((0x3010054b961 : Nat) <<< 64) ||| 0xa20003000071280) >>> (((h / 8 + (((0x9e2031001 : Nat) >>> ((h % 8) * 5)) &&& 31)) % 27) * 4)) &&& 15))) (by decide +kernel)
def r7 : Closed T 5 :=
  ⟨v4.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v4.property⟩
def a6 : List Move := [swapRows 33]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r8 : Closed T 5 :=
  ⟨v4.val.map (movedWord a6.reverse), reflectState _ a6 a6ok v4.property⟩
def a7 : List Move := [swapRows 33, swapRows 48]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r9 : Closed T 5 :=
  ⟨v4.val.map (movedWord a7.reverse), reflectState _ a7 a7ok v4.property⟩
def r10 : Closed T 5 :=
  ⟨v4.val.map (movedWord a2.reverse), reflectState _ a2 a2ok v4.property⟩
def r11 : Closed T 5 :=
  ⟨v4.val.map (movedWord a3.reverse), reflectState _ a3 a3ok v4.property⟩
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v4, r7, r8, r9, r10, r11] ((((((0x13934200 : Nat) <<< 64) ||| 0x1316710020080035) >>> (((h / 8 + (((0x40b1830 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 25) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B32

namespace B33
def R : List Sig := vars 29
def T : Sig := 0xfffafaa0fffafaa0
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B32.low
end B33

namespace B34
def R : List Sig := vars 63
def T : Sig := 0xeeeaeee0eee8eaa0
def P : Nat → Bits
  | 0 => ((0x1ff83ffc1ffffffc : BitVec 64) ++ (0xfd27d9cd33dff84 : BitVec 64))
  | 1 => ((0xe0ffc1ffe0f03c03 : BitVec 64) ++ (0xfc2db2e72ccecc7f : BitVec 64))
  | 2 => ((0xfffe3fff003ff0 : BitVec 64) ++ (0xd0f1c307f0f30f2b : BitVec 64))
  | 3 => ((0xff00003fffffc003 : BitVec 64) ++ (0x233e03f83f03f053 : BitVec 64))
  | 4 => ((0xffffffc00000000c : BitVec 64) ++ (0x3c3ffc003ffc009c : BitVec 64))
  | 5 => ((0xf : BitVec 64) ++ (0xc03fffffc00000e0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x12802440194a525 : BitVec 64) ++ (0x4680148c41145584 : BitVec 64))
  | 1 => ((0x2058409c20a0a82f : BitVec 64) ++ (0xfd44b0a5044ccc7b : BitVec 64))
  | 2 => ((0x896b42b5a0112c0 : BitVec 64) ++ (0x714302b0a30a29 : BitVec 64))
  | 3 => ((0x5a0210339c4b0040 : BitVec 64) ++ (0x13a03503a03a052 : BitVec 64))
  | 4 => ((0x9ce739010802008a : BitVec 64) ++ (0xbabfe8003ff80084 : BitVec 64))
  | 5 => ((0x10042002108c230f : BitVec 64) ++ (0xfc3fffffc0000000 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 63 P N 0
def w1 := inputObserved 63 P N 1
def w2 := inputObserved 63 P N 2
def w3 := inputObserved 63 P N 3
def w4 := inputObserved 63 P N 4
def w5 := inputObserved 63 P N 5
theorem s0 : Slice true R T 0x444400004444 4 :=
  slice_correct (ms := fixRows 17 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
def p0 : Pool R T := checkedPool s0 []
  (0x444400004444, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s1 : Slice true R T 0xff0000 4 :=
  slice_correct (ms := fixRows 40 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := checkedPool s1 []
  (0xff0000, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w6 := combineObserved 1 w0 w2
def w7 := combineObserved 1 w0 w3
def w8 := combineObserved 1 w2 w3
def v0 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w6, w7, w8, w4, w5]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
def w9 := combineObserved 2 w6 w3
def v1 : Closed T 6 := closeState (raw := R) properPN 6 [w9, w0, w1, w2, w7, w4, w5]
  (fun _ => ([(usePool p1)], [])) (by decide +kernel)
def w10 := combineObserved 0 w0 w8
def v2 : Closed T 6 := closeState (raw := R) properPN 6 [w10, w1, w2, w7, w8, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
def w11 := combineObserved 3 w0 w8
def v3 : Closed T 6 := closeState (raw := R) properPN 6 [w11, w1, w2, w7, w8, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
def v4 : Closed T 6 := closeState (raw := R) properPN 6 [w9, w0, w1, w6, w8, w4, w5]
  (fun _ => ([(usePool p1)], [])) (by decide +kernel)
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w11, w0, w1, w2, w3, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
theorem s2 : Slice true R T 0xff00ff00ff00ff 7 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p2 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (3, 0xaaaaaaaaaaaaaaaa, 0xfffafffafffafffa), (0, 0xfffafffafffafffa, 0xffff0000ffff0000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffa0000fffa0000, 0x5550555055505550, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s3 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B21.low
def p3 : Pool R T := checkedPool s3 []
  (0xff00ff00ff00ff00, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w12 := combineObserved 1 w6 w3
def v6 : Closed T 6 := closeState (raw := R) properPN 6 [w11, w1, w2, w3, w12, w4, w5]
  (fun _ => ([(usePool p1), (joinPools p2 p3)], [])) (by decide +kernel)
def w13 := combineObserved 0 w1 w12
def v7 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w13, w2, w3, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
def p4 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa), (3, 0xf0f0f0f0f0f0f0f0, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 3, [0xf0a0f0a0f0a0f0a, 0xccc8ccc8ccc8ccc8, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f 7 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B9.low
def p5 : Pool R T := checkedPool s4 [(1, 0xfafafafafafafafa, 0xff00ff00ff00ff00), (0, 0xcccccccccccccccc, 0xfffafffafffafffa), (3, 0xff00ff00ff00ff00, 0xfffafffafffafffa)]
  (0xf0f0f0f0f0f0f0f, 7, 3, [0xfa00fa00fa00fa, 0xccc8ccc8ccc8ccc8, 0xfffafffafffafffa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s5 : Slice true R T 0xf0f0f0f0f0f0f0f0 4 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B22.low
def p6 : Pool R T := checkedPool s5 []
  (0xf0f0f0f0f0f0f0f0, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p7 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa), (0, 0xfffafffafffafffa, 0xffff0000ffff0000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffa0000fffa0000, 0xccc8ccc8ccc8ccc8, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p8 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa), (2, 0xfffafffafffafffa, 0xffff0000ffff0000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffa0000fffa, 0xccc8ccc8ccc8ccc8, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s6 : Slice true R T 0xcccccccc 7 :=
  slice_correct (ms := fixRows 32 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B33.low
def p9 : Pool R T := checkedPool s6 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (1, 0xfafafafafafafafa, 0xff00ff00ff00ff00)]
  (0xcccccccc, 7, 2, [0xfffafffafffafffa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p10 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa), (2, 0xfffafffafffafffa, 0xffffffff00000000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffafffa, 0xccc8ccc8ccc8ccc8, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v8 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w13, w2, w3, w12, w4, w5]
  (fun h => chooseRoute #[(usePool p0), (joinPools p4 p3), (joinPools p5 p6), (joinPools p7 p3), (joinPools p8 p3), (usePool p9), (joinPools p10 p3)] #[] ((((0x30458a20 : Nat) >>> ((h % 11) * 3)) &&& 7))) (by decide +kernel)
def p11 : Pool R T := checkedPool s4 [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (3, 0xff00ff00ff00ff00, 0xfffafffafffafffa), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)]
  (0xf0f0f0f0f0f0f0f, 7, 3, [0xccc8ccc8ccc8ccc8, 0xfa00fa00fa00fa, 0xffaaffaaffaaffaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v9 : Closed T 6 := closeState (raw := R) properPN 6 [w9, w0, w1, w2, w12, w4, w5]
  (fun _ => ([(usePool p1), (joinPools p11 p6)], [])) (by decide +kernel)
def p12 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xfffafffafffafffa, 0xffff0000ffff0000), (3, 0xaaaaaaaaaaaaaaaa, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 3, [0x5550555055505550, 0xfffa0000fffa0000, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p13 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xfffafffafffafffa, 0xffff0000ffff0000), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 3, [0xccc8ccc8ccc8ccc8, 0xfffa0000fffa0000, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s7 : Slice true R T 0xcccc 4 :=
  slice_correct (ms := fixRows 48 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B23.low
def p14 : Pool R T := checkedPool s7 []
  (0xcccc, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p15 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xfffafffafffafffa, 0xffff0000ffff0000), (2, 0xfffafffafffafffa, 0xffffffff00000000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffafffa, 0xfffa0000fffa0000, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w14 := combineObserved 0 w12 w4
def v10 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w14, w12, w5]
  (fun h => chooseRoute #[(joinPools p12 p3), (joinPools p13 p3), (usePool p0), (usePool p1), (usePool p14), (joinPools p15 p3)] #[] ((((0x58c2000001 : Nat) >>> ((h % 14) * 3)) &&& 7))) (by decide +kernel)
def p16 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (2, 0xfffafffafffafffa, 0xffff0000ffff0000), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 3, [0xccc8ccc8ccc8ccc8, 0xfffa0000fffa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p17 : Pool R T := checkedPool s6 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (1, 0xfafafafafafafafa, 0xff00ff00ff00ff00), (2, 0xfffafffafffafffa, 0xffff0000ffff0000)]
  (0xcccccccc, 7, 3, [0xfffa0000fffa, 0xfffafffafffafffa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p18 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (2, 0xfffafffafffafffa, 0xffff0000ffff0000), (2, 0xfffafffafffafffa, 0xffffffff00000000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffafffa, 0xfffa0000fffa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w15 := combineObserved 2 w12 w4
def v11 : Closed T 6 := closeState (raw := R) properPN 6 [w15, w0, w1, w2, w3, w12, w5]
  (fun h => chooseRoute #[(usePool p0), (joinPools p16 p3), (usePool p17), (usePool p1), (joinPools p18 p3)] #[] ((((0x40000ca : Nat) >>> ((h % 11) * 3)) &&& 7))) (by decide +kernel)
def w16 := combineObserved 2 w12 w5
def v12 : Closed T 6 := closeState (raw := R) properPN 6 [w16, w0, w1, w2, w3, w4]
  (fun _ => ([], [])) (by decide +kernel)
def p19 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (2, 0xfffafffafffafffa, 0xffffffff00000000), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 3, [0xccc8ccc8ccc8ccc8, 0xfffafffa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p20 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (2, 0xfffafffafffafffa, 0xffffffff00000000), (0, 0xfffafffafffafffa, 0xffff0000ffff0000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffa0000fffa0000, 0xfffafffa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p21 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (2, 0xfffafffafffafffa, 0xffffffff00000000), (2, 0xfffafffafffafffa, 0xffff0000ffff0000)]
  (0xff00ff00ff00ff, 7, 3, [0xfffa0000fffa, 0xfffafffa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v13 : Closed T 6 := closeState (raw := R) properPN 6 [w16, w0, w1, w2, w3, w12, w4]
  (fun h => chooseRoute #[(usePool p1), (joinPools p19 p3), (usePool p9), (joinPools p20 p3), (joinPools p21 p3)] #[] ((((0x1400b : Nat) >>> ((h % 8) * 3)) &&& 7))) (by decide +kernel)
def v14 : Closed T 6 := closeState (raw := R) properPN 6 [w11, w1, w2, w6, w3, w4, w5]
  (fun _ => ([(usePool p1)], [])) (by decide +kernel)
def p22 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 2, [0xccc8ccc8ccc8ccc8, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p23 : Pool R T := checkedPool s4 [(1, 0xfafafafafafafafa, 0xff00ff00ff00ff00), (0, 0xcccccccccccccccc, 0xfffafffafffafffa), (2, 0xfafafafafafafafa, 0xff00ff00ff00ff00)]
  (0xf0f0f0f0f0f0f0f, 7, 3, [0xfa00fa00fa00fa, 0xccc8ccc8ccc8ccc8, 0xfffafffafffafffa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v15 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w13, w2, w6, w3, w4, w5]
  (fun _ => ([(usePool p22), (joinPools p23 p6)], [])) (by decide +kernel)
def v16 : Closed T 6 := closeState (raw := R) properPN 6 [w16, w0, w1, w2, w6, w3, w4]
  (fun _ => ([], [])) (by decide +kernel)
def p24 : Pool R T := checkedPool s2 [(0, 0xaaaaaaaaaaaaaaaa, 0xffff0000ffff0000), (1, 0xaaaa0000aaaa0000, 0xf0f0f0f0f0f0f0f0), (0, 0xcccccccccccccccc, 0xfffafff0fffafff0)]
  (0xff00ff00ff00ff, 7, 3, [0xccc8ccc0ccc8ccc0, 0xfafaf0f0fafaf0f0, 0xaaaa0000aaaa0000, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s8 : Slice true R T 0xffffffff00000000 5 :=
  slice_correct (ms := fixRows 0 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B20.low
def p25 : Pool R T := checkedPool s8 []
  (0xffffffff00000000, 5, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w17 := combineObserved 0 w0 w4
def w18 := combineObserved 1 w17 w2
def w19 := combineObserved 1 w18 w3
def v17 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w19, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (joinPools p24 p3), (usePool p0), (usePool p25)] #[] ((((0x2012030 : Nat) >>> ((h % 18) * 2)) &&& 3))) (by decide +kernel)
def w20 := combineObserved 2 w18 w3
def v18 : Closed T 6 := closeState (raw := R) properPN 6 [w20, w0, w1, w2, w3, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
def w21 := combineObserved 3 w17 w8
def v19 : Closed T 6 := closeState (raw := R) properPN 6 [w21, w0, w1, w2, w3, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
def v20 : Closed T 6 := closeState (raw := R) properPN 6 [w11, w17, w1, w2, w3, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
def w22 := combineObserved 3 w0 w4
def w23 := combineObserved 1 w22 w2
def w24 := combineObserved 1 w23 w3
def v21 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w24, w4, w5]
  (fun _ => ([(usePool p1)], [])) (by decide +kernel)
def w25 := combineObserved 2 w23 w3
def v22 : Closed T 6 := closeState (raw := R) properPN 6 [w25, w0, w1, w2, w3, w4, w5]
  (fun _ => ([], [])) (by decide +kernel)
theorem s9 : Slice true R T 0xf0f0000 4 :=
  slice_correct (ms := fixRows 36 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p26 : Pool R T := checkedPool s9 []
  (0xf0f0000, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w26 := combineObserved 1 w22 w5
def v23 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w8, w4, w26]
  (fun h => chooseRoute #[(usePool p1), (usePool p26), (usePool p0)] #[] ((((0x20100 : Nat) >>> ((h % 10) * 2)) &&& 3))) (by decide +kernel)
def w27 := combineObserved 1 w2 w4
def v24 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w27, w26]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
def w28 := combineObserved 3 w22 w8
def v25 : Closed T 6 := closeState (raw := R) properPN 6 [w28, w0, w1, w2, w3, w4, w5]
  (fun _ => ([(usePool p0)], [])) (by decide +kernel)
def v26 : Closed T 6 := closeState (raw := R) properPN 6 [w11, w22, w1, w2, w3, w4, w5]
  (fun _ => ([(usePool p1)], [])) (by decide +kernel)
def p27 : Pool R T := checkedPool s4 [(0, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (3, 0xaaa0aaa0aaa0aaa0, 0xcccccccccccccccc)]
  (0xf0f0f0f0f0f0f0f, 7, 2, [0x444c444c444c444c, 0xaaa0aaa0aaa0aaa0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w29 := combineObserved 3 w10 w1
def v27 : Closed T 6 := closeState (raw := R) properPN 6 [w29, w0, w2, w3, w8, w4, w5]
  (fun _ => ([(usePool p27)], [])) (by decide +kernel)
def p28 : Pool R T := checkedPool s4 [(0, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (3, 0xaaa0aaa0aaa0aaa0, 0xffff0000ffff0000)]
  (0xf0f0f0f0f0f0f0f, 7, 2, [0x555f0000555f0000, 0xaaa0aaa0aaa0aaa0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w30 := combineObserved 3 w10 w4
def v28 : Closed T 6 := closeState (raw := R) properPN 6 [w30, w0, w1, w2, w3, w8, w5]
  (fun _ => ([(usePool p28)], [])) (by decide +kernel)
theorem s10 : Slice true R T 0xf0f0f0f00000000 4 :=
  slice_correct (ms := fixRows 4 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
def p29 : Pool R T := checkedPool s10 []
  (0xf0f0f0f00000000, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w31 := combineObserved 1 w10 w5
def v29 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w8, w4, w31]
  (fun _ => ([(usePool p29)], [])) (by decide +kernel)
def p30 : Pool R T := checkedPool s2 [(0, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (1, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (3, 0xaaa0aaa0aaa0aaa0, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 3, [0x555a555a555a555a, 0xfffafffafffafffa, 0xaaa0aaa0aaa0aaa0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v30 : Closed T 6 := closeState (raw := R) properPN 6 [w10, w1, w2, w3, w12, w4, w5]
  (fun _ => ([(joinPools p30 p3), (usePool p0)], [])) (by decide +kernel)
def p31 : Pool R T := checkedPool s4 [(1, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)]
  (0xf0f0f0f0f0f0f0f, 7, 2, [0xccc8ccc8ccc8ccc8, 0xfffafffafffafffa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v31 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w13, w2, w3, w8, w4, w5]
  (fun _ => ([(usePool p31)], [])) (by decide +kernel)
def v32 : Closed T 6 := closeState (raw := R) properPN 6 [w9, w0, w1, w2, w8, w4, w5]
  (fun _ => ([(usePool p1)], [])) (by decide +kernel)
def p32 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (0, 0xfffafffafffafffa, 0xffff0000ffff0000), (3, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0)]
  (0xff00ff00ff00ff, 7, 3, [0x5550555055505550, 0xfffa0000fffa0000, 0xfffafffafffafffa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p33 : Pool R T := checkedPool s4 [(1, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (0, 0xfffafffafffafffa, 0xffff0000ffff0000)]
  (0xf0f0f0f0f0f0f0f, 7, 2, [0xfffa0000fffa0000, 0xfffafffafffafffa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v33 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w8, w14, w5]
  (fun h => chooseRoute #[(usePool p0), (joinPools p32 p3), (usePool p33)] #[] ((((0x120 : Nat) >>> ((h % 7) * 2)) &&& 3))) (by decide +kernel)
def v34 : Closed T 6 := closeState (raw := R) properPN 6 [w16, w0, w1, w2, w3, w8, w4]
  (fun _ => ([(usePool p29)], [])) (by decide +kernel)
def w32 := combineObserved 2 w0 w8
def w33 := combineObserved 1 w32 w3
def v35 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w33, w8, w4, w5]
  (fun _ => ([(usePool p1)], [])) (by decide +kernel)
def p34 : Pool R T := checkedPool s2 [(2, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (1, 0xa000a000a000a, 0xfff0fff0fff0fff0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)]
  (0xff00ff00ff00ff, 7, 3, [0xccc8ccc8ccc8ccc8, 0xfffafffafffafffa, 0xa000a000a000a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v36 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w12, w4, w5]
  (fun h => chooseRoute #[(joinPools p34 p3), (usePool p0), (usePool p1), (usePool p25)] #[] ((((0x781 : Nat) >>> ((h % 7) * 2)) &&& 3))) (by decide +kernel)
def p35 : Pool R T := checkedPool s2 [(2, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (3, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0), (1, 0xa000a000a000a, 0x5550555055505550)]
  (0xff00ff00ff00ff, 7, 3, [0x555a555a555a555a, 0x5550555055505550, 0xa000a000a000a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v37 : Closed T 6 := closeState (raw := R) properPN 6 [w32, w11, w1, w2, w3, w4, w5]
  (fun _ => ([(joinPools p35 p3)], [])) (by decide +kernel)
def w34 := combineObserved 0 w8 w4
def w35 := combineObserved 1 w34 w5
def v38 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w8, w4, w35]
  (fun h => chooseRoute #[(usePool p1), (usePool p26), (usePool p0)] #[] ((((0x1002 : Nat) >>> ((h % 10) * 2)) &&& 3))) (by decide +kernel)
theorem s11 : Slice true R T 0xc0c0c0c 4 :=
  slice_correct (ms := fixRows 36 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p36 : Pool R T := checkedPool s11 []
  (0xc0c0c0c, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p37 : Pool R T := checkedPool s4 [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0xffaaffaaffaaffaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def a0 : List Move := [swapRows 50]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 6 :=
  ⟨v1.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v1.property⟩
def v39 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w6, w3, w7, w4, w5]
  (fun h => chooseRoute #[(usePool p36), (usePool p1), (usePool p37)] #[v1, r0, v0] ((((0x858405000201 : Nat) >>> ((h % 18) * 3)) &&& 7))) (by decide +kernel)
def p38 : Pool R T := checkedPool s6 [(1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00), (1, 0xff00ff00ff00ff00, 0xf0f0f0f0f0f0f0f0)]
  (0xcccccccc, 7, 2, [0xfff0fff0fff0fff0, 0xffaaffaaffaaffaa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r1 : Closed T 6 :=
  ⟨v4.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v4.property⟩
def v40 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w7, w8, w4, w5]
  (fun h => chooseRoute #[(usePool p37), (usePool p1), (usePool p0), (usePool p38), (usePool p36), (usePool p29)] #[r1, v3, v2, v0] ((((((0x2812300014534673 : Nat) <<< 64) ||| 0x1153004202190014) >>> (((h / 10 + (((0x5ab3502650 : Nat) >>> ((h % 10) * 4)) &&& 15)) % 33) * 4)) &&& 15))) (by decide +kernel)
def p39 : Pool R T := checkedPool s4 [(1, 0xfafafafafafafafa, 0xff00ff00ff00ff00)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0xfffafffafffafffa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p40 : Pool R T := checkedPool s2 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0)]
  (0xff00ff00ff00ff, 7, 1, [0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r2 : Closed T 6 :=
  ⟨v9.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v9.property⟩
def v41 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w12, w4, w5]
  (fun h => chooseRoute #[(usePool p9), (usePool p0), (usePool p39), (usePool p40), (usePool p1), (usePool p25)] #[v13, v12, v11, v9, r2, v5, v6, v8, v7, v10] ((((((0xc73914f00b04e04 : Nat) <<< 64) ||| 0x160028a15504d400) >>> (((h / 10 + (((0x2203018870082 : Nat) >>> ((h % 10) * 5)) &&& 31)) % 31) * 4)) &&& 15))) (by decide +kernel)
theorem s12 : Slice true R T 0x44444444 4 :=
  slice_correct (ms := fixRows 33 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B26.low
def p41 : Pool R T := checkedPool s12 []
  (0x44444444, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v42 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w6, w3, w12, w4, w5]
  (fun h => chooseRoute #[(usePool p0), (usePool p40), (usePool p1), (usePool p26), (usePool p41)] #[v16, r0, v9, v14, v15] ((((((0x806403950 : Nat) <<< 64) ||| 0x270001) >>> ((h % 25) * 4)) &&& 15))) (by decide +kernel)
def p42 : Pool R T := checkedPool s6 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (2, 0xfafafafafafafafa, 0xff00ff00ff00ff00)]
  (0xcccccccc, 7, 2, [0xfa00fa00fa00fa, 0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p43 : Pool R T := checkedPool s4 [(2, 0xfafafafafafafafa, 0xff00ff00ff00ff00)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0xfa00fa00fa00fa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v43 : Closed T 7 := closeState (raw := R) properPN 7 [w9, w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p36), (usePool p42), (usePool p0), (usePool p40), (usePool p25), (usePool p43)] #[v1, v9] ((((((0x403226001240 : Nat) <<< 64) ||| 0x5300560413738030) >>> (((h / 10 + (((0x8f12241 : Nat) >>> ((h % 10) * 3)) &&& 7)) % 28) * 4)) &&& 15))) (by decide +kernel)
def v44 : Closed T 7 := closeState (raw := R) properPN 7 [w9, w0, w1, w2, w6, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p36), (usePool p0), (usePool p1), (usePool p40)] #[v9, v4] ((((0x621002a00 : Nat) >>> ((h % 17) * 3)) &&& 7))) (by decide +kernel)
def p44 : Pool R T := checkedPool s2 [(1, 0xaa00aa00aa00aa, 0xf0f0f0f0f0f0f0f0)]
  (0xff00ff00ff00ff, 7, 1, [0xf0faf0faf0faf0fa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p45 : Pool R T := checkedPool s4 [(2, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0xaa00aa00aa00aa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def w36 := combineObserved 2 w0 w3
def w37 := combineObserved 1 w36 w2
def v45 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w37, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p44), (usePool p45), (usePool p41)] #[] ((((((0x260822 : Nat) <<< 64) ||| 0x1020641000000008) >>> (((h / 10 + (((0x1102b688 : Nat) >>> ((h % 10) * 3)) &&& 7)) % 30) * 3)) &&& 7))) (by decide +kernel)
theorem s13 : Slice true R T 0xffff0000ffff 6 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
def p46 : Pool R T := checkedPool s13 [(1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)]
  (0xffff0000ffff, 6, 1, [0xfff0fff0fff0fff0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s14 : Slice true R T 0xf0f00000f0f0000 5 :=
  slice_correct (ms := fixRows 4 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B11.low
def p47 : Pool R T := checkedPool s14 []
  (0xf0f00000f0f0000, 5, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v46 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w18, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (joinPools p46 p47), (usePool p26), (usePool p41)] #[v18, v17] ((((((0x420118100802 : Nat) <<< 64) ||| 0x143109060022001) >>> (((h / 13 + (((0x8000321015 : Nat) >>> ((h % 13) * 4)) &&& 15)) % 38) * 3)) &&& 7))) (by decide +kernel)
theorem s15 : Slice true R T 0xff000000ff0000 5 :=
  slice_correct (ms := fixRows 8 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B8.low
def p48 : Pool R T := checkedPool s15 []
  (0xff000000ff0000, 5, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v47 : Closed T 7 := closeState (raw := R) properPN 7 [w17, w0, w1, w2, w3, w8, w4, w5]
  (fun h => chooseRoute #[(joinPools p46 p47), (usePool p36), (joinPools p46 p48), (usePool p1), (usePool p0)] #[v20, v19, v17] ((((((0x2100 : Nat) <<< 64) ||| 0x804004600bd841e) >>> ((h % 28) * 3)) &&& 7))) (by decide +kernel)
def w38 := combineObserved 2 w0 w4
def w39 := combineObserved 3 w38 w1
def v48 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w39, w2, w3, w4, w5]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
def w40 := combineObserved 1 w38 w5
def v49 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w4, w40]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
def v50 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w23, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (joinPools p46 p47), (usePool p26), (usePool p14)] #[v22, v21] ((((((0x314107200 : Nat) <<< 64) ||| 0x20000020084b100) >>> (((h / 11 + (((0x40c08 : Nat) >>> ((h % 11) * 3)) &&& 7)) % 34) * 3)) &&& 7))) (by decide +kernel)
def r3 : Closed T 6 :=
  ⟨v24.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v24.property⟩
def v51 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w4, w26]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p26), (usePool p14)] #[v23, v24, r3] ((((((((((0x201 : Nat) <<< 64) ||| 0x6400012402180090) <<< 64) ||| 0x104800004800101) <<< 64) ||| 0x8000105608c1a008) >>> (((h / 22 + (((((0x250110 : Nat) <<< 64) ||| 0x4128230000002001) >>> ((h % 22) * 4)) &&& 15)) % 69) * 3)) &&& 7))) (by decide +kernel)
def v52 : Closed T 7 := closeState (raw := R) properPN 7 [w22, w0, w1, w2, w3, w8, w4, w5]
  (fun h => chooseRoute #[(joinPools p46 p47), (usePool p36), (joinPools p46 p48), (usePool p1), (usePool p0), (usePool p26)] #[v26, v25, v23, v21] ((((((((0x3 : Nat) <<< 64) ||| 0x40300300826000) <<< 64) ||| 0x4347030900541) >>> ((h % 34) * 4)) &&& 15))) (by decide +kernel)
def v53 : Closed T 7 := closeState (raw := R) properPN 7 [w22, w0, w1, w2, w3, w27, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p36)] #[v24] ((((0x4491003040 : Nat) >>> (((h / 8 + (((0x400204 : Nat) >>> ((h % 8) * 3)) &&& 7)) % 27) * 2)) &&& 3))) (by decide +kernel)
def p49 : Pool R T := checkedPool s4 [(0, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0xaaa0aaa0aaa0aaa0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r4 : Closed T 6 :=
  ⟨v2.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v2.property⟩
def v54 : Closed T 7 := closeState (raw := R) properPN 7 [w10, w0, w1, w2, w3, w8, w4, w5]
  (fun h => chooseRoute #[(usePool p36), (usePool p1), (usePool p0), (usePool p49)] #[v27, v5, v28, v30, v2, r4, v29] ((((0x23179401a0110856 : Nat) >>> (((h / 6 + (((0xf63a07 : Nat) >>> ((h % 6) * 4)) &&& 15)) % 16) * 4)) &&& 15))) (by decide +kernel)
def p50 : Pool R T := checkedPool s4 [(1, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0xfffafffafffafffa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r5 : Closed T 6 :=
  ⟨v32.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v32.property⟩
def v55 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w8, w12, w4, w5]
  (fun h => chooseRoute #[(usePool p36), (usePool p50), (usePool p0), (usePool p1)] #[v34, v32, r5, v6, v30, v31, v33] ((((0x705091633200a804 : Nat) >>> (((h / 4 + (((0xa0 : Nat) >>> ((h % 4) * 2)) &&& 3)) % 16) * 4)) &&& 15))) (by decide +kernel)
def p51 : Pool R T := checkedPool s4 [(2, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0xa000a000a000a, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r6 : Closed T 6 :=
  ⟨v35.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v35.property⟩
def v56 : Closed T 7 := closeState (raw := R) properPN 7 [w32, w0, w1, w2, w3, w8, w4, w5]
  (fun h => chooseRoute #[(usePool p0), (usePool p51)] #[v37, v36, v35, r6] ((((0x18008a10020 : Nat) >>> (((h / 2 + ((0 >>> ((h % 2) * 1)) &&& 1)) % 19) * 3)) &&& 7))) (by decide +kernel)
def p52 : Pool R T := checkedPool s6 [(1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (3, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0)]
  (0xcccccccc, 7, 2, [0x5550555055505550, 0xfff0fff0fff0fff0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p53 : Pool R T := checkedPool s4 [(3, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0)]
  (0xf0f0f0f0f0f0f0f, 7, 1, [0x5550555055505550, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p54 : Pool R T := checkedPool s2 [(3, 0xaaaaaaaaaaaaaaaa, 0xfff0fff0fff0fff0)]
  (0xff00ff00ff00ff, 7, 1, [0x5550555055505550, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r7 : Closed T 6 :=
  ⟨v14.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v14.property⟩
def v57 : Closed T 7 := closeState (raw := R) properPN 7 [w11, w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p52), (usePool p0), (usePool p1), (usePool p36), (usePool p25), (usePool p53), (usePool p54)] #[v26, v20, v14, r7, v6, v36] ((((((0x5224311c2142 : Nat) <<< 64) ||| 0x19017638a1b0020) >>> (((h / 10 + (((0x3c1d0248 : Nat) >>> ((h % 10) * 3)) &&& 7)) % 28) * 4)) &&& 15))) (by decide +kernel)
def r8 : Closed T 6 :=
  ⟨v3.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v3.property⟩
def v58 : Closed T 7 := closeState (raw := R) properPN 7 [w11, w0, w1, w2, w3, w8, w4, w5]
  (fun h => chooseRoute #[(usePool p36), (usePool p1), (usePool p0), (usePool p53)] #[v37, v6, v3, r8] ((((((0x300 : Nat) <<< 64) ||| 0xe0a006020a00008) >>> ((h % 26) * 3)) &&& 7))) (by decide +kernel)
def v59 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w34, w8, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p36), (usePool p26), (usePool p0)] #[v38] ((((0x802200000000003 : Nat) >>> ((h % 25) * 3)) &&& 7))) (by decide +kernel)
def w41 := combineObserved 3 w8 w4
def v60 : Closed T 7 := closeState (raw := R) properPN 7 [w41, w0, w1, w2, w3, w8, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p26), (usePool p0)] #[] ((((0x8010 : Nat) >>> ((h % 9) * 2)) &&& 3))) (by decide +kernel)
def w42 := combineObserved 3 w0 w27
def v61 : Closed T 7 := closeState (raw := R) properPN 7 [w42, w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p26)] #[] ((((((0x1400000001040 : Nat) <<< 64) ||| 0x14601000000) >>> ((h % 60) * 2)) &&& 3))) (by decide +kernel)
def p55 : Pool R T := checkedPool s6 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0)]
  (0xcccccccc, 7, 1, [0xfafafafafafafafa, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def p56 : Pool R T := checkedPool s4 []
  (0xf0f0f0f0f0f0f0f, 7, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r9 : Closed T 7 :=
  ⟨v40.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v40.property⟩
def v62 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w2, w6, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p0), (usePool p36), (usePool p40), (usePool p41), (usePool p55), (usePool p56), (usePool p26), (usePool p1)] #[v44, v43, v39, v42, v41, r9] ((((((((((((((((0x13 : Nat) <<< 64) ||| 0x8043020d00427027) <<< 64) ||| 0x301403901000006) <<< 64) ||| 0x740640303011100) <<< 64) ||| 0x3540014007500301) <<< 64) ||| 0x36b0402200004050) <<< 64) ||| 0x60a73c1374006) >>> (((h / 33 + (((((((0x24f7100 : Nat) <<< 64) ||| 0x4908408101e17800) <<< 64) ||| 0x88031040018840) >>> ((h % 33) * 5)) &&& 31)) % 100) * 4)) &&& 15))) (by decide +kernel)
def p57 : Pool R T := checkedPool s2 []
  (0xff00ff00ff00ff, 7, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v63 : Closed T 8 := closeState (raw := R) properPN 8 [w36, w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p36), (usePool p57), (usePool p41)] #[v45] ((((((((((((0x1043b0200 : Nat) <<< 64) ||| 0x209040000208000) <<< 64) ||| 0x2482400000492082) <<< 64) ||| 0x8412490c124304) <<< 64) ||| 0x8108048040249001) >>> (((h / 33 + (((((0x20590500a5610151 : Nat) <<< 64) ||| 0x70142114162110) >>> ((h % 33) * 4)) &&& 15)) % 99) * 3)) &&& 7))) (by decide +kernel)
def r10 : Closed T 7 :=
  ⟨v46.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v46.property⟩
def v64 : Closed T 8 := closeState (raw := R) properPN 8 [w17, w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p36), (usePool p41), (usePool p26)] #[v47, v46, r10] ((((((((((((0x20000021804 : Nat) <<< 64) ||| 0x8a08000248018) <<< 64) ||| 0x18040000c480090) <<< 64) ||| 0x49e5820820824924) <<< 64) ||| 0x124804c209200401) >>> (((h / 34 + (((((((0x3 : Nat) <<< 64) ||| 0x30000010101001) <<< 64) ||| 0x202113000081718) >>> ((h % 34) * 4)) &&& 15)) % 101) * 3)) &&& 7))) (by decide +kernel)
def w43 := combineObserved 1 w0 w4
def v65 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w2, w3, w4, w43, w5]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s16 : Slice true R T 0xcccccccc 6 :=
  slice_correct (ms := fixRows 32 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B30.low
def p58 : Pool R T := checkedPool s16 []
  (0xcccccccc, 6, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s17 : Slice true R T 0xffffffff 7 :=
  slice_correct (ms := fixRows 32 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B17.low
def p59 : Pool R T := checkedPool s17 []
  (0xffffffff, 7, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v66 : Closed T 8 := closeState (raw := R) properPN 8 [w38, w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p58), (usePool p26), (usePool p36), (usePool p59)] #[v48, v49] ((((((((((((0xe0000100000800 : Nat) <<< 64) ||| 0x8000000000001008) <<< 64) ||| 0x82000010040413) <<< 64) ||| 0x4000000020000004) <<< 64) ||| 0x30008053040) >>> (((h / 37 + (((((0x40 : Nat) <<< 64) ||| 0x5001410c0204c04) >>> ((h % 37) * 2)) &&& 3)) % 109) * 3)) &&& 7))) (by decide +kernel)
def r11 : Closed T 7 :=
  ⟨v53.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v53.property⟩
def r12 : Closed T 7 :=
  ⟨v50.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v50.property⟩
def v67 : Closed T 8 := closeState (raw := R) properPN 8 [w22, w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p36), (usePool p14), (usePool p59), (usePool p26)] #[v52, v53, r11, v50, r12, v51] ((((((((((((((((0x1100101010 : Nat) <<< 64) ||| 0x60001101100010a0) <<< 64) ||| 0x101103000001011) <<< 64) ||| 0x9000000010101010) <<< 64) ||| 0x3001000001015110) <<< 64) ||| 0x8b3011000000110) <<< 64) ||| 0x1110100000704121) >>> (((h / 35 + (((((((0x41 : Nat) <<< 64) ||| 0x5203800140011013) <<< 64) ||| 0x170000001520000) >>> ((h % 35) * 4)) &&& 15)) % 107) * 4)) &&& 15))) (by decide +kernel)
def p60 : Pool R T := checkedPool s6 [(1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)]
  (0xcccccccc, 7, 1, [0xfff0fff0fff0fff0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
theorem s18 : Slice true R T 0xcc00cc 4 :=
  slice_correct (ms := fixRows 40 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
def p61 : Pool R T := checkedPool s18 []
  (0xcc00cc, 4, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v68 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w2, w3, w8, w4, w5]
  (fun h => chooseRoute #[(usePool p60), (usePool p36), (usePool p56), (usePool p1), (usePool p57), (usePool p0), (usePool p61), (usePool p26)] #[v56, v60, v58, v57, v52, v54, v47, v59, v55, v41, v40, r9] ((((((((((((((((((((((0x402 : Nat) <<< 64) ||| 0x3c631844018c8018) <<< 64) ||| 0xc60385000b423080) <<< 64) ||| 0x65010600806b1c4a) <<< 64) ||| 0x8d801846300c03) <<< 64) ||| 0x2301442200a70) <<< 64) ||| 0x702403001c198) <<< 64) ||| 0xc80016030a800280) <<< 64) ||| 0x4308420048633000) <<< 64) ||| 0x30842000c6010c20) >>> (((h / 38 + (((((((0x53852044c04108 : Nat) <<< 64) ||| 0xe008c46004460012) <<< 64) ||| 0xe008403002138024) >>> ((h % 38) * 5)) &&& 31)) % 118) * 5)) &&& 31))) (by decide +kernel)
def p62 : Pool R T := checkedPool s6 [(1, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000)]
  (0xcccccccc, 7, 1, [0xfffff0f0fffff0f0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def v69 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w2, w3, w4, w27, w5]
  (fun h => chooseRoute #[(usePool p0), (usePool p26), (usePool p36), (usePool p1), (usePool p62)] #[v53, v61] ((((((((((((((0x6 : Nat) <<< 64) ||| 0xd86c36066186d861) <<< 64) ||| 0xa6db11b6d861b0c0) <<< 64) ||| 0x2006dd4186db11b0) <<< 64) ||| 0x186d84186db60) <<< 64) ||| 0x6186c301b09b003) >>> (((h / 36 + (((((((0xbf00 : Nat) <<< 64) ||| 0xb02110001003010) <<< 64) ||| 0x210100f000000100) >>> ((h % 36) * 4)) &&& 15)) % 108) * 3)) &&& 7))) (by decide +kernel)
def w44 := combineObserved 3 w3 w4
def v70 : Closed T 8 := closeState (raw := R) properPN 8 [w44, w0, w1, w2, w3, w4, w5]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
def p63 : Pool R T := checkedPool s6 []
  (0xcccccccc, 7, 0, [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]) (by decide +kernel)
def r13 : Closed T 8 :=
  ⟨v63.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v63.property⟩
def r14 : Closed T 8 :=
  ⟨v70.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v70.property⟩
def r15 : Closed T 8 :=
  ⟨v62.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v62.property⟩
def r16 : Closed T 8 :=
  ⟨v69.val.map (movedWord a0.reverse), reflectState _ a0 a0ok v69.property⟩
def v71 : Closed T 9 := closeState (raw := R) properPN 9 [w0, w1, w2, w3, w4, w5]
  (fun h => chooseRoute #[(usePool p63), (usePool p58), (usePool p56), (usePool p57), (usePool p59)] #[v66, v63, r13, v70, r14, v67, v64, v62, r15, v68, v65, v69, r16] ((((((((((((((0x23 : Nat) <<< 64) ||| 0x3d6488464120002) <<< 64) ||| 0x34402284100c8608) <<< 64) ||| 0x464700a110860000) <<< 64) ||| 0x2010030100c1902) <<< 64) ||| 0x4004009008e1) >>> (((h / 20 + (((((0x623c00157 : Nat) <<< 64) ||| 0x3114001acc129002) >>> ((h % 20) * 5)) &&& 31)) % 66) * 5)) &&& 31))) (by decide +kernel)
theorem low : Lower true R T 10 :=
  fromClosed v71 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 4, 5), (0xcccccccccccccccc, 12, 14), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9), (0xffff0000ffff0000, 3, 19), (0xffffffff00000000, 6, 38)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B34

def fullRoots : List Sig := inputs
def fullWord : Sig := 0xeeeaeee0eee8eaa0
theorem fullBound : Lower true fullRoots fullWord 10 := by
  intro p bank h hit
  have hlow := B34.low p bank h hit
  omega
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373984 * 2 ^ 32 + 4008241824)
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_38539.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [6, 12]⟩, ⟨.and, [14, 15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 16⟩ (List.ofFn x) = posted x := by decide +kernel

theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_38539

open PEqualNP.Outside.L_meta_38539 in
theorem PEqualNP.Outside.L_meta_38539 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve fullBound

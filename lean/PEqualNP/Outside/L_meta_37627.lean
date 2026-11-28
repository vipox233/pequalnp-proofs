import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37627.Model
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

def inputChunks (xs : List Nat) : Nat := xs.foldr (fun w r => w ||| (r <<< 60)) 0
def inputs : List Sig := [(BitVec.ofNat 512 (inputChunks [0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaa])),(BitVec.ofNat 512 (inputChunks [0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xccccccccccccccc, 0xcccccccc])),(BitVec.ofNat 512 (inputChunks [0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0])),(BitVec.ofNat 512 (inputChunks [0xf00ff00ff00ff00, 0xff00ff00ff00f, 0xff00ff00ff00ff, 0xff00ff00ff00ff0, 0xf00ff00ff00ff00, 0xff00ff00ff00f, 0xff00ff00ff00ff, 0xff00ff00ff00ff0, 0xff00ff00])),(BitVec.ofNat 512 (inputChunks [0xfff0000ffff0000, 0xff0000ffff0000f, 0xf0000ffff0000ff, 0xffff0000fff, 0xffff0000ffff, 0xffff0000ffff0, 0xffff0000ffff00, 0xffff0000ffff000, 0xffff0000])),(BitVec.ofNat 512 (inputChunks [0xfffffff00000000, 0xffffff00000000f, 0xfffff00000000ff, 0xffff00000000fff, 0xfff00000000ffff, 0xff00000000fffff, 0xf00000000ffffff, 0xfffffff, 0xffffffff])),(BitVec.ofNat 512 (inputChunks [0x0, 0xffffffffffffff0, 0xff, 0xffffffffffff000, 0xffff, 0xffffffffff00000, 0xffffff, 0xffffffff0000000, 0xffffffff])),(BitVec.ofNat 512 (inputChunks [0x0, 0x0, 0xfffffffffffff00, 0xfffffffffffffff, 0xffff, 0x0, 0xfffffffff000000, 0xfffffffffffffff, 0xffffffff])),(BitVec.ofNat 512 (inputChunks [0x0, 0x0, 0x0, 0x0, 0xfffffffffff0000, 0xfffffffffffffff, 0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff]))]
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
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def eqF (a b : Sig) : Bool := Nat.beq a.toNat b.toNat
theorem eqF_eq (a b : Sig) : eqF a b = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp [eqF,BitVec.toNat_inj]
noncomputable def anyEq (m d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || ih) l
theorem anyEq_eq (m d : Sig) (l : List Sig) :
    anyEq m d l = (l.map (masked d)).any (fun v => v==m) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || anyEq m d vs) = _
    rw [ih,eqF_eq,List.map_cons,List.any_cons]
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d || anyEq (masked d a) d pool ||
    (u && anyEq (masked d (neg a)) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  simp only [availF,availableB,eqF_eq,anyEq_eq]
noncomputable def allF (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => availF u d pool v && ih) l
theorem allF_eq (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) :
    allF u d pool l = l.all (availableB u d pool) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (availF u d pool v && allF u d pool vs) = _
    rw [ih,availF_eq,List.all_cons]
noncomputable def countF (d : Sig) (l : List Sig) : Nat :=
  @List.rec Sig (fun _ => Nat) 0
    (fun v _ ih => cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ ih) ih) l
theorem countF_eq (d : Sig) (l : List Sig) : countF d l = l.countP (isMaskedConstant d) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ (countF d vs)) (countF d vs) = _
    rw [ih,eqF_eq,eqF_eq,List.countP_cons]
    change _ = _ + if (masked d v == zero || masked d v == d) = true then 1 else 0
    cases (masked d v == zero || masked d v == d) <;> rfl
noncomputable def scalarPoolCutF (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  allF u c.domain c.wires rest &&
    cond (availF u c.domain c.wires (choiceVal op))
      (Nat.blt (k+c.paid) (c.bound+countF c.domain (choiceVal op::rest)))
      (Nat.blt (k+c.paid+1) (c.bound+countF c.domain (choiceVal op::rest)) &&
        (allowedB u op.1 && (availF u c.domain c.wires op.2.1 && availF u c.domain c.wires op.2.2)))
theorem scalarPoolCutF_ok {u : Bool} {c : BoundPool} {k : Nat} {rest : List Sig} {op : Choice}
    (h : scalarPoolCutF u c k rest op = true) : scalarPoolCut u c k rest op = true := by
  simp only [scalarPoolCutF,allF_eq,availF_eq,countF_eq,Bool.and_eq_true] at h
  obtain ⟨hall,hc⟩ := h
  simp only [scalarPoolCut,choiceOK,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  cases hz : availableB u c.domain c.wires (choiceVal op)
  · rw [hz] at hc
    simp only [cond_false,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inr hc.2⟩
    simpa using hc.1
  · rw [hz] at hc
    simp only [cond_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inl (by simp)⟩
    simpa using hc
noncomputable def anyP (f : BoundPool → Bool) (l : List BoundPool) : Bool :=
  @List.rec BoundPool (fun _ => Bool) false (fun p _ ih => f p || ih) l
theorem anyP_eq (f : BoundPool → Bool) (l : List BoundPool) : anyP f l = l.any f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v || anyP f vs) = _
    rw [ih,List.any_cons]
noncomputable def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  anyP (fun p => scalarPoolCutF u p k rest op) pools ||
    (links (keySet (choiceVal op::rest))).any (sameWords (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd (scalarPoolCutF_ok ok)
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
noncomputable def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

noncomputable def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
theorem or_ones_and {n : Nat} (x y z : BitVec n) (h : (x &&& y) ||| z = BitVec.allOnes n) :
    x ||| z = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun w => w.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hi, decide_true] at hb ⊢
  cases hx : x.getLsbD i <;> simp_all
theorem takeTwo_right (c : Cov) (a b : Bits) :
    takeTwo c a b = takeOne c b &&& ~~~((c.2.1 &&& a) ||| (c.2.2 &&& (a &&& b))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo, takeOne, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
def quickPair (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152
  else Nat.blt c.1 (c.2.1+1) &&
    (((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152) &&
     ((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152))
theorem evalMove_cov {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) ≠ BitVec.allOnes 152) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else if (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) != BitVec.allOnes 152 then true else _) = true
  by_cases hlen : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap
  · rw [if_pos hlen]
  · rw [if_neg hlen,if_pos (bne_iff_ne.mpr h)]
theorem evalMove_long {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else _) = true
  rw [if_pos h]
theorem quickPair_ok {c : NodeContext} {a b : Decor} {op : Nat} (h : quickPair c a b op = true) :
    testPair c a b op = true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  unfold quickPair at h
  simp only [testPair,Bool.and_eq_true]
  split at h
  next hlt =>
    have hl : cap < n := by simpa using hlt
    have hf := bne_iff_ne.mp h
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_long (ka:=true) (kb:=false) (by simp <;> omega)⟩,
      evalMove_long (ka:=false) (kb:=true) (by simp <;> omega)⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
  next =>
    simp only [Bool.and_eq_true,Nat.blt_eq,bne_iff_ne,ne_eq] at h
    obtain ⟨hl,hb,ha⟩ := h
    have hf : (takeTwo cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ||| column (!cov.2) (dbin op a b).2) ≠ BitVec.allOnes 152 := by
      intro e
      rw [takeTwo_right] at e
      exact hb (or_ones_and _ _ _ e)
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_cov (ka:=true) (kb:=false) hb⟩,
      evalMove_cov (ka:=false) (kb:=true) ha⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
theorem pairQ {c : NodeContext} {a b : Decor} {op : Nat}
    (h : (quickPair c a b op || testPair c a b op) = true) : testPair c a b op = true := by
  rcases Bool.or_eq_true_iff.mp h with q | t
  · exact quickPair_ok q
  · exact t
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (fun op => quickPair ctx a b op || testPair ctx a b op))
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => pairQ (h.1 b bm d (opsOf_mem hd))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => pairQ (h.1 a haTail d (opsOf_mem hd))
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

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

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

end PEqualNP.Outside.L_meta_37627.Model

namespace PEqualNP.Outside.L_meta_37627
open PEqualNP.Outside.L_meta_37627.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

abbrev Catalog := List (Sig × Nat)
abbrev Hints := Nat → Nat → List Nat

def purchases : Nat → Nat → List Sig → List Choice
  | 0, _, _ => []
  | n+1, code, bank =>
    let a := bank.getD (code &&& 15) zero
    let b := bank.getD ((code >>> 4) &&& 15) zero
    let x := if code.testBit 10 then neg a else a
    let y := if code.testBit 11 then neg b else b
    let v : Choice := ((code >>> 8) &&& 3, x, y)
    v :: purchases n (code >>> 12) (bank ++ [choiceVal v])

def fromHint (raw : List Sig) (ds : Catalog) (q : Nat) : Option BoundPool := do
  let desc ← ds[q &&& 255]?
  let cs := purchases ((q >>> 8) &&& 7) (q >>> 11) raw
  let ws ← makePool true desc.1 raw cs
  return ⟨desc.1,desc.2, cs.length,ws⟩

def SafeCatalog (g : Atlas) (ds : Catalog) : Prop :=
  ∀ p ∈ ds, Slice true (roots g) (target g) p.1 p.2

theorem safeNil (g : Atlas) : SafeCatalog g [] := by
  intro p hp
  simp at hp

theorem safeCons {g ds p} (one : Slice true (roots g) (target g) p.1 p.2) (tail : SafeCatalog g ds) :
    SafeCatalog g (p::ds) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | h
  · exact one
  · exact tail v h

def pools (g : Atlas) (ds : Catalog) (hs : Hints) (k i : Nat) :=
  (hs k i).filterMap (fromHint (roots g) ds)

theorem pools_valid {g ds} (safe : SafeCatalog g ds) (hs : Hints) (k i : Nat) :
    ∀ p ∈ pools g ds hs k i, ValidPool true (roots g) (target g) p := by
  intro p hp
  obtain ⟨q, _, hq⟩ := List.mem_filterMap.mp hp
  cases hd : ds[q &&& 255]? with
  | none => simp [fromHint, hd] at hq
  | some v =>
    let cs := purchases ((q >>> 8) &&& 7) (q >>> 11) (roots g)
    cases hm : makePool true v.1 (roots g) cs with
    | none => simp [fromHint, hd, ←show purchases ((q >>> 8) &&& 7) (q >>> 11) (roots g) = cs from rfl, cs] at hm; simp [fromHint, hd, hm] at hq
    | some bank =>
      have eq : (⟨v.1,v.2,cs.length,bank⟩ : BoundPool) = p := by
        simpa [fromHint, hd, ←show purchases ((q >>> 8) &&& 7) (q >>> 11) (roots g) = cs from rfl, hm, cs] using hq
      rw [←eq]
      exact build_valid (safe v (List.mem_of_getElem? hd)) cs hm

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let i := locate g k tag
  if i < count g k then [vals g k i] else []

noncomputable def checkRow (g : Atlas) (ds : Catalog) (hs : Hints) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  decide vs.Nodup && !vs.contains (target g) &&
    testAll (k,ws.length,ws,preCov true ws,pools g ds hs k i,links g (k-1)) ws

def Ready (g : Atlas) (ds : Catalog) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧ SafeCatalog g ds

theorem checked {g ds hs r s} (ready : Ready g ds r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g ds hs l i=true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hk : k=0
    · subst k
      intro n cap run
      have : n=0 := by omega
      subst n
      have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
      exact h.1.2 (List.mem_toFinset.mp hm)
    apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 (pools_valid ready.2.2 hs k i) _ h.2
    · intro a ha
      exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
    · intro tag xs hx
      simp only [links] at hx
      split at hx
      next le =>
        obtain rfl := List.mem_singleton.mp hx
        exact ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le
      next => simp at hx

def Complete (g : Atlas) (ds : Catalog) (hs : Hints) :=
  ∀ k ≤ top g, ∀ i < count g k, checkRow g ds hs k i=true

theorem frozen {g ds hs p n} (ready : Ready g ds p n) (complete : Complete g ds hs)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem lowerNeg {roots T k} (low : Lower true roots T k) : Lower true roots (neg T) k := by
  intro p bank hr hav
  rw [obs_neg] at hav
  have h := avail_inv (u:=true) rfl hav
  rw [inv_inv'] at h
  exact low p bank hr h

def identifyRows (i j : Nat) (sign : Bool) : List Move :=
  let a := inputs.getD i zero
  let b := if sign then neg (inputs.getD j zero) else inputs.getD j zero
  [(neg a &&& b, a &&& neg b, Fin.ofNat 512 (1 <<< i))]

def freeSigned (base : List Sig) (w : Sig) :=
  freeWord base w || freeWord base (neg w)

theorem signedFree {base w} (h : freeSigned base w=true) :
    Available true (base.map observe) (observe w) := by
  simp only [freeSigned,Bool.or_eq_true] at h
  rcases h with h | h
  · exact freeWord_ok h
  · have hx := avail_inv (u:=true) rfl (freeWord_ok (u:=true) h)
    simpa only [obs_neg,inv_inv'] using hx

def signedMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeSigned base (movedWord ms a))

theorem signedMapCorrect {ms raw T base G} (ok : signedMap ms raw T base G=true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available true (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [signedMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => signedFree (ok.2 a ha)⟩

theorem signedSlice {ms raw T base G L d} (ok : signedMap ms raw T base G=true)
    (all : movedWord ms d=one) (pg : proper G) (low : Lower true base G L) :
    Slice true raw T d L := by
  obtain ⟨eq,supp⟩ := signedMapCorrect ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper pg
  · rw [obs]
    exact low

def flipInput (j : Nat) : Move :=
  let a := inputs.getD j zero
  (neg a,a,Fin.ofNat 512 (1 <<< j))

def field (ws : Nat → Nat) (pos width : Nat) : Nat :=
  let r := pos % 60
  let low := (ws (pos / 60)) >>> r
  let value := if r+width ≤ 60 then low else low ||| ((ws (pos/60+1)) <<< (60-r))
  value &&& ((1 <<< width)-1)

def hashRow (n b spec tag : Nat) : Nat :=
  if n<2 then 0 else if spec % 2 = 1 then spec / 2 else
   (tag / b % n + (spec / 2) * (1+(tag/(b*n) % (n-1)))) % n

def repeatWord (v : Nat) : Sig := BitVec.ofNat 512 (v * ((2 ^ 512 - 1) / (2 ^ 64 - 1)))

def big (v : List Nat) : Nat := v.foldr (fun w rest => w ||| (rest <<< 60)) 0

def hintsAt (words : Nat → Nat) (rowBase rowWidth listBase listWidth dictBase dictWidth i : Nat) : List Nat :=
  let start := field words (rowBase + i*rowWidth) rowWidth
  let stop := field words (rowBase + (i+1)*rowWidth) rowWidth
  (List.range (stop-start)).map fun j =>
    let h := field words (listBase + (start+j)*listWidth) listWidth
    field words (dictBase + h*dictWidth) dictWidth

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def page0 : List Nat := [0x48110e898a60887, 0x8676a09a243e121, 0xa926888714c9314, 0x2221c9324c12097, 0x4dd45344823c6a9, 0xcc8841248040358, 0x85e922211289110, 0x890fc98221ea428, 0x240887a98a217a6, 0x17c68885fa0243f, 0xa657a68905f1222, 0xa0a417c6890dfa0, 0x6e992617e8098df, 0x9876992437a6888, 0x82987a98a43ba62, 0xf260905fa02657e, 0x417e8498f699241, 0x92637e84985f1a2, 0x880001da42906e9, 0x15be000000000, 0x1a80001b80000, 0x32106000000, 0x1aae2580000000, 0xca0a602f78805a]
def page1 : List Nat := [0xa520c51841c8481, 0x4941cd5ad6b5a94, 0xd8f9ac6318b529, 0x3f481273b936867, 0x5f443e987d21fa6, 0x29062080e45afa6, 0x27a7724e64c6ec6, 0x1533508010fc907, 0xf240c1ec64a1802, 0xf0200427cd020a, 0x10f320043ccc01, 0xf861f0c8a17c0c, 0x3fe61d043e107f2, 0xe86950ca8421c9f, 0x281056212612671, 0x3e68104f1a2416a, 0x615e84985ba0a41, 0xa0616a29195ba0a, 0xe1a2415a48185a8, 0x957920616a29994, 0x7d7ce9a0419a641, 0xe0a800006400483, 0xe987e30fc65fcc2, 0xe997c32fe65f883]
def page2 : List Nat := [0xe107d20f861fc83, 0x10800026357b7, 0x14f0358db691201, 0xfa61fccbf087e3, 0xf843fcc7f197f2, 0xfc41f0c3e90ff1, 0x118400002e71000, 0xf186d6492344015, 0xd3d3ec688c2c688, 0x5409f45b53503d3, 0xbc9b5150f3f5350, 0x424c76e4509510d, 0x3e42550510bdd85, 0x58c510db8d42544, 0x41bb49b5150fe62, 0x45a454caf7614c9, 0x1442bf6150d409f, 0x6e4589510f98954, 0x91530db49b5150f, 0x9f159325067d16, 0x1b5150e7f568c54, 0x443e4254c5109f4, 0xf6550f10db8d625, 0xc510d7915314c27]
def page3 : List Nat := [0x9f45b5350be6254, 0x5414c3e62590510, 0x27c65509319f19, 0x564c540cf50f515, 0x5319fd5a414c27c, 0xf195434439d4350, 0x43486df6150d309, 0x75d43d4530bdd85, 0x13f6e08000524, 0xa00000160000000, 0x1254000011c0130, 0x3200000, 0x860168, 0x83c00000000, 0xc0041a0209f0000, 0x740000001580001, 0x100000000400000, 0x30000000, 0x1400000008, 0x90000000300, 0x400000001e000, 0x90000848100000, 0x140212000981, 0x5490d0188a22081]
def page4 : List Nat := [0x3414088a9a1a034, 0x4102c4a22081125, 0x409a88982058944, 0x6a228680b51140, 0x40e30c30a208186, 0x8a079e798596512, 0xcb0baeb2caa8a22, 0x6631410c0fbcdb2, 0x34314008ada47a4, 0x720cf343a06105, 0xe21ff5250640531, 0x8a987f8c540fea1, 0xea2e21ff5250efc, 0x3fa62885fd4540b, 0x30fa98e21fe4544, 0x5443fea6a0f750d, 0x50531be9ae21fe3, 0x7d454c6fc8a98ff, 0x87f4c941ff20a61, 0xa85f541c43d84a8, 0xa2a1f74c530bfa8, 0xea1a837f5350bfe, 0x3fa8498df41641d, 0x31bfa8a87f54144]
def page5 : List Nat := [0x150efa6b20f750d, 0x91531f712a21fc5, 0xf531442fea6a07f, 0x85fd4532bfa8a61, 0xa657e35443fa868, 0xa0a0ef50540bf22, 0xea0a217f5050efe, 0x3fa82985f41631f, 0x21fb20a21fd3150, 0x1443fea498ff50d, 0x50d40bfa9a83f63, 0x7e45442fa8b18ef, 0x83184100bfa8263, 0xbe30807cf6c02, 0x114778c00066285, 0x470420b8a2400, 0x400000001000000, 0xc0000000, 0x5000000020, 0x1c0000000c00, 0x9000000040000, 0x2c0000001400000, 0x60000000, 0x1c0000000d]
def page6 : List Nat := [0x800000003c0, 0x20000008100000, 0x810000624040003, 0x2000201000000c4, 0x824080004120, 0x88104000104820, 0x204240011020a00, 0x105000484820002, 0x13021200098, 0x4c4808002624, 0x13120600098902, 0x4c8828002624140, 0x212000a0104000, 0x808002824000014, 0x6000a0902000504, 0x2824100014120, 0xa1104000504830, 0x864040014320000, 0x10000050c818002, 0x140021020800108, 0x884810004204, 0x23120a00118105, 0x904820004804100, 0x20000121903000]
def page7 : List Nat := [0x820006204040031, 0x200188105000c40, 0x6424100031021, 0x198105000c84828, 0x624080033120200, 0x104000cc4828006, 0x800341202001a0, 0xd04820006824, 0x343206001a1104, 0x4410284a2208100, 0x40b12888204094, 0x2ea226080e2511, 0x9a88a0203d444c1, 0xa22868075114040, 0x1c0400d4450d016, 0x629110682811058, 0x210f870361a0c05, 0x94c05b2b13c9646, 0xa88409ecec71361, 0x552a1469f4d2551, 0x519ec9612f56ab0, 0x8f97bbc5d4e26db, 0x89c3e170682405f, 0xe101e2554963d18]
def page8 : List Nat := [0xce8c0a1060b1015, 0xf464912c1b95100, 0xf1e951665458406, 0x162840232c488b0, 0xe20f040f344101f, 0x991eac61e167483, 0x28b904860506f05, 0x4811e584a32030, 0x106090a1060b903, 0x92c00e14a100b0a, 0x8386be1ef44109, 0xe4440404422e00b, 0xad1634c2f192059, 0x388541442b21289, 0x28416243040600, 0x20d8f1068828403, 0x63e98a16240d489, 0x840c4381e882084, 0xe9ae9a0a303240b, 0xb524201a516605c, 0x1d09ec8d9010647, 0xc6051c35891181a, 0x2d7ae1414c901ef, 0xc9060d264860532]
def page9 : List Nat := [0x4ca87880aa46392, 0x1eec5060801e90, 0x2350628a100c01, 0x1800c2142718284, 0x4707083d6100e14, 0x2511c1238ba91e1, 0x62558f28848041c, 0x621b104c3128f2, 0xc1e58a8b0868646, 0x43f50dd8a0e1403, 0x7f503f4cbf50bfc, 0xf443f487f8c7f4c, 0x383f507f907f4c3, 0x5d41198400, 0x60000200000800, 0x600002800010000, 0x8000200000e0000, 0x1a0000a00004, 0x1000007800038, 0x82a20411102060, 0x40d2120a9090444, 0xa989004c082a60, 0x450081a64415312, 0x28241141200a010]
def page10 : List Nat := [0x43202a190050882, 0x89058c48128640d, 0x81c82412412051, 0x4031020b88104c4, 0x78c56a94268a901, 0x240501a2893e3c3, 0x73cd284590fbc31, 0xe1b0608586e9829, 0xe688610d04c8a58, 0x85c508862c31212, 0x5048a07905a691, 0xa84a0858c38c08, 0x213870a64918a61, 0x8b1ac2c688fb639, 0xc2431062214813c, 0x21e483621e8800d, 0xa1aca21e409fe35, 0x5d3724c5304430e, 0x51087eeaa3263a0, 0x4292619390f624d, 0x50d42c829723aa, 0x2a8e1aa62885ab7, 0x216cdcd4150110b, 0x3248368a3262982]
def page11 : List Nat := [0xa2e649854f5790d, 0xdc1434cb208beec, 0xf4aa1ac221a2172, 0xa8859b705894310, 0x68d520c38872346, 0x1ec4a2a218710e4, 0x8d435884348717a, 0x10f826490a60886, 0x90a416c41f43505, 0xd815210e9723a6a, 0xa86a122b9961d43, 0x1a650f604cb40e1, 0x14c2a693e871aa2, 0x90a49843f765174, 0x9e434d5108deeca, 0x16a1ec4a2a2117d, 0x9043f67d0d45443, 0x501108becf21a6a, 0xe86a1241e850921, 0x907d09324c297ab, 0x3d2a868b664a0dc, 0x82218750f625444, 0x940443c8a1a829, 0x8683684995b117d]
def page12 : List Nat := [0x8b50b560c940d1a, 0x90f0ea1ec2a9087, 0x6a498d2d47d8525, 0xd42d4930e1a86a1, 0xea1ec4a8087c350, 0x843f67d0d454830, 0x510ba22f21a608, 0x8419281654dc455, 0x4241b3250257bb2, 0xe1a87a9264a0ea9, 0x2656a49f4350110, 0x4344346a1a2da1, 0x6b288690e994358, 0x3d5c424c930c3a8, 0x4359b1a82a02215, 0x60885a927115404, 0x3150110ba22f992, 0x32a86a12616c51d, 0x5c92790d304430e, 0x930b328e1aa6088, 0x29822133d9c424c, 0x49b43502e89ba4, 0x38aca1a62a06ab7, 0x81a650d6010f20c]
def page13 : List Nat := [0x5010ea7b9aa4292, 0xa90a4a061d43d85, 0xdc132485108deec, 0x21eb3c8a2126178, 0xa885d1474c53044, 0x550110a5a4f21c8, 0x2a8599261664dc4, 0x994341b3250386a, 0x43d96e093486986, 0xa0221534df61497, 0x58843c82d8a3a42, 0xa8ba12649868d43, 0x1b4919314c110e1, 0x14c2c79b8a4a128, 0x3265a061c6550d4, 0x9c354c11087eeaa, 0x75b828c99243724, 0xa0de37050921442, 0x41732c38aca1a64, 0xc8599261c350d42, 0x2474c5304438722, 0xab0ea99260885d, 0x822117dd5464cb3, 0x815110f58a32829]
def page14 : List Nat := [0x868b68498e1d43d, 0x634dc4550920d2a, 0x44346a1ac421a41, 0x264985b117d0d40, 0xf524c940b1e8e29, 0x9b9282a0221c350, 0x854f7351521482d, 0xc530a70eaa12808, 0x8698a2117dd945c, 0x43d8142cc2e883c, 0xc38aca1a64a0699, 0xe619350f624d510, 0xa325022fbaa8c98, 0x6836849870f53d0, 0x450d3150110d328, 0x830e32a86a1263e, 0x800058d470d5324, 0x8843c9529080048, 0x2bab001d001d0d3, 0x63280073680000e, 0xd0552ab090c015, 0x5c800c00428107, 0x3d8503082084020, 0x7b0810000010023]
def page15 : List Nat := [0x800002012, 0x70000000280, 0xc90180050c84000, 0x5024404c502414c, 0x1454cc901c4050, 0x508cc9014c8d09, 0x84210842108420, 0x18c421084210842, 0x3106318c6318c63, 0x39ce7318c6318c6, 0x421084210839ce7, 0x5294a5252942108, 0x6318c5ad6a5294a, 0x6b58c6318c6318c, 0x841ef739ce739ad, 0x496318c61084210, 0x9019c0104204c5e, 0x641732d750d05cc, 0x40e350f424ca7e1, 0x41b5150a7e564c5, 0x4436d42d49309f, 0x7f5690d20ee50d4, 0x515109ed81454ca, 0xb751a434ca6f62]
def page16 : List Nat := [0xca35443af4350b2, 0x4cb5e43d4930d7c, 0xe4241732bb45b42, 0xf209bd89354436, 0xd750d05cc6ed621, 0xe454436f6550b20, 0xc3ad4350b20cf90, 0x53d0540e7115434, 0x943bb588434873f, 0xb50d42486fb6054, 0x524c6ef26d1530e, 0x36d4249510db50b, 0x28c930f58d53144, 0x30bb498354436f5, 0x49a435073d45505, 0x25033d4351521bb, 0xed60109329f45b5, 0xd45429fd8d45486, 0x9f49915cc33d43, 0x48524c2ef615092, 0x90ebf6350940db5, 0xf56909309f89915, 0xc910f3149324c27, 0xb74db424c67c654]
def page17 : List Nat := [0x90590b3d43d4141, 0xc76d21497409f8d, 0x60505409fd8125c, 0x530d790d35443bb, 0xf55b315027c6550, 0x21502fa464c1109, 0x67f6251531eb509, 0x50c439f195424c, 0x409f8d925d079d6, 0xd855010e7f654cb, 0x34439c5350d409f, 0x7e2645730bd5844, 0x50921be41b43442, 0xb745a434c2ef63, 0xc921cc2df361152, 0x503f36050510f34, 0xd434d520af4db41, 0xc9409f55b43c835, 0xeed81425027f560, 0x8424caed2690d10, 0xc27e36497409bd5, 0x16915329f49b514, 0x510dbd95420ca7d, 0x718d515027f624d]
def page18 : List Nat := [0x45442f906d0d30b, 0x27f6550b31b74d8, 0x61151097d8d4544, 0x109f51b524c6ed2, 0xd813590be532485, 0x5cc27f60515329f, 0xde464cb309f9192, 0x51632eb50d42482, 0xeb508325027f60, 0x8115cca7d269151, 0x442f546485109fd, 0xd4245732ec50540, 0xcb20af51931d036, 0xbed8141503ce434, 0xa454836d4241732, 0x42ef62545309f4d, 0x56cc940bed81424, 0x520cf50d05d067f, 0xb58525d0f3d4351, 0x25442ed2690d40d, 0xaad26d0d409f4da, 0x50921e750f424c, 0x42d790f504caef6, 0x15932506bd4690d]
def page19 : List Nat := [0x3506f906cc9409f, 0xe75148520af41b4, 0xd0d40b791931cc3, 0xdb4c925442bd16, 0x540443ae455092, 0x4427f614d520fc5, 0xd468d510f690d30, 0xb30d790f524c67, 0x9f45b5050efb605, 0x525cc35d43d4132, 0x27e46416329fd8, 0x43915109fd5b315, 0x5309f919354833c, 0xbcca254427f56d0, 0x40442df6150d30d, 0x27e2641643fc485, 0x6d4132af919524c, 0x41cfd0f515027d1, 0xd09324c27d36d41, 0x24867d06d4941f3, 0x7e468d510bb9193, 0x4d521dbd8525d0e, 0x19f49b515027f60, 0x85454839e4550d3]
def page20 : List Nat := [0x10e7f60496439fd, 0xd6250c43c750d52, 0x940e750d414c39, 0xe750c43c833f53d, 0x52590f5d328d510, 0xa7d56cc9409fd8, 0x464cb309f41b535, 0x5409f45a35482dd, 0xf41b5150eef6254, 0x32502df6350b329, 0x27e4649510dbd49, 0x34c921d750d15cc, 0x30db8d521483ce4, 0x41a42502ef26d0d, 0x35027d2691530be, 0x7d36d4540bb49a5, 0x149409f59443486, 0x1af51b32502df36, 0xf525067d06d493, 0x4433d43d4941cfd, 0xf528c9409fd5b32, 0xd209fd89454436, 0x9f919354427e651, 0x5424827e4645730]
def page21 : List Nat := [0x2dd3648730eb11, 0x36d0530ebd49425, 0x5309fd8525d02dd, 0xf91935c833d4511, 0x254433d45509309, 0x39d4350b31dbd0a, 0x34cb209f1593250, 0x20f3d49324c3cd4, 0x50d35c82ef614c9, 0x24867d46d4532d7, 0x5f6351520bbd813, 0x501109f49a454c6, 0x9fd8525d0fb942, 0x5b424c67d464d72, 0x4827f6049743bd4, 0xe45d09209f51b51, 0xc530b7919324c33, 0xbb49a43486dd46c, 0x9304435d324d740, 0x27e2645740be51, 0x464c921af51b315, 0x740bb49b43c82ed, 0x7d4d435079d434c, 0x454867e1641742d]
def page22 : List Nat := [0xa7e16416439fd81, 0x68c920bb41b424c, 0x209f51b514c2ed4, 0x895214433e45505, 0x24c27f6351532f9, 0x9c5350d42be41a3, 0x4c9409fd8115d0b, 0xaf51921503af42, 0x1b32506f6464c51, 0x443b64550510af5, 0xd06d0a32afd1835, 0xc5309f89915d0ee, 0x9fd8d45482de464, 0xb434427e464d521, 0xc27f65505309fd5, 0x6d4943f6d81314, 0xf209f4db525067d, 0xb50921d02ed2690, 0x404436d2691532e, 0x27e2641741bed8d, 0x550b30afd854250, 0x10cf50545cc27f6, 0x41b424c2f90690d, 0x25067f568c940be]
def page23 : List Nat := [0xcd434c920d7d4d3, 0x50920dbd852590f, 0xf550d31442ef63, 0x9324c3d1314c11, 0x4c3cc354c920f31, 0xa354c110d791531, 0xe32cfd0f5050bd, 0x8f91935442ed26d, 0xb504c63e464d520, 0xe7d36d45429f49, 0x45d05209f89905d, 0x540b751931cc33e, 0xf41b514ca7f5648, 0x325067d16915209, 0x6fb6050940dbd49, 0x6cc520cf50945cc, 0x30afd5b4350aed2, 0x91932483cd32485, 0x1443f1314c110bb, 0xdf6354940f95092, 0x50932af51921d02, 0xaf51a325039d43, 0xd424c75d315173, 0x4c36f6049743e75]
def page24 : List Nat := [0xe434d7209f45a45, 0x730e750d42cc35, 0xbb49b434867f655, 0x9514c36f654cb20, 0x75d43d4530af11, 0x46497319f8d905d, 0x520fad81424827e, 0xf91905ccb6e4548, 0x32503ce434c9209, 0x35d45cc5309f558, 0x641731cf517414c, 0x40fc485304427e2, 0x50d25d027e564c9, 0x54427d56d0530cf, 0xbd464c540cf50d4, 0x497419fd85454c2, 0xd750f504c73d43, 0x9b414835e454c93, 0xd02df6350b31bb4, 0xc6550520afd8542, 0x9309fd8125d067, 0xcf50f5050a7f561, 0xb5350acd2690d30, 0x42ed3690920db49]
def page25 : List Nat := [0x43d0930bd45b424, 0x530cf915434c79d, 0x79894310edd464c, 0x42ccb6d5214940e, 0x2f906cc910e350d, 0x3515109f55a32d0, 0x40cfd9542d027f6, 0xd0d45442dd36149, 0x34433e4550d30cf, 0xef2690d409f9944, 0xd09329fd95424c2, 0x9f55b424c33e45, 0x85454cbf1315011, 0x90bce42cc9309fd, 0xf5350540d750d35, 0x1720b749b314c33, 0xbb49b434427f635, 0x9304433e4590930, 0x82ed464c920f64c, 0x464c510cfd0d45c, 0x7439fd81454c6f5, 0x750d32d067e1641, 0x4350bb74350510e, 0x27f6045643e7d4d]
def page26 : List Nat := [0x550910b74da424c, 0x42be580434427c6, 0xd8941502bd06d0d, 0x54835e43d4131af, 0x6d6149643d7d0e3, 0xd09319f49b53507, 0xbb49b454c27f56, 0x8843483b4455051, 0x5035f438d510bb5, 0xf6550832d7d4d43, 0x1510d7515314c26, 0xe75854310e7d369, 0xb414839c4550d31, 0x827e36495109fd5, 0x314d7409f59443c, 0x930e750c434875d, 0xdd85434879d4350, 0x4350bcf6350b32b, 0x35d454c930d7d4d, 0x291510e750d41cc, 0x30bd45b324433f4, 0x49b5050efb604c9, 0x50a7d46d41319f, 0xba45501109f4db5]
def page27 : List Nat := [0xd4d42cf50535d03, 0x9f55a325027d16, 0x5b43442ed26d0d3, 0xd036f5290940bd4, 0xd16d49309f8d915, 0xc1109f8d915d0a7, 0xd750d25cc7d9434, 0x9214827e4645732, 0xcb6f6049643bb4d, 0x4291510cf50d458, 0x530fcd81314433d, 0xbd8d42c82fb604c, 0x31442df6250d30b, 0x36f5294940f590d, 0x64cb40d710e3544, 0x40d78d731482bd4, 0xd8d424c75f538c9, 0x3482fb604c910b7, 0xb75150540bb49b4, 0xd4543afd8543503, 0x9f55a43c827d26, 0x58424c39d4310d1, 0xd067c654c5209f5, 0xd5690d21af91932]
def page28 : List Nat := [0x4532d754c535027, 0xfc505304435d43d, 0xb535039d43cc540, 0x827f61548439f49, 0x354c110bb91932c, 0x940cf50d15d03d8, 0x714d435073f5350, 0x45c82dd464c930e, 0x27d5690b30cf50d, 0x49643eed094044, 0x21cf50945cc36d6, 0xd8115d0f5e434d5, 0x54cb1d43540439f, 0xbf46149309fd584, 0x4cb30cf915424c6, 0xd710e354835f65, 0x1932506bd460d52, 0x4c2bd26d0540af9, 0xd43cc940d7d8d45, 0x9743f38d5324839, 0x9f195424c36d604, 0x13510a7d468d520, 0xca7d2645740d758, 0x3641742cf581450]
def page29 : List Nat := [0x42d750f524c67e, 0xf45b425027e3654, 0x414c36e42d4930a, 0x27d56d0d21e750f, 0x6d0d31b7d8532cc, 0x409fd5b424c2ed2, 0x90f514cabd460c9, 0x3503d4354c510d7, 0x7f5690d10afd894, 0x544439f45b5050a, 0xed50d414427f62, 0x19500caf7624c51, 0x482dc63549409f9, 0xd434c9419f91a35, 0x4930cf915434cb9, 0xfcd8530442bc465, 0x5314833d4345742, 0x67d16d4943d78d, 0x63545409f49b505, 0x931e750d32502df, 0xb149425033e45d0, 0x524c2f90690d40e, 0x35f53cc941dbd4a, 0x610930e750d3150]
def page30 : List Nat := [0x109f51b504cadd3, 0xd0d404435d434d5, 0x3506df3611510ee, 0x9d4310d20afd814, 0x4d741bb51932c83, 0xcfd0f525035d32, 0xd42cca7f625153, 0x4833d424d740e75, 0xd4689510afd1835, 0x740b741a434c67, 0x9fd815110ebf635, 0xb314827f654cb41, 0xc35e434d5209fd5, 0x5690930f6d81324, 0x910b749a434c27d, 0xf4db52502f906d0, 0x32487cd434c9219, 0x27f654c740f9d85, 0x4cb40db4d52148, 0x21bb49a43482fb6, 0xd0a325033f43515, 0x24caf53648510eb, 0x3f43d4542eb9174, 0x54530afd8d41503]
def page31 : List Nat := [0xb7d8931cc2be46, 0x8542487b8455011, 0xcc27f6254043f9d, 0xd0691531d750d25, 0xc9309f4db514827, 0xcfd0f50506dd46c, 0xf515036d4548520, 0x43af4350920cf50, 0x43915209f49a354, 0x742be58043c833c, 0xfd8941d033d4341, 0x435035e43d4530a, 0x2f51690d10e7d4d, 0x2cc930cf914424c, 0x329fd59214c3cd4, 0x4da42cc2df6050d, 0x25033d45d0930b7, 0xf516cc941cf50f5, 0xd4d41b7d81434c6, 0xafd814350a7d06, 0xf424c76d32d452, 0x4867d0691532e75, 0xf6054843d750d35, 0xc530d750d15cca7]
def page32 : List Nat := [0x9f51b524c2df624, 0x7324c2dd0690d32, 0x435d3251730d791, 0x4550d32af518354, 0x941d7517324c39c, 0x7915434cb9d43cc, 0x454c2bd4614930e, 0x36d42d4520cfd91, 0x14c530d7917314c, 0x30bbc9a53503d75, 0x49b43502df614c9, 0x15035f530c940af, 0x1d43544439f1593, 0x90d32bed8143c83, 0x2e7915434c2df56, 0xf524c2ed2690e4, 0x506f76350510d75, 0x76250510e7d4d43, 0xc110afd8d42d02f, 0x9fd5b42443db324, 0x9500cbf36150110, 0x2bd36d0940db50, 0x4351520af519325, 0x7309f45b535033f]
def page33 : List Nat := [0xbd0d424876d2149, 0x21483eb604c920e, 0x2bd468cb40bb519, 0x34cb40eb50b3250, 0x419fd5b434839d4, 0x4d8454827f56cc9, 0x24827e4641731b7, 0x3e4391520d78d73, 0x10932b74d9214c3, 0xb74db424c2ef56, 0xf00001add16cc93, 0x20000b7b3, 0x8000fac, 0x27000ad5c680000, 0x3a5000020000, 0x110cf080000000, 0xaa5000008070000, 0xe6878000febd40b, 0x10001848b54b23, 0xe89d004c5d7bcad, 0xee4004190d20208, 0x91ba00000000000, 0x3e11befd4020e, 0x2436010]
def page34 : List Nat := [0x93000bc40000001, 0xc01000004001d1a, 0xd3d3c9ed01804, 0x3357420000022b0, 0xa40024b34b39c01, 0x6234c40150d62a6, 0xd86f000625d3800, 0xe040030d4c73754, 0x1ee00000000a56, 0x668002ba0000200, 0xdd42d8af00042c, 0x31000fa40012f00, 0x672008000, 0x33de280000002, 0x75a7d0, 0xfe8b96572277400, 0x40020ec3f0011, 0x80000000065915, 0x3cf000029b, 0x500000011893000, 0x94ec1542a0, 0x6ccea995000018, 0x150000080102100, 0x400345004a64022]
def page35 : List Nat := [0x400200014, 0x2d29cc000000, 0x42e01000, 0xab69ecab0000, 0x65334603800, 0x2000171592f8c0, 0xf6d6000000002d6, 0x21d10ea3c001b, 0xe284a28005fa164, 0x390000000236570, 0x98c80080a0021bc, 0x22880060201, 0x27b3220024ec170, 0x208d7000d6400, 0x1364002710000, 0x4a0900097de4c69, 0x2f5a, 0x33f2c404000000, 0xbb80e36e0024380, 0x6050408029ee000, 0x40000026683309, 0xc00002000b94a48, 0x60400010000a5, 0x800000000000000]
def page36 : List Nat := [0x135c1a, 0x100c040c50080, 0x40008ca3f400008, 0x1cc8000000000, 0x8b60100042d416, 0x200000000, 0x400000000132000, 0xac0022900, 0x444a6b000000228, 0x96009d5bbf020eb, 0x481a002228002, 0x80119b7fa00000, 0x8005350000, 0x19237ba00000006, 0x217800001084d, 0xa73ef2c0347784a, 0x3679eb3940000, 0xe904000001b2008, 0xa8c0000ba7, 0x40000e008b043a8, 0x6b58f8000007d, 0x2c26140000a0, 0x83e00000, 0x7e200052a753b20]
def page37 : List Nat := [0x196d020000000c7, 0xfe4d88000000027, 0x3000a7e6f80000c, 0x3ca0280025, 0xe008021f9000000, 0xaf5ec8069d, 0x4332018000, 0x26080000400, 0xc63000000000370, 0xe40000020e00060, 0x16dc910014, 0x480000000001006, 0x38b0012a48, 0x900873405000000, 0x3890004ec0136, 0x602800187000000, 0xa6160011f80216, 0x4708005ba0001c8, 0x6766daa9000cf, 0x566002238000, 0xd100004802, 0x49a000004010000, 0x3bd50e00000000, 0xb14000000000000]
def page38 : List Nat := [0x2ec002ef376, 0x5bce1010f9c0f80, 0x1fa81004002, 0x1f40000000, 0xc00397000000000, 0x181802000e0, 0x2432000003d30, 0x7180000028c00, 0x992000000000000, 0x5300004403000, 0x19c000020000280, 0x700001006000004, 0x938042e6001f6a3, 0x4d3008002, 0x80000000, 0x20000, 0x1000000000006, 0x280000000, 0x60000, 0x200000000000e, 0x480000000, 0xa0000, 0x3000000000016, 0x680000000]
def page39 : List Nat := [0xe0000, 0x41000000110200, 0x4c08100000022, 0x981030000, 0x240c00000131202, 0x4c48200000026, 0x991020000, 0x441800000132206, 0x5008100000026, 0xa09010000, 0x440800000141208, 0x5088280000028, 0xa19070000, 0x40c00000143210, 0x8c48180000046, 0x1191030000, 0x44140000023220c, 0xcc08180000048, 0x1989030000, 0x440800000331208, 0xcc88180000066, 0x1a09040000, 0x680000000342204, 0x54d0d0000022a48]
def page40 : List Nat := [0x92921a010004, 0x680400125243404, 0x94d0d0100024a68, 0x988882040004, 0x81000132342404, 0x8cc90100028222, 0xa1821a000005, 0x680800143043402, 0xc8cc90080028608, 0x1211a12010008, 0x280400245130404, 0x144c90080048a26, 0x1881082000009, 0x280000325343402, 0xc88c90080066246, 0x19a821201000c, 0x480400341241400, 0x140c90080068448, 0x1a9098202000d, 0x80800352131402, 0x48505008006a428, 0x1a98a0202000d, 0x480400353141402, 0x4410d800006a628]
def page41 : List Nat := [0x2309a88830050c5, 0xc0360145131601, 0x40201006c628a22, 0x8038180c050281, 0x6830140a0502410, 0x42210078381a0d0, 0x160a85024120884, 0xd86832180c0602e, 0x8442110880401f0, 0x271309048241188, 0x68ac5429148a050, 0x5e2e170b85c2d1, 0x34198c86231188c, 0xb0d46a341a0d068, 0x47c3d1d0e470371, 0x442190884422090, 0x29148a45229148a, 0x9048241208e462, 0x5228940a04e2512, 0xc15cac552a150a4, 0x4ba5d2d964b0582, 0x603017cbe5e2f17, 0x2988c46230984c0, 0x8d2693419cce663]
def page42 : List Nat := [0x6d361b0d66a351a, 0x81bcdc6e371b8da, 0x8ec75391c8e0703, 0x7e3e9f4fa7a3b9d, 0x1a0d068240a04fe, 0x90c854221106834, 0x8944a25128843a1, 0x6a351a8c45a2912, 0x51a8d46a351a8d4, 0x9349245208f4723, 0xca6530974ba5928, 0x53e9e4e26934994, 0xa451a8d44a25128, 0x52a552a853a994a, 0x158ab55aad56ab5, 0xb158ac15eae56ab, 0xb2d56ab459ac962, 0x570b85badd6eb75, 0xba5cae572b95cae, 0xfafd7cbd5e2ed74, 0x190c46230d82c05, 0xc964b2592c86432, 0x532994ca6532994, 0xd9ccd6632d94ca6]
def page43 : List Nat := [0xd269345a2d067b3, 0xd365b0d86b359aa, 0xdbede6f375b8db6, 0xe170381c0e07037, 0x2391c6e270b85c2, 0x9d2e873b99cce57, 0xee76bb1d8eb753a, 0xabd1e6f278bc1e0, 0x1feff7f3f5f2f97, 0x481c0a05018040, 0x2c1609048241209, 0xa1b0c8542611078, 0x1388c421f0f87c3, 0xcc6631178b45227, 0x2371a8d46a351a8, 0x2692c8a431e8ec7, 0x44a24f269349a4d, 0xa5b2d964ae55299, 0x32994c6613097cb, 0xccd66b359a4d265, 0x2773b9d4ea73399, 0x41a05027f3e9ecf, 0x2d128742a150683, 0xe9d4ca5d229147a]
def page44 : List Nat := [0x52a9546a150a853, 0xcd62af56aad52a7, 0x2bf5dae56eb559a, 0x67b359acb61b0d8, 0x75b6d96ab4da2d1, 0xaeb75ba5cae16eb, 0x79bc5e2ef77bb5d, 0x5fefb7cbddeaf3, 0xf0f85c2e070380c, 0x8bc562b1387c3e1, 0x7e3f1f8fc7e3b1b, 0xb2390c8643218fc, 0x96cae4f2793c9e4, 0xde6b3599cbe5f2f, 0xb3b9cce66f379bc, 0xa5d268b45a1d067, 0x6eaf57aad469f4d, 0xf65b1d86c361aed, 0xb6db6db6db5da6c, 0xd6e771b8dc6e36f, 0xb7dbedeef377bbd, 0xc2e17037fbfdfef, 0x47238fc6e2f1387, 0xb9bcce672f97cae]
def page45 : List Nat := [0xd3e974ba1cfe7f3, 0xcf63afd6eaf53a9, 0xfc5e2f0f83bfdbe, 0xe9f4fa3cfe5f278, 0x7fbbdbecf5fafd5, 0x7e7f2f8fc7e1f0f, 0xf8fbfdbedf6fafd, 0x30a10706fdfebf3, 0x60acc2189e141b, 0x1a03a3401d0f103, 0x485000d0820418, 0xc28100487a60b2, 0x681d82020c3004a, 0x8ac018204000980, 0xc0c001984834c01, 0x813a9419d3c0020, 0x40cd5a0632686, 0x98070615480100c, 0x103057c14ea9081, 0xe081004a20a8c0e, 0xa0032d92484100, 0x73a8a69f1cb9c0b, 0x86060662f00002b, 0xa9371c08800806]
def page46 : List Nat := [0x2013a1c2034000, 0x2188038068031e6, 0x200118004980d0a, 0xc78046d92800, 0x50a0028206f009d, 0x1800141023a0650, 0x70164148933a156, 0xc405305c083000e, 0x7423b28700983a5, 0xc0c803069a08002, 0x2700844a380831, 0x16ca40a40ab92c2, 0xb52e107386c90b8, 0x980681b0374102, 0x42012c0441d069c, 0x8301028cb8d300, 0xa35b07023459b08, 0xa0908b0e101233, 0x810000a5088c200, 0x461418001100c08, 0x8d3a001003a047, 0x800c745800020, 0x99320020cf0e5c2, 0x80c0840a04c0010]
def page47 : List Nat := [0x3cdc7153a6062b0, 0x540401f720019f, 0x20100c2013a2d48, 0xb205284b2656a50, 0xe3880a040051a9c, 0x2b0a052142c3, 0x80c09f1c0c42000, 0x100c0830a1c7290, 0xc10000c03034301, 0x95547020d026cc0, 0x2854c01e0e0b0c0, 0xc68552390016e6c, 0x5540606f54851d2, 0xc012175214f0e08, 0x1c080a002050050, 0x896a5b971134f38, 0x302180a84a3e4b, 0xfbf0a609011a025, 0xea2e60a00840230, 0x3fea6a07b90920b, 0x32fea8a61f93044, 0x2503bc8698fb508, 0x54042ff98a417f5, 0xff50506fa4ba05f]
def page48 : List Nat := [0x7fd4d42fea1263, 0xa617d058cbfc8a9, 0x4ba0ff90d20fe22, 0xea2c857f53506fa, 0xbfaa4985f4d740b, 0x31f699641dd434c, 0x3507fe84907fd0d, 0x14930ff19281fd4, 0xf531442fa0ba1ff, 0x5f4d510fea8a81, 0x2417e45442fa8b9, 0xa2a1dbc9743ff99, 0xfa1a817d1590efe, 0x7fea0995f51530d, 0x30bea2a41fc454c, 0x3cc3f88690df915, 0x4c920dfa1a83dd4, 0xfd42507fea4a07f, 0x87fcc910be9ae83, 0x4657e25443fe829, 0x64987fd4131f7a1, 0xea12217d15cc3fa, 0x7fea2a07fd0d21f, 0x43af9a8857d4548]
def page49 : List Nat := [0x390afc8a905f544, 0x10930fe1aa41fe4, 0xdd43ccafea2a17f, 0x7fd4532fe29a83, 0xa81f521443fc6a9, 0x87a17f0c940dfa0, 0xfa9a81fe4350b7a, 0x3fa84a07f90930b, 0x21ff22a617d4544, 0x1482fa6a907b509, 0x49731fe99221ff4, 0x7f5050f7a87a05f, 0x86f50d40fea0a81, 0x2817d25443ba659, 0x4b21fb4c920fea9, 0xf21a81fe5250ede, 0x6fc8a997f50f20f, 0x32bea8087dd43cc, 0x5443be64987b50b, 0x50940be82e63fc3, 0xfd314c2fea6a16f, 0x87f91510ffa1221, 0x6813f450cbfc868, 0x6a887f50d40ff19]
def page50 : List Nat := [0xea28657d05d07fc, 0x2fa4b985b496439, 0x30fea1a41ed42c8, 0x3442ba6a217f507, 0x50920ee99261fc4, 0xff31503de84997b, 0x1df41732be8ae87, 0xa61dd31cc3faa2a, 0x8a98dfd4941fea2, 0xf12a21fd438cafc, 0x6fa8a98ff90d41f, 0x41ffa1c65ff524c, 0x5ccbfa64a07fd49, 0x51632fe21a417d4, 0xfe324c3fa84905f, 0x5f4d521bfa8a41, 0xa61bd4350b7a83a, 0xa4a07fd4142ffa2, 0xe8ae817d358cbfc, 0x3fa65a07f94d40b, 0x42bea2c87fd414c, 0x510bfa85995f4d7, 0x4cb41bfa82637d3, 0x7d25d0ffe84997f]
def page51 : List Nat := [0x8ff50932ffa9261, 0xa63fc43c83fa859, 0xa0a1fb4c921fea1, 0xea0a81ec424cbfa, 0xbfe86887790d32d, 0x42dfa12817f5050, 0x250ffe84985f416, 0xd0931bea80657f5, 0x7f524c7ba62987f, 0xff14d42ff21661, 0xa417f514c3fa869, 0x86887f48740fe98, 0xe82c87fe42503fa, 0x3ba86987f4c540b, 0x40fe90e61fd424c, 0x250ffc8a98dfd45, 0x50d32ffa9a83fd5, 0x7d5210ffea2a17f, 0x8efd0d42fea0a41, 0xe41fe43487ba869, 0x4ba1df51432be9a, 0xe29a81fd324c6da, 0xbdc85997f4c740f, 0x10ff99283ff434c]
def page52 : List Nat := [0x5d0bfc8a997f115, 0x51532bfa82837d0, 0xfd4390bf88a995f, 0x17f14940ffa1a61, 0xe65fd32507fa86a, 0x87905f45742be8a, 0xea1a61fd214c3fe, 0x7faa6a07fd4530f, 0x20ff292617d45cc, 0x3d07da42907fd0d, 0xcc530dea1a83bd4, 0x7e35443fc879077, 0x1fd50510ff99281, 0x6817d3590afa4b2, 0x8621ff48540dea1, 0xe22a41fd42cc33a, 0x3dc64907fd4520f, 0x10bfa8265de434c, 0x5482fea2997e501, 0x93400bfa92617e3, 0x70000c0b0007, 0x90912e4d0b000f6, 0x50511e108003e0, 0x34a1cc008780]
def page53 : List Nat := [0x1008141e0d0122e, 0x80c02c604d78332, 0x2c1297a003000, 0x1538a449988820, 0x8f800929e020690, 0x31e824300001, 0x90941a00002a0, 0xc000c050302c041, 0x10074806404f4de, 0x8000000005c, 0x6000000020000, 0x280000001000000, 0x60000000, 0x200000000e, 0xa0000000480, 0x3000000016000, 0xe0000000680000, 0x800010200000000, 0xc48000006040, 0x32202000189010, 0x48000008040800, 0x202000209010001, 0x80008640000042, 0x2190200010c8]
def page54 : List Nat := [0x22041000110200, 0x981000004848080, 0x40c00130204000, 0x10004c48000026, 0x131206000989, 0x4c88080026241, 0x132206000991020, 0x8000026441800, 0x200000a01020005, 0x200028240400141, 0xa11010005048, 0x28441400142204, 0xa190100050c8000, 0x40000143204000, 0x10008408200042, 0xc00230204001109, 0x8c48000046040, 0x231206001189010, 0xc88100046440400, 0x20c001191030008, 0x48040800232, 0x1209010009048, 0x48440800242202, 0x219010009088280]
def page55 : List Nat := [0x40000243204001, 0x1000cc48000062, 0x400331208001989, 0xcc88100066440, 0x341202001a09000, 0x88080068241000, 0x202001a1102000d, 0x68640800343, 0x8a99820045490d0, 0xa68680115340400, 0x21a0249490d00a2, 0x680925343402929, 0x4c44c10024a68, 0x93133040098921a, 0xc8d090126424080, 0x1104009a8212014, 0x10028228080135, 0x404a09a1a00504d, 0x28466480942120, 0xa1821a0150c10d0, 0x626280143043404, 0x1920150c5050028, 0x280145110400a28, 0x54410d0028a26]
def page56 : List Nat := [0xa451104011a8882, 0x144c50048a26080, 0x13240322898a019, 0xd00e4a48680645, 0x401a8098a00c94d, 0xea426080b50141, 0xa90a0202d484c50, 0x628080b52141403, 0xa0a01d4c505006a, 0xc00353142403a98, 0x1902c0480700b00, 0x1802a04e0900f8, 0x901182103f0720d, 0x660c01682904c0, 0xf43c8760e41b834, 0x120230448821001, 0x58a71462804c896, 0x310610be16c2c45, 0x31bc3606a8d3196, 0x7b8f51e03ac730e, 0x4434841042003f8, 0x2623e4708c11422, 0x89d1342644c0969, 0x9a524a39442804f]
def page57 : List Nat := [0x1622be55ca994f2, 0xf0bc9722de5b0b3, 0x324638c51873025, 0x59a7344680ce196, 0x70cdf9b43626bcd, 0x23ba75cea1ce394, 0xff9fa3ec7c4f69e, 0xa84505a07408808, 0x2a44e8911021a42, 0xd20a3d4708cd172, 0xb09592925049290, 0xa714da9a93325e4, 0x1d4127e4f89e53b, 0x53ea654b291516a, 0xaab355eab553aa3, 0xb25632c2580aed5, 0x55c4b6d6c2d459e, 0x7e2f95e6bc174ae, 0xec2d84306606bfd, 0x2b64ec858cb1461, 0xd9eb3966acc9973, 0xacd49a634968ad0, 0xb696ccd7dae3586, 0xfdbe3796e6dc5b6]
def page58 : List Nat := [0x72ae45c5b87706d, 0x63a7748e85cfb9a, 0xef1dc3b6766ec5d, 0xb7acf3de43c3780, 0xf5be77caf8defbd, 0x9005ff3fc7ecfc1, 0x1582303e0540880, 0x61342484106e0bc, 0x8d1021d4338610b, 0xc5a8ab14e27c498, 0xf63b4708d91922f, 0xc0a0402320e9051, 0x531917452e060d0, 0xe073a1c05011f38, 0x30d05060d0e1f1, 0xb057e0c51331a47, 0xe05060d080d050, 0x6022c570b06412e, 0x40c06050d09070, 0x743083f3e0b0306, 0x5034625063c0d1, 0x806010e0d080604, 0x18390b0982540b0, 0xb30062f2e043b11]
def page59 : List Nat := [0x3c0b090402320e0, 0xd6c032605040e08, 0xd093b332805250, 0x4030a064708062e, 0x25306044c06050, 0x2050d2232080704, 0x220300072a29074, 0x34042032e0d3a4a, 0x8052541150c070, 0x100330e7945060d, 0x6070a010047050, 0x70e040232195303, 0x50425324653080, 0x143000308094708, 0xc0a0474466f2e5, 0x5320e050d383218, 0x25331a54030d060, 0xb1708510b080504, 0x1330e442f0c0a2, 0x64907014d05390b, 0xc0b0706050d050, 0xc070502220d0e36, 0x6002205040b053, 0xd060c0601070d0a]
def page60 : List Nat := [0x10a0d0706012a0, 0x100060506050d03, 0xa030c4371071a0, 0x83c450427734115, 0x70a05010d05060, 0x60a544d05040e09, 0xd3c13084b09052, 0xe060550162a061d, 0x300c043e5205040, 0x832180b09048053, 0x40c06430605043, 0x6192c424f030007, 0x30830060d384, 0xd080d06634c253c, 0x10e0d0b0501070, 0x20e05320e0c0805, 0x320a02062c04023, 0x6040e250503060e, 0x8430605070d5f2, 0xf050d6028050425, 0x383233310b0e783, 0x50477030c01040e, 0xe75283e41150a4, 0x9040206054b0533]
def page61 : List Nat := [0x50468060e08071, 0xd073a4c254d1304, 0x2e480f08061f050, 0x483030b642f0604, 0x81303e1139093f0, 0x701520609020522, 0xd05160207424e0, 0x43f06050d070601, 0x1202073a32060e0, 0x50d480f08052a06, 0xc5a5928056e0e0, 0xe0d560c0539250e, 0x60508040e30062, 0x20105620e060d0a, 0x5d2605042507060, 0x1050e673006042e, 0x10054060605046, 0xf0708064c050709, 0x241022050933480, 0xb080c057f0d530e, 0x4118150c0976470, 0x7010d0b05040e3b, 0x33090d0a3b330, 0xf0427090d475401]
def page62 : List Nat := [0xe2720040b0a0d3, 0x80604050a01410c, 0x51270b3f01300d0, 0xd3c04250c060804, 0x90d0a090706050, 0x40e2d142c060301, 0x2e38326d032f060, 0x6250b042e080604, 0x5002c060528042, 0xa0b050128383209, 0x40333320e20230, 0x5040901390b0e0b, 0x722620d0e0c060, 0xb05283a480f0806, 0x5b0b06060b05040, 0x54c08135808305c, 0x63028300c060b0, 0x30905540501040c, 0xd0e010e28050d0, 0x428052d062a2c05, 0x705010d065e260, 0xb43480f0705082e, 0xd172e525104067, 0xe0501062e0543]
def page63 : List Nat := [0xd0606050d0b010, 0xd0d24051f220905, 0x3004450c080b067, 0x94a090e0d270c04, 0x50d081f0a06000, 0x30702010e0d0609, 0x704024605042e4, 0x50e322023093208, 0xd052720040c030, 0x7092a0905000a4f, 0x1a095432040e1a4, 0xa062f0b04050e3b, 0x710801000605500, 0xf0430060a060d08, 0x50324050e33662, 0x66e0d0e03250d0d, 0xb09210b5c5b300, 0xe0905060353263d, 0xd05280b043e0d0, 0xb05040d07420a06, 0x70805510645030, 0x80f0805072c480f, 0x287000010e0b424, 0x20b06040e0b0504]
def page64 : List Nat := [0xb04060e0451383, 0x1050d0b06050d0a, 0x501060d0a07060, 0xe07050d06040907, 0xe0705011f32050, 0x425410c01330e46, 0xe1d0d080504060, 0x32d060e33500533, 0x3a05044b121f050, 0x10511390b070337, 0x590c05060d2c060, 0x701450d5508285a, 0x2f040e2e06280b2, 0xb6a0e0507060d65, 0x430c06013069036, 0x50d353407011b08, 0x46190305253f130, 0xc480f0706082532, 0x10d1c06012a7a3, 0x9030b3c0a070906, 0x67c0b4c7211390, 0x3fd42ff41fd300c, 0xfc32fd10fc43fd4, 0xf31fc42fe42fd21]
def page65 : List Nat := [0x32fd32fd31fd41f, 0x3fe43fd40ff30ff, 0xff42fe32ff40ff4, 0x73a36c0fd20ff20, 0x1000091bd020, 0x200000c000040, 0x1c0000c0000500, 0x140000900004000, 0xd0000600002c000, 0x8644040001c0000, 0x432022190010880, 0x90144080086408, 0x480260409302009, 0x40132202989014c, 0x2a090050081280, 0x150c80284405412, 0xc6440543204a190, 0x432032190090880, 0x8102cc08048640a, 0x80664407312039, 0x40741203a0102d0, 0x5a1901d0c80684, 0x806848301803432, 0x910f8e0ccbcac98]
def page66 : List Nat := [0xd5b9a1897155412, 0x43116022209f9e5, 0x8530436d04c1551, 0x440c286035c10b7, 0x403100d244511f1, 0xc3453843051060, 0xf14c12314c1445, 0x4530536904c10d1, 0x52016043042417, 0x4da8c11714a6443, 0x5b0271433680041, 0x640e694511a1031, 0xcdb0016f0f1c041, 0x6e30516210cac40, 0x441c03051003043, 0x8346b9093927d31, 0x8348b90f04a1c85, 0x2146498f04a1c65, 0x8143c425844028b, 0x87b2a8318479751, 0x8e50f0691721c3a, 0x8ca3cbae0d19621, 0xb2170d4390b05, 0x54390a32cb20a9b]
def page67 : List Nat := [0x6a1c652284163dc, 0x966a42c1a35c878, 0xca40c720aa300b1, 0xcaa0841a650f068, 0x3791b25c4317216, 0xa9eeaa1c641045d, 0x6431ddd95114543, 0xa30842a7baa8719, 0x78346b90ceb2791, 0x355e428ca30cb28, 0xe363928c9ae215, 0x6b90e6b50c9a505, 0x691721e1a87214, 0xbb20a02c859a8cb, 0xf0e428ca458c23d, 0x820a5eeaa1c8590, 0x7190414bdd54390, 0x78db25c42e43828, 0xb0e0a2c6498c3d4, 0x814e1c14590931a, 0x158cb0ea1acb194, 0x1948b90f0d43909, 0xdd91505632e1a87, 0x346a1e0d214651d]
def page68 : List Nat := [0x5884d9379182084, 0x141438f2eb8348, 0xb22a0ac851edd95, 0x4f5790a324c63bb, 0x408f6ec8280b195, 0x192638b90965c86, 0x8d82084386a2c85, 0xa87ab48498cb947, 0x18b909658ca40c3, 0x28cb27192cb90c6, 0x2a621058c7050e4, 0xe428d420c9c65b, 0xe583c8519461c35, 0x205a87050e42082, 0x8c941d548583465, 0xeca98c818750f56, 0xe42d5a325070ea1, 0xd1a868b4851962, 0x14618750d5690a3, 0x180e2134ca1e0d2, 0xae10b8110ee, 0x5daa08000000, 0x9ad00, 0x1cc177000000a0]
def page69 : List Nat := [0xf00000004b9c14d, 0x803e00000a20002, 0xe7280df8f4, 0x108210842100000, 0x41cc52948420c63, 0x5294a5292942108, 0x7b9ce7358c5ad6a, 0x442b29463083def, 0x4fa8d82c650c40b, 0x48a8417d1b04108, 0x85baa88a2a1edc6, 0xb08a4a1e7a8782c, 0xb086bc8b192633e, 0x3a86a2c613e9b48, 0x20041aea1a6a10f, 0x1d721464a0f5c85, 0x3464105d8c49884, 0x2157a8d0ac65f48, 0xa8d1a8416e9b00b, 0x2e21ec302871847, 0x3f1b64b20edc659, 0xe4b206dc6412c21, 0xf3a87204613eb0, 0x8721465b71948b9]
def page70 : List Nat := [0x2835f232632071a, 0x69b48590f58a521, 0xb90f5c8592c817, 0x7d20d21041b7196, 0xd19481b79348b19, 0x619ea1a8a10d7c8, 0xa1c8b084fecaa0c, 0xb186ba86292639e, 0x6a2d21283379348, 0xac853e2b464a0f, 0x3aea1e4b186ee2b, 0x348b196bc649ac8, 0x194fec6a2e413f8, 0xa2d22c61bd82c0b, 0x841b72126b90cf, 0x7c30287904fecaa, 0x46a1073a869ac81, 0x84fecaa1e433ea3, 0xc0292873fb1a8b8, 0xe433e3028a98cfc, 0xd83465884fec6a2, 0x2a104fec29ac857, 0x4fe4c282833f1b2, 0xd82c853e9b0a4a0]
def page71 : List Nat := [0x41afa9c64a04fa2, 0x3128b884fa2d228, 0xb90cfec2a2c653e, 0xfc6c8ac85d72128, 0x9ae213e8b0a0a1c, 0x17d93481084f8c4, 0x28b1967a86a2e2, 0x195da8d196433e3, 0x8c4a18437d8342b, 0x14213f9346b085d, 0xd72128a104fead2, 0x28a98e7c8522c61, 0x85d8c4a08413631, 0x868ac85af1926b8, 0xc633e3026b90e7a, 0xe8b60b1967c84a2, 0x64a05dc8d196433, 0xf9c65180415ea34, 0xd192837c302a2a1, 0x857cb062b1957c8, 0x23464105ba6d8ac, 0xa10e7c8b2126177, 0xfc8c8ac613ea326, 0x1942176312a2a1c]
def page72 : List Nat := [0x5cf22a8698cfead, 0x34851857a8c02c6, 0x104fec6a28437d8, 0x8c4a1c853e9b48a, 0x2841b71948a1075, 0xaf1928b184fec2a, 0x26b905f48c10421, 0xcfe0d22a633ea3, 0x87228415e31286a, 0xc613d8346b90e7a, 0xe9b60b214fe4d22, 0x41084fc8c9ae413, 0x4fc6d92c81f88b0, 0xa988413fab464a0, 0x653fb1a8a104fec, 0x834858867ec8a2c, 0xb90cfc6d92e217d, 0x6ec2a1a833ea346, 0x190417c9b481087, 0x33fb0a6b205da8d, 0x36a6a0f3a872126, 0x90cfeca98c813f8, 0x20a02c653e3028b, 0x1c653fab48498ef]
def page73 : List Nat := [0xba8a82b19798c4a, 0x46b90edc8582e43, 0x85da6d21041b721, 0x649a8413ea30a49, 0x4653fab4849879c, 0xe31287185de0d21, 0x8518edc8412c216, 0xdf64d184216e9b4, 0x2a28413f930a098, 0x63bd82c0b2167a8, 0x3126b20ebc64282, 0x5204fa8c9ae213e, 0xfe4c282873eb2c6, 0x21283aea1a6b884, 0x59ea1c8b90f6e2d, 0xb64b885f60d0ac8, 0x18eba868ac613e9, 0x8c0a1c653ea364b, 0x8263cea1c85185b, 0x5fb0a87216ba862, 0x465184fecaa1843, 0x87ca2d21643ec83, 0xc08ac65e71964b1, 0xe43b72164b18cf8]
def page74 : List Nat := [0xea2c6498cfa6d22, 0x2b196bc6522c61a, 0x4f0c0a2a63bb8ac, 0xc28a875f2320b19, 0x853f2364b885de4, 0x32a87086ea2a0ac, 0xa105da2d214653e, 0x98a519263b72122, 0xa1c65bda84a0a1f, 0x35e31287205bec2, 0xa6a105ba8d1926, 0x90cfa6c12c213fb, 0xc8d92c61d721283, 0xac813ea30a498cf, 0x9f2128b884f84c8, 0xc81084fa2d1a841, 0x973a8719283dca1, 0x848ac65ae9b48b1, 0xc61ebb0a8698edc, 0xe8b48b1973a86a0, 0x4b18fd60d190413, 0x4fa8c12c213f236, 0x721283f58348410, 0x43dd214810867ea]
def page75 : List Nat := [0x30a86a0eba871ae, 0x2a1cfc8c9a843da, 0xe22d20421bba8ca, 0x8ac653eb2e43207, 0x39ea1e4b204fc8c, 0x362b194fcc02928, 0xa073a869ac855ea, 0xa8d90c817d83464, 0x84213fab464a0d7, 0xeb8b46498fb4651, 0x46498f9c649ae43, 0x8cba6d22841e721, 0xad19621ea30a869, 0xe43cfa9a86a0cfa, 0x71964b20cba6d22, 0x65206bc651ac21b, 0x5d8c4a1e41d7214, 0xd22a61b7210a498, 0x836e9b42b214fe4, 0x234610857a6d212, 0x52067a86292837d, 0xf60d19481dc8348, 0x92c6177936a0a1d, 0x1bca80a0a1ede43]
def page76 : List Nat := [0x287184facb90c6, 0xa04fe4da8a87edb, 0xc8522c213e2b464, 0x82639ea18a0a0e7, 0xe69b485194fa8c2, 0xc6a1079a8719041, 0x84fac392c61aea1, 0xad216213f230a49, 0x841ed83465184fa, 0x721643205f0c0a1, 0x61084fc8c9ae21d, 0xcfecaa1841f88b4, 0xd1ae433f8346b90, 0x613f230a498c7a8, 0x2322a1079c6590c, 0x31867c849ac813f, 0xbc6c82c856e9b64, 0xa2c637cb062b215, 0x13fb2a87904f8c4, 0x128b184fa8d92c6, 0x2173a87194813e3, 0xc0a1e213e3022b, 0x8421b71928b90df, 0x5e9b485207b2871]
def page77 : List Nat := [0x48b90eba8782c65, 0x73a86a2c653d83, 0x2d196433e3126b2, 0x8416e9b484987ce, 0xf300a498cfa8c9a, 0x8590cfc8c9a8413, 0x4f84c8ac61f38b4, 0xd22a635e3028721, 0x653e9b0a4a0cfe4, 0xb0287206ba868ac, 0x590fd48410421dd, 0x5c84a0841d6a1c8, 0x988413eab485187, 0x1e71926390f9c64, 0xb60b90cfe4da9a8, 0xa1edc849a8413e9, 0xe0d22e437cb00a2, 0x9263af1922b184f, 0xe6a1c6590faa2d1, 0x80b215f26c10421, 0xcfa6d92c81bc82, 0x6d92c833ea360b9, 0xc65b72164b884fa, 0xea2c8498edc8582]
def page78 : List Nat := [0x8b194fa6c282839, 0xcfec2a2c61d7212, 0x4a2a636e3128698, 0x216ea3465184f8c, 0xa1a8298df28c104, 0x2a1eba629ac81ce, 0x70c0a1c813f836a, 0x1a8417ca3461087, 0x13ea346b086dc85, 0x1a83187760d2148, 0x90e7a868ac816fb, 0x8c09ac85f28b465, 0x4213f1b22b204f, 0xb790e4b207d4641, 0x4849867c8428283, 0xe7a86a2e417d83, 0x848ac813eb2c652, 0xe413fb2a878867c, 0xea364b886ba869a, 0x84104fe4da9a833, 0x57a8d19483d6a1c, 0xd28287cea1a6320, 0x213eab48518dde4, 0x21465184fe4d22c]
def page79 : List Nat := [0xb186dc64a2841e7, 0xfa8c9ae439ea0a8, 0x19281aea1c6b084, 0x16f23465186d8a5, 0x346498eba629a84, 0xafcfc8c9ae436f2, 0x50700020e0200c, 0x4ed0e0c00417808, 0xa1844000001403c, 0x46e0500925804, 0x152283c09004, 0x5422050fa00008, 0xa5828014c201108, 0x2000b98b8012b2, 0xf1c20001486a2e, 0x428417083ce6800, 0x53ec720428b, 0x211eb080835808, 0xeb80c0004a0c346, 0x6f8240200c00014, 0x1000bb81447000, 0x200346601028, 0x1f004ded9362888, 0xdb8015e8b8ab844]
def page80 : List Nat := [0xd000290009fb86, 0x10140f01c01010, 0x412b28140305c, 0x1002c0d040, 0x10280000574896, 0x44f28dd2e00024, 0x100000800010, 0x163a5e00000, 0x300403030cb876, 0x100009000, 0x9c8900000573b96, 0x30200301912804, 0x61aea34804308ea, 0x100000000000008, 0x40000000000, 0xc000000, 0x500000000002000, 0xc0000000000, 0x1c000000, 0x900000000004000, 0x140000000000, 0x2c000000, 0x10000000c480800, 0x412040000002090]
def page81 : List Nat := [0x86404000000, 0x40000004c482000, 0x43202000000a090, 0x484408000001, 0x1000000c8482000, 0x402020000019810, 0x680408000003, 0x10000c04c100800, 0x31402000200a020, 0xa026280c000501, 0x200014050500800, 0x31406000280a0a0, 0xa4282808000521, 0x30004c00c100000, 0x414020009a81020, 0x26a480804001350, 0x4d4c8501800, 0x40404000a002020, 0x286086804001400, 0x100051408101000, 0x30402000a2818a0, 0x28a642808001452, 0x10005400c500800, 0x41404000a8020a0]
def page82 : List Nat := [0x440640800001500, 0x20009144c500800, 0x2140600182990a0, 0x64a082808003053, 0x2000c948c101800, 0x404040019292020, 0x68a040808003253, 0x1000d14c8501000, 0x41402001a98a0a0, 0xa6a282804004531, 0x10015144c500800, 0x40402002aa11820, 0xc6a680804006352, 0x10019148c100800, 0x314020032299820, 0xe0a282804007051, 0x1001d4c50500800, 0x40402003aa098a0, 0x48a040c00009352, 0x5188d40818026c, 0x800019312291830, 0xa050200c040200, 0xb05028120903818, 0x84c240f070381a0]
def page83 : List Nat := [0x361b0d0642c1509, 0x1108803e1e0f070, 0x944a241208c442, 0x52281409c4e2713, 0xe168b4542a148a4, 0x8c46030178bc5c2, 0x70371b0d86c3518, 0xe1f0f4783c1e0e0, 0x1088240201007e3, 0x944622914884321, 0x2289409e4e2612c, 0x960b0572b950a65, 0xbe5e2e170b85b2c, 0x331188c4613017c, 0x1a0cc6532994ca6, 0xd86c351a8d26834, 0xc361b0d86c361b0, 0x1cce271379b0d86, 0xec763a9d4e8743a, 0xd3d9e8f2783c1dc, 0x20d0682411fcfa7, 0xe87432190a8542, 0xe45a29148a45225, 0x24d22914823d1e8]
def page84 : List Nat := [0x32984ba5d2e954a, 0xb4da6d369b4d269, 0xa8542a05027d3a9, 0x4aa551a8d44a150, 0xa54aa550a854295, 0x2ad56ab552a954a, 0x66b057abd5aac56, 0x55aad568b459acd, 0x2e570b85bad96cb, 0x7abd5e2ed76ba5d, 0x160b0582c05faf9, 0xb2190c76331186c, 0x9ccc65b2d96c964, 0x569b49a4d267b39, 0xb65b2d86bb59aad, 0xbede6f36db6da6c, 0x572b91c4e06fb7d, 0x3a5d2e9743a1cce, 0xdaed76bb5d8eb75, 0x87bbd9ecf4793bd, 0x3e9f4fa7d3e5f2f, 0xfefe7ebf1f8fb7d, 0x180c06030180c01, 0x4220f0783c12070]
def page85 : List Nat := [0x170b8542a130884, 0x87c3e1d0e8642e, 0xc4e251288c46211, 0x33188bc5e2f178a, 0x8fc7a3b1c8dc6a, 0x41976024102012, 0xc101484619e0006, 0x64c90206081090, 0x204100146204080, 0x248600b47524f0, 0x10038255860a0dc, 0x438100344811418, 0x40012c26106042, 0x21828b0c0c00104, 0x8042225814e820, 0x302095061c7c487, 0xaf630810600a810, 0x2838a0c00050f81, 0x41822a0ca320404, 0x180802068c80342, 0x6c083860818405, 0x20418806000812, 0x106081006704d9d, 0x80027a002021408]
def page86 : List Nat := [0x283722430406081, 0x282880138352d5, 0x1d830c041028e3, 0xa043034c01b033e, 0x204302063cd913, 0x3040580406dd003, 0x8704015345afc02, 0x86469c132860d5, 0x4181067d80142a0, 0x85882020808406f, 0xe7408306c9a815c, 0xc30100001821, 0x906041113800302, 0xab00a1a8706084b, 0xa0c609028008081, 0xfa6a105f4d640fe, 0x3fea1e217f258c3, 0x8cbba87197f9454, 0x4943bea2841fd15, 0xf1590bfc64a0ff1, 0xff90a10be29287f, 0x61fd5150ffc8518, 0xa0ef50e42ff214, 0x8ac657d15902f8a]
def page87 : List Nat := [0xfa2a105f8d420ff, 0xbe29261ff21902, 0x8c3f8a0a1ff4564, 0xe30ff19421ff25, 0xd35902fe4b88775, 0x7fc1721bea2843f, 0x41fe424c6fa2b21, 0xb197f85642bea2e, 0xa9a83fd43842fc8, 0xdc64105f51531ff, 0x3fe292837d35c43, 0x8c3fea2a1ffd414, 0x9631ff292877d15, 0xd458c37a86a0dfc, 0xff8ca40fea0e43f, 0x43ee32c87fa6390, 0x590ff50f21fea18, 0x1ac857c524c7dc8, 0xf8a098df4d720ff, 0xbf82e437e45c87, 0x903bc6498fe8c21, 0xf20be9a843ff25, 0xd5050ff8a2a1ff5, 0x7f51420ff21261f]
def page88 : List Nat := [0x65fe158cbf48108, 0x4a0ff45420fe02c, 0x216217d3590b7c8, 0xf82b195f4d420ff, 0x2dea1c817f25903, 0x83fc65885f5163, 0x1631ff02c65fd31, 0xe30082fc6b085f5, 0xdf14941fe8ac85f, 0x637e45843f8a0a0, 0xb195f91530bf22a, 0x12c21fe5050ffc8, 0xf8a098ff4d721be, 0xbe9ae43be42902, 0x83bc65185f9142, 0x1642fe82c65ee42, 0xd158c3fc81187f0, 0x5f8d721be9ac83f, 0x85fe40082fa2b19, 0xb217f4c640fe9ac, 0xac857f53507fc0, 0xfe0b197f50420fe, 0xfe29263fe32906, 0x503fc8a98df1494]
def page89 : List Nat := [0x1721bea2c617f53, 0xf058cbba8698df5, 0x7b90a32bf82c85f, 0x41ff0590afc8b18, 0xb215f14143fea18, 0xa2c657f5150ffa0, 0xfe4b20fe08210fe, 0xff90c61fd45c86, 0xc43fa8298ff8c94, 0x24000a088e97d45, 0x203038b8020a080, 0x9ea220a0e020e60, 0x3c08248884c021e, 0x40f39c012142830, 0x2804100f029087, 0xe0c02079e6511b, 0xa050000d001, 0x40000000100000, 0xc000000, 0x500000002, 0x1c0000000c0, 0x900000004000, 0x2c000000140000, 0x100000006000000]
def page90 : List Nat := [0x102040000810, 0x808100002040c, 0x2020a0001010300, 0x481800042408000, 0x20001810000008, 0x80006040c000302, 0x189010000c082, 0x80400000322060, 0x10200010080800, 0x4040004020a0002, 0x200010481000082, 0x1102020002110, 0x44081800220408, 0x212040009010000, 0x48200024240c001, 0x20009810000048, 0x80026040c001302, 0x989030004c480, 0x26440c001312080, 0x10100050080000, 0x40400140204000a, 0x400050481000282, 0x142204000a090, 0x50c80800286400]
def page91 : List Nat := [0x102040010810100, 0x8000042040c002, 0x60011010200088, 0x800440414002202, 0x1181030008c080, 0x4624040023020a0, 0x91000008c481800, 0x404002322060011, 0x500090081000480, 0x2412020012010, 0x90880000482408, 0x432020012110200, 0x81000620404002, 0x188103000c4, 0x800640408003202, 0x190902000c8081, 0x642410003212060, 0x8101000cc080000, 0x40c003312020019, 0xcc482000662, 0x340202001a010, 0xd0480800680408, 0x41208001a090200, 0x900000686404003]
def page92 : List Nat := [0x2101212000808c, 0x8a026280c501314, 0x80a0a0214050500, 0x26280c501434002, 0x200148505010a4, 0x801350204069a81, 0x34d490100a6a480, 0x432304009a990a0, 0x408100286480801, 0x30400a281020251, 0x50128a460805452, 0x119118200514c8, 0x484480802350204, 0x2898a0191408100, 0x464802452304012, 0xa02c149090060a, 0x803053214078299, 0xc948c101e4a460, 0x252404059292020, 0x6008006a6282807, 0x28420f0340b81e0, 0x28821d0681805a1, 0x48c02b8a8278922, 0x510e418fe3b0de3]
def page93 : List Nat := [0x113e4d12a4891c4, 0xe16c5915c5414c5, 0xd1aa68194639865, 0xb9e6779cc711ba6, 0x7a1683a047f1f67, 0x524c912368ba268, 0x22829ea76992589, 0xeab4ab2a4a6290a, 0xc2e2b6ad4b2abea, 0xdb28c7b0ec1af6b, 0xa360d534cd133cc, 0x939ce3b82dfb70d, 0x93daf23c2edbace, 0xa41f0540b003f2f, 0x7c5712c3f0dc310, 0x4c8b20c751b4651, 0x14bd2dcaf2a4a12, 0x1d013cceb38cd53, 0x2d3f4d527475154, 0xcd6b58d5d555515, 0x1606040f6157b5, 0xde52b0140ee0569, 0x20d08a6800c0820, 0x6806a00906a44a1]
def page94 : List Nat := [0x4b4048c705a960a, 0x1610ea622232120, 0x616064270e8ba60, 0x3e980a06c006046, 0x20c0a083442709a, 0x4860a0c0672181, 0xe8868706e149606, 0x69a70080604800, 0xa0e0c10d2d0361e, 0x1210040236483c6, 0x28a0a04b492c414, 0x2c002080060c8c3, 0x6140c06047844f4, 0x181206021024501, 0x63a100618540620, 0x72180c0880be0e0, 0xee4840804820c04, 0xe08900806040a9, 0xec00c1828046618, 0x45814141204004, 0x81294a8048e1806, 0x88c9a70289a669, 0x80e067418120c0a, 0x5a68020014140a6]
def page95 : List Nat := [0xaa0c824080220c2, 0x3a120a660806020, 0x1406c2be700806, 0x16120e06022a464, 0xa185e9a6c7084b8, 0x826a0a06688606a, 0xe10160612c00e08, 0x141204580806048, 0x602260aae0a02aa, 0xa02ac0602aa120, 0x44a0c12d62658ae, 0x68018349a709ca, 0xc660400120e18a6, 0xe0d0502781ac0a, 0xa045874187eae10, 0x658180c088e5c0, 0xa06c20602a60826, 0x8264089040706e0, 0x80c082206045408, 0x8c26588a1286761, 0xc02188ca6800c54, 0x5e9ac66a0a06660, 0x69e08140e0a08, 0xda52b0140edc542]
def page96 : List Nat := [0xd0ca88eaa860a58, 0x806910aa44a120, 0xa088c6c9ce692, 0x4020c049e08161, 0x268182054088014, 0x8406022a740e880, 0xe1206c00e040c2c, 0xa44a0c12d828663, 0x204023676101018, 0xba601016fa965a9, 0xc4270c656029018, 0x720c5690700e648, 0xc120aaa24060478, 0x5c100c0ececc2a1, 0x6aaf69208068e30, 0x40c52b00e14e28, 0x80480f83800228e, 0xca24080222f2840, 0xe0c628cb208042c, 0x18100e0690a89a8, 0x1296025a180e04, 0x4cb4b4aa58060, 0x6100c068e161206, 0x8e14060410069ac]
def page97 : List Nat := [0xe150e8868226208, 0xcac940a6652b00, 0xc06007a2c160602, 0x580604940afe100, 0xa5a62042218120a, 0x648264028218140, 0x4acecba601610ee, 0x45aba601016f09, 0xc38b20c042c5c0a, 0x8c9b000e0c04007, 0xc3a008290020e02, 0x2200cbc0c0638f, 0xc0e02002e3a0806, 0xc29abc080638d40, 0x48c9c12140200b6, 0xac9404ac1872180, 0x2081204020e120a, 0xa21614066806046, 0xe41f8400804020a, 0x61fa87fc21fc65f, 0x3fa83fa63fc85fa, 0xfe21fc83fe43fc6, 0xc81fa81f843fc61, 0x1380006c00f9d7f]
def page98 : List Nat := [0x10000040018002, 0x140000800003000, 0x7000030000, 0x50000240001, 0x40400000180000b, 0x120410103080810, 0x1034c08084240c2, 0x80a6240d3120298, 0x941202a0102500, 0x2a190150c802824, 0x84081c2040a1020, 0x6040e3020318100, 0x2201189038c480c, 0x1019008046440e3, 0x814824064020520, 0x64220521100904, 0x588103c40816204, 0xc848164040f2020, 0xa28405060190903, 0x4076dd92e5290f1, 0x829c6805d49d2a3, 0x620720206178059, 0x2206d040bae365c, 0x42075840248825b]
def page99 : List Nat := [0x4c2e1164a89825d, 0x64658805c508259, 0x25dd6d82074d011, 0x45a07805bc340f8, 0x4fca3cf3045aca8, 0x2821ee21484e60e, 0x5fc217e84487fd8, 0x7c81fc437a85be6, 0xa65b861f821fa43, 0x482bbc617881b, 0xa00000700002000, 0x800003700000684, 0x40000180000, 0xc08206040c0000a, 0x440c40204201010, 0x204a11014c88226, 0x18c08246040d42, 0x266440e40205201, 0x342205a1101cc88, 0x2891f69644d2440, 0x310404a4c44d30b, 0x20808c58c928808, 0x20c410120f1906, 0x452424314041882]
def page100 : List Nat := [0x8b1a3f7342441c4, 0x5708c98221ed112, 0xc986418e22c6298, 0x818e22a64985708, 0x7e4c11002864003, 0x837c25443f26190, 0x2995f49741be928, 0x92a217d5110af8a, 0xfca2214f11521bf, 0x1be82e433c454c2, 0x87de4310dfc542, 0xc530bf1ac433f45, 0xd35887da6490f78, 0x5f49631f6996437, 0x857f25d07ba6498, 0x2885fc9441bf8ae, 0x90a217f25087ec4, 0xfa2b905f45742fa, 0x68005bf721886, 0x4202013c60005e6, 0x1000004000000, 0x14000080000300, 0x120000800003000, 0xc00005800028000]
def page101 : List Nat := [0x8000380001a0000, 0x212042190410082, 0x9450e1020640402, 0xaebacb289249247, 0xcf3c90c0db6cb0b, 0x3140105d6d144f3, 0x28946202114120c, 0x209a610107339e8, 0x10104041051c566, 0x3f843fa2088a4c5, 0xfe83fe41f883fe4, 0xa61fa65fc43fa43, 0x23f885fc63fe85f, 0x9e52b0040438, 0x20000080000, 0x280001000006, 0x240000e000060, 0x22000100000780, 0x34808022040400, 0x14404013020c909, 0xf20201109038848, 0x78c141a18064240, 0x54264684e192b44, 0x2618820430a2081]
def page102 : List Nat := [0x4402d34498a2021, 0x204144a4cca3081, 0x262080873526188, 0x5790f120c415c1, 0x405902b4a4c3104, 0x62083e51a93220c, 0x6cc740688b308c0, 0x109b55b41c825d5, 0xdf315033b341d01, 0x5fd4540ef98e81, 0xe41df35d02fa2ba, 0x80887bd0720f6a0, 0xe22a21f741443f6, 0x37e82a05fd1510b, 0x41dea0e81bf41d0, 0x5d06fea0a0fbc97, 0x1310b7433c17d0, 0xc00008000040000, 0xc00014000100000, 0x284404000200001, 0x4e6314610028640, 0x324ace3083deb5a, 0x480543270612954, 0xff40df31ef20325]
def page103 : List Nat := [0xd41dd31fd10ed20, 0x4402ff41fd40f, 0x400000901c2, 0x800003000010, 0x7000030000140, 0x810000240001000, 0x320202989034c4, 0x4aa271830606624, 0x3190becc64bcafb, 0xaa0345d0bb43bc2, 0x688f932a04190b3, 0x4414fa7ec688c2c, 0xb88427e8a18d7cd, 0x107f10ffd07f0c7, 0xc80402c01ffcc7f, 0x30000100000400, 0x44240000008000, 0x47c8488624bb299, 0xe9f4fa7d3fc9046, 0x4900aa2428827d3, 0x84873649a109f09, 0xc1b8e090c212cf9, 0x1578dd16c829b32, 0xa8f1ba2d90527e5]
def page104 : List Nat := [0x6015441da8a2f2c, 0x1ed63645c60485f, 0x6486bec2246d812, 0x68d921a9f8455a3, 0x455b60486b72014, 0xf6187050a31abf8, 0x1ed438485169023, 0x6486b7c22568d92, 0x145a40ad88055a3, 0x851d268c7b58e12, 0xf6187054a31a7e5, 0x18fd861c1548863, 0x6c82bec2256d812, 0x40d921af8805451, 0x651d21442b72195, 0x70df7648650af48, 0xaf51890116c833, 0x1842be2014145b2, 0x648640dd8371c12, 0x81d954443378df7, 0xf96146d81218fd2, 0x1bf080545214429, 0x552be2014749a3, 0x7485508fe2845c6]
def page105 : List Nat := [0x649e319033719e3, 0xd46070552218ff8, 0x8dd870da604867, 0x15023f5e23149a4, 0x55121cdc678dd2, 0x455d16c827d4607, 0xd4607050a21abf8, 0x1af88055b604867, 0x6c82b7c22468d92, 0x748510a7e5851d1, 0x81c146486f9e094, 0x791e3745b20df11, 0xabf8455d268c73, 0x68c6fc201574851, 0x6d8121af88055d2, 0x55121442be2014, 0xd2195748510bf08, 0x1be78255d21442b, 0x69423f5a0705502, 0x7487108fd788c52, 0x81c151442ede115, 0x7961468d9219f92, 0x9ed281c154c869, 0x1883f48dc704851]
def page106 : List Nat := [0x145a50dda371c12, 0x55116c83b58e12, 0xe4a07055110af88, 0x8fd861c151c867, 0x48c6fc201414851, 0x745b208fd861c15, 0x81c1544873751e3, 0x755e3745b209ed2, 0xaf887551600873, 0x1442bde19574871, 0x68d921bf08051d2, 0x81c152886b62014, 0x78df76486509f51, 0xaf880551600873, 0x6c827e4a0705051, 0x50721cde578dd1, 0x81c1544863f6187, 0x70df76486408ff6, 0xed438485169433, 0x552dd961474851, 0x7486108ff8149c6, 0x55a36486b76183, 0x7e1d21cda10adc8, 0xbb78455d214427]
def page107 : List Nat := [0x1942dd961474871, 0x4885108ff8649e3, 0x651d21c42fc2015, 0xf6187055321af78, 0x1ecd21cd9268423, 0x6c82b7219548d92, 0x55921af5189411, 0x192038ab7c4607, 0x1c400282002100, 0x108445000381000, 0x6de400006255d43, 0x8180000c49d587a, 0x24f000a03000002, 0x13aad74001a, 0x4000000000, 0x800000000, 0x100000000, 0x14000000, 0x1800000, 0x1c0000, 0x20000, 0x2400, 0x280, 0x2c]
def page108 : List Nat := [0x340000000000003, 0x3c000000000000, 0x4000000000000, 0x440000000000, 0x48000000000, 0x7400000000, 0x2204000000000, 0x420458000000, 0x6404083400000, 0x6c2428180000, 0xc0282838000, 0xc02a283800, 0xc02a88380, 0xc0000022044283c, 0x40000024222083, 0x810000002c00428, 0x283c000002c0042, 0x64834000002c004, 0x620800000002c00, 0xc24281400000420, 0x6c2428180000046, 0x46c242840000004, 0x46c24284400000, 0x4ac2828380000]
def page109 : List Nat := [0x6c82a2838000, 0xc6c42080000, 0xc46c242c140, 0x4000ac06c242c14, 0x14000ac46c242c1, 0xc18000c046c242c, 0x2c14000c046c242, 0x62c18000e024c46, 0x242c08000e024c4, 0xc242c08000e028c, 0x42220c14000e02a, 0xc0242c0c000ec2, 0xe0a0020c0000220, 0x2e0c0242c140022, 0x22e0c0242c18002, 0x2ec86c420c0000, 0x46e22c640c140, 0x80046e22c640c18, 0x4ae28c242c0, 0xc0000620c6c420c, 0x2c080066e420020, 0x20c00006e82ac24, 0x620c000086e4200, 0xc420c000086e420]
def page110 : List Nat := [0x84021004016ce66, 0x2a40210070c0e02, 0x30c0e0, 0x1a3450910182030, 0x62c4c911223c68d, 0x1c3870e1c3260c1, 0x22342850a03e78e, 0x172c58a54274e95, 0xe1bb76ed9b3462c, 0x90e03f7cedd3a72, 0x9f366cc95264c78, 0x9af5eb55ab4e850, 0xdeb972ddbb76acd, 0xbd7e180e4c586f, 0x200702e1cab4684, 0xc5e141c0181f2aa, 0xe0802c5c20b8600, 0x665899140048804, 0xf2068c2d5e24bbb, 0x312e080121a0c99, 0x5012c3820730e53, 0x8e9c6c9858c6e98, 0x143163a6d92a445, 0xaf8f3548f46831e]
def page111 : List Nat := [0x2e010a974143194, 0x1443f8382428834, 0xeee2a94437e1c12, 0x2d906dd568d921b, 0xbf485269037eaba, 0x54721dfa828b641, 0x7ef1ba42a05fc70, 0xd1b2437e1c14648, 0x85ff7254521fbc8, 0xc1414437b10a2d2, 0x40dbc6e8b6417e1, 0x1ba2d904fd768c6, 0x463f70d9514876e, 0xf7655121bf8e0aa, 0x19427fbb2a518cf, 0xf0e0a8e413f5da2, 0xc090cff7149a40b, 0xf58dd214437ea36, 0x45a50fb86ca1243, 0x27e93ec2aa4fd27, 0xe93481bf94116c8, 0xdf77154921dfa6, 0xc5524867fbb2a81, 0x50bf8e0aa6437fd]
def page112 : List Nat := [0xbb2a5886f52145a, 0x6433f45f625527f, 0xd548d921dfaa283, 0x5476f2b46c90fd, 0xfacf18e413f49c6, 0xc090cff7149a509, 0x3f1d9544877f2b6, 0x50b10bf8e0a9443, 0x27ebb043204ff76, 0xe302a7fd5512144, 0xcfd27181419fa4, 0x1e46486dfba2ac9, 0x10dfce0934637fc, 0xbb2a3905ff71549, 0xc81bddd921c427f, 0xe3748620fbc6e90, 0x4876e1b0c090fd, 0xf8e0a9243f78d86, 0xac90dfc7054a31b, 0xf70dd21942fc382, 0x90a31fea2e30243, 0x27fbb2a910cfd67, 0xf206417fdc54244, 0xdfd1794320bfa2]
def page113 : List Nat := [0x4521442fe382ac9, 0x509faed10c81fd5, 0xbb243284fd76086, 0xc813f1d9544437f, 0xf2745a509faed90, 0x4442ffb92a918ef, 0xf0e090a217fdc95, 0x43086ed2149a10f, 0xf78dd21943ee1ba, 0xd8121dbe6c93421, 0xeffb92a9886fe46, 0xe8b6413f49c6050, 0xcfd1718154dfa8, 0x1e56487eeaa06c9, 0x319faed18ca17fc, 0xaba42884fd27c1a, 0x6217e1c142c43fa, 0xc6748540bf0e0a9, 0x6c82fc38283906f, 0xfa2e30285bf95d1, 0x42a86fe07d85529, 0x3f45c6054b7fb0a, 0xd8121dfc62934a1, 0x2fc83e43086de36]
def page114 : List Nat := [0xe90a21bf55116c8, 0x8fdc3654921fea8, 0x58364867fbb2a91, 0x109feecaa621f79, 0xaa2c010cfc76549, 0x481be91d600877c, 0xc7655121dfa428b, 0x6902fe3b2a8885f, 0xfeecaa641bd4851, 0x42886ff61485409, 0xbf90116c83faa0a, 0x55221bf8e0a1463, 0x2fc382a9905ff72, 0xe90e213f5db2194, 0x87de568d921feca, 0xd9424877f10a4d2, 0x20dfc0fb0a85f78, 0x3824d18ff870486, 0x4a13fdd9428c77e, 0xd3749a50dfa428b, 0x14867fbb243206f, 0xfcae93463f70d94, 0x2d287ef2149a10d, 0xbf19d215437e93a]
def page115 : List Nat := [0x8d9219fa4f83483, 0x37eab6c090ede46, 0x2302437fdc94144, 0x8dff7150921dfa4, 0x5d214427eb3ca51, 0x50fb86c30243fd9, 0xb8aa8886ff2145a, 0x4813f49f06946ff, 0xe2745a40dfc4293, 0x877f93a2d204f, 0xfa8e93463bf5516, 0xa890dfc7055132d, 0x7fdc951442ffb8a, 0x98121bdee4a8a43, 0x7ef2306c90ede36, 0xc93421b78d86048, 0x87f55488510dba6, 0xc1428867f13a2d2, 0x21bf8e0aa0437f1, 0xb3ca3905ef72505, 0x481bf485268427e, 0xc7055221dfc6293, 0x486fe3828290df, 0xfa4f18ca1f78db6]
def page116 : List Nat := [0x8510edc3698121b, 0x7bdc941c86fbb8a, 0x48640bf8e0a8a43, 0x6ffb92a890fdc37, 0x2934a1b751a3648, 0xefe4745b20dfae, 0xc154486bf2ba8c9, 0x10bf8e0a12437f1, 0xb8aa9907f647485, 0xe43bf91d268c6ff, 0xf7255132bdee4a8, 0x68c6fbb8a8490df, 0xfacf20e41bf5492, 0x2d206fd2149a509, 0xf7487368427e93a, 0x48710dfaa893463, 0x2fcb8043207f647, 0xca0e417e1c15144, 0x87de36549219fee, 0xc141c87fc382430, 0x31dfeec90c817f1, 0xb928290efd5749a, 0x421bd88516902ff, 0x55748710dde4293]
def page117 : List Nat := [0x6c877ea124d18ff, 0xfaa28b641bf5050, 0x4d287f55448710d, 0xfb485268437f38a, 0x519219fa4e302a9, 0x6fcb8043285fc70, 0x2aa6433fdd954c8, 0x4fc7650910bfee, 0x1d21c437eb8a4d2, 0x50dfaa883643fd5, 0x90a2d207de37485, 0xca17e1c1544437f, 0xe7149a409feec90, 0x19036e9b64d086f, 0xf4aeb00437f49e3, 0x2bcefd2745a40d, 0x6ad5ee70000000, 0x80004e8f7c00000, 0xb7015368a00c680, 0x2640000000000c, 0xc01c10000000020, 0xa00000060224a9, 0x500000cf00001a2, 0x27a000100018000]
def page118 : List Nat := [0xa9000022e000500, 0x173400000067c01, 0x4008b839cc01bb0, 0xcd016dc01977dcd, 0x1000c581400, 0xc1400044ac005f0, 0x40c72000075, 0xdfcde0000020a6, 0x1ea0065a4c02006, 0x1930001, 0x25c014b138fece, 0x11b0079c00dd0, 0xc28018ee5c080, 0xd810001b40803c6, 0xe5e000000000001, 0x5c8b, 0x830028c04, 0x40c59072d51e410, 0x892880000000225, 0x29a600001e401, 0x80000ae8dc04000, 0x25686400020200, 0x20019d0000000, 0xeda026aa7fb2000]
def page119 : List Nat := [0xc36c98c00000071, 0x2e6007b87ec7, 0x1394d80000060, 0x4b1491c00330000, 0xac00, 0x6000000000020, 0x1000000000, 0x280000, 0xe000000000060, 0x2000000000, 0x480000, 0x160000000000a0, 0x3000000000, 0x680000, 0x1e0000000000e0, 0x4000000000, 0x880000, 0x26000000000120, 0x5000000000, 0xa80000, 0x2e000000000160, 0x6400000000, 0xd00000, 0x3a0000000001b0]
def page120 : List Nat := [0x7c00000000, 0x1000000, 0x44000000000210, 0x8c00000000, 0x1200000, 0x4c000000000250, 0x9c00000000, 0x1400000, 0x54000000000290, 0x2040000000000, 0x408080000, 0x20a000000081040, 0x2041800000010, 0x808280000, 0x212000000101060, 0x4042800000020, 0x808680000, 0x202000000101150, 0x4240800000021, 0x848180000, 0x210000000109070, 0x4242400000021, 0x848500000, 0x2200000001090f0]
def page121 : List Nat := [0x4244400000021, 0xc48700000, 0x21a000000189140, 0x8041800000032, 0x1008680000, 0x21a000000281050, 0x22040000000050, 0x4408080000, 0x20c000000881050, 0x22041c00000110, 0x4408400000, 0x2200000008810f0, 0x22044400000110, 0x4808080000, 0x20c000000901050, 0x24041c00000120, 0x4808400000, 0x214000000901090, 0x24043400000120, 0x4808800000, 0x224000000901110, 0x24045400000120, 0x4848080000, 0x208000000909030]
def page122 : List Nat := [0x24241400000121, 0x4848300000, 0x210000000909070, 0x24242400000121, 0x4848500000, 0x2200000009090f0, 0x24244400000121, 0x4848a00000, 0x204000000a010d0, 0x28241000000141, 0x5048300000, 0x222000000a090e0, 0x28440800000141, 0x5088680000, 0x21a000000a11150, 0x2a240800000150, 0x5448200000, 0x21c000000a89050, 0x2a244000000151, 0x5488100000, 0x22a000000a910d0, 0x2a840800000152, 0x5508200000, 0x21c000000aa10d0]
def page123 : List Nat := [0x42040000000154, 0x8408080000, 0x210000001081070, 0x42042400000210, 0x8408500000, 0x22a0000010810e0, 0x44240400000220, 0x8848100000, 0x20a000001109030, 0x44241800000221, 0x8848380000, 0x212000001109080, 0x44243c00000221, 0x8848800000, 0x228000001109110, 0x46240000000221, 0x8c48380000, 0x21c000001189080, 0x46244000000231, 0x8c48880000, 0x22e000001189140, 0x46443400000231, 0x9008100000, 0x21a000001201040]
def page124 : List Nat := [0x48043800000240, 0x9008a80000, 0x2140000012090e0, 0x4a040800000242, 0x9408200000, 0x21c0000012810d0, 0x4a045400000250, 0x9448280000, 0x20a0000012890e0, 0x4a442400000252, 0xc408000000, 0x220000001881010, 0x62044400000310, 0xc808080000, 0x210000001901070, 0x64043400000320, 0xc808800000, 0x22a000001901110, 0x64240400000320, 0xc848280000, 0x20e000001909060, 0x64242000000321, 0xc848480000, 0x2200000019090f0]
def page125 : List Nat := [0x64244400000321, 0xcc08680000, 0x210000001991070, 0x68040000000332, 0xd048300000, 0x20c000001a090e0, 0x68443400000342, 0xd088a80000, 0x20a000001a81000, 0x6a243800000351, 0xd488280000, 0x22a000001a910d0, 0xc24281400000352, 0x404410300000, 0x40000008090a010, 0x48080400010210, 0x409410080002, 0x40a000081902060, 0x62081800020310, 0x84c850100004, 0x40c000130882050, 0x404083400026110, 0xd84850280006, 0x4120001b090a060]
def page126 : List Nat := [0xc24282800036121, 0xd84850800006, 0x4000001b090a110, 0x64081800040010, 0x1184850300008, 0x40a000280082000, 0x64081400050110, 0x158485028000a, 0x40600030090a020, 0x24281400060121, 0x180485030000c, 0x404000300a0a000, 0x28280c00060141, 0x180505070000c, 0x404000300a12010, 0x28480c00060142, 0x180509030000c, 0x42a000300a120d0, 0x2a280000060142, 0x180545010000c, 0x41c000300a8a030, 0x2a480400060151, 0x180549010000c, 0x40a000300a92030]
def page127 : List Nat := [0x2a483400060152, 0x1805490a8000c, 0x402000300aa2000, 0x2a880800060154, 0x180551018000c, 0x40a000300aa20e0, 0x2080000106321, 0x4401010300022, 0x40a000880282050, 0x44281800110221, 0x440c410000022, 0x4000008b0202000, 0xc0a081400116050, 0x4589010100022, 0x4040008b1202030, 0xc48481000116242, 0x4589410100022, 0x4040008b1282030, 0xc4a481000116252, 0x458c810100022, 0x40a0008b1902040, 0xc64081800116320, 0x4844410080022, 0x406000908882020]
def page128 : List Nat := [0x222081400121110, 0x4844410300024, 0x40a0009088820f0, 0x244281800121221, 0x484c410100024, 0x40a000909882030, 0x262081800121310, 0x484c850280024, 0x40600090990a060, 0x26a480c00121342, 0x4980410080024, 0x40c000930182050, 0xc08081800126030, 0x4981410280024, 0x40c000930882050, 0xc42080800126110, 0x4988410180024, 0x40c000931082050, 0xc46280000126210, 0x4988c50280024, 0x40400093118a060, 0xc48080c00126240, 0x4989010300024, 0x40400093120a000]
def page129 : List Nat := [0xc4a080c00126250, 0x4989410280024, 0x40000093128a000, 0xc42081400136210, 0x4d88410300026, 0x4200009b10820e0, 0xc42084400136210, 0x500c850100026, 0x404000a08082010, 0xc24280800142321, 0x5184850300028, 0x402000a8190a020, 0x464280800151010, 0x550041008002a, 0x404000aa190a020, 0x4280400156121, 0x580085020002c, 0x40c000b0010a050, 0x4283c00160021, 0x580085080002c, 0x40a000b0010a110, 0x44281800160221, 0x5808c5028002c, 0x40a000b0118a060]
def page130 : List Nat := [0x64281800160321, 0x584c81010002c, 0x40a000b09902040, 0x264081800161320, 0x5888c5028002c, 0x400000b1118a060, 0x22080000210010, 0x840c410000042, 0x40c00110890a050, 0x264280800221121, 0x884c850280044, 0x40a00110990a060, 0xc22081800226110, 0x8d84850080044, 0x40c0011b090a050, 0xc24282400236121, 0x8d84850500046, 0x4220011b090a100, 0xc24280800236121, 0x9184850180048, 0x4060012b090a020, 0xc24281400256121, 0x9585090a8004a, 0x40000130090a020]
def page131 : List Nat := [0x22080800310010, 0xc408410000062, 0x40c0018b1902050, 0x2080400316320, 0xc800410280064, 0x40400190810a020, 0x224281400321110, 0xc848410100064, 0x404001909102020, 0x248080800321221, 0xc849410100064, 0x40c00193118a050, 0xc62081400326231, 0xc98c410300064, 0x40a0019b1082000, 0xc42081800336210, 0xcd88410800066, 0x40c0019b1082110, 0xc44281800346021, 0xd18c850300068, 0x40a001ab010a050, 0xc62081400356221, 0xd58c85028006a, 0x404001b0090a010]
def page132 : List Nat := [0x24280c00360121, 0xd80485028006c, 0x40a001b0090a060, 0x224081800361120, 0xd84501010006c, 0x404001b08a02030, 0x228480c00361142, 0xd84541010006c, 0x404001b08a82030, 0x22a480c00361152, 0xd84551010006c, 0x400001b08aa2030, 0x428280800362141, 0xd88505018006c, 0x404001b10a8a000, 0x42a280c00362151, 0xd88551000006c, 0x406001b10aa2020, 0x824281800362154, 0xd905490a8006c, 0x4000021b1082000, 0xc0a080000536040, 0x18d884100000a6, 0x400004b08202000]
def page133 : List Nat := [0x208080000961050, 0x2984141000014c, 0x60a0831b1083000, 0x242c1836060121, 0xdc458c818286c0c, 0x60a1b88b1903060, 0xc242c1860236121, 0xc04988c5800c046, 0x60c380a10083011, 0x4020c0470146121, 0xc0558485828e02a, 0x600382a31083001, 0x242c1070556210, 0x5c18050980a200c, 0x6028b8300a93014, 0x4a4c0576010242, 0xd888490981aec02, 0x602bb1109293035, 0x442c0d76320010, 0xdc458c8182aec64, 0x60b1b88b1903068, 0xc242c1b60236121, 0xd8508c41826c046, 0x1bb0a9188304d]
def page134 : List Nat := [0x301f03004004804, 0xf41d03105a0ac1, 0x70ba15c2804a084, 0x468850fc1d43686, 0xa2ac5289f134244, 0xd819c320618bd16, 0x47c0f01d03846e8, 0x4e478891082063f, 0x14b2864ec9a12a2, 0xc8b69662be554a7, 0x30c608be97b2e85, 0x89ac34666cc898d, 0x734e51c837c6ccd, 0xc3d2784ec9d53a0, 0x2a013f87e8f91e, 0xe8710b211418821, 0x4347a8c915a2443, 0xd342614b6941252, 0xaa0d3ba754e29b, 0x2a5542a6d4b28a5, 0x95f2bb570ac956, 0x5ceb8d6dad3594b, 0x1afd5f2bd178aea, 0xc798f316620c2d8]
def page135 : List Nat := [0x5660cb996326642, 0xabb51692d119e33, 0x4db5b1b626bad69, 0x8f708dfdbdb776e, 0x5d439e730e55c8b, 0x92f15df3b876ceb, 0xbe27bef59e93cd7, 0x3601bfc7e6fc5f5, 0x8550860e4188230, 0x7c488830ee1b432, 0x1ba344608b915e2, 0xe91722a404778e1, 0x524a093526248c8, 0xf31e604bb9632ae, 0xe79c937a6bcd098, 0x2804f89e73b274c, 0x3346289d0ea1541, 0xd3ba654b69151fa, 0x92b0559aa752ea2, 0xb015eab956aacf5, 0x3c24b33652c6587, 0x7bdf2c30162b0c0, 0xc96077a468e0eae, 0x940bb6ee0ed72b4]
def page136 : List Nat := [0x58a1ed8e1bb8db9, 0x9ec2a0c0445e2d1, 0xce1307c5a6f3626, 0x1b6d1370f37b514, 0x2d8381a7939c2b7, 0xe56fba5b78c5631, 0x246a875fae04a1c, 0x8620f1c81de86c1, 0x2a92bd901d84a08, 0x80fee051d5ea455, 0x8f4781006816195, 0x53c1e0450361a8a, 0xd1f1bc2a3c6ced4, 0x9045010078481cd, 0x200a282afe1f, 0x3c5251701102810, 0xd5d1a130903c083, 0xec5e5403c1c0401, 0x50280442d158941, 0x33c38150d1501, 0x2e924b677379a03, 0xb0a8f9b11d8d609, 0x802630ab68786, 0x3e895b820080097]
def page137 : List Nat := [0x619854240501000, 0xb40c0a002abc20a, 0xec159b9341db65e, 0x91d6564b64b198c, 0xec26120700cf47, 0x3a7d30256a75c9, 0x151d8c40fd5cace, 0x764ea168e590c61, 0x221c62ac1e0e02, 0x520d1501508814, 0xdb6e27338aa0561, 0x2d6eb95cadd4d0a, 0x60b8380026b8db5, 0xd74a45c5aab098f, 0x861007814095c99, 0x40088ba7d2420a0, 0xe7c6e2b1a2a02a0, 0xc6e0721898a2fce, 0xb4503426120700c, 0x22d061104a245af, 0x541007017b06c0b, 0xe0280d363aa8e2d, 0x15e36643d220200, 0x4a525693c092a09]
def page138 : List Nat := [0x456131d81807000, 0xecc35b40a944b6b, 0x3412b196d708a0e, 0x3095e4a66129960, 0xaa2fcb184046513, 0xe2141203c1c0401, 0x70aa5adb874b856, 0xb75b9bfdf0930a9, 0x2ce6906e02ad70a, 0x13096012af2e0b4, 0x401c917dbe5f0e, 0xf8e80af1c5a2809, 0xde4158c6b70e06d, 0xb3848d91f27c2ad, 0x261208016c10f49, 0x346a33a1ce87210, 0x8332796098481c0, 0x425f21a6a10112f, 0xa0006cace83010d, 0xd5918643917031c, 0xa45d540401c0501, 0x9078380803510ee, 0x80c942391d8c0e8, 0x75a5d26c960e06]
def page139 : List Nat := [0x32f080ba1007014, 0x6c0428508038422, 0xae15670c4484309, 0xa1f05709b513858, 0x92dd884b856e51, 0x5d9c08e47218fc7, 0x76132021b010afc, 0x1455c5002ca4245, 0x2f168ac50f6c10d, 0x8218540a0185846, 0xb61b8a43891152a, 0x25632e375b2770a, 0xac880c2532c06c, 0xa61207834091, 0xa0ad278cd080502, 0xb8d464e5630f2b8, 0xbb5e0d2550482d1, 0xeefa69aac241678, 0x5813dd8cb123ed, 0x44024a0c45c378, 0x12862daa4884354, 0x4375881a8010732, 0xaa022012585f4ba, 0x9b0a2e21d524421]
def page140 : List Nat := [0x8595fc9c8f1103b, 0x1582772b8f5fadb, 0xf0130803c467cbe, 0xb8d466c6698b530, 0x8f0e8151f366391, 0xb7756ca503e236d, 0xc2585957971187d, 0x550fc0f0200dacf, 0xa752a804ea2793d, 0x2a82693751aa556, 0x114861507d56a75, 0xc6e43143619644d, 0xcb187e0a0f06380, 0x884471bb2188229, 0x8ba1d0196c40d58, 0x9022bc1e643496c, 0x3c1c9078b3cbe9, 0x125f10f14582809, 0x358ac0250161030, 0x10075b5da89bee, 0x4570bb5b8bc0f07, 0x54bdb4bc4e13830, 0x890fe1fb7d19241, 0x27c47284a41330a]
def page141 : List Nat := [0x9848200519e25, 0xc42c8a12310c2a1, 0xc53b2703b6ebe88, 0x8218401c0501e70, 0xb707c660a8f1b08, 0x405767092ea099a, 0x1298922310232dc, 0x141584c07014253, 0xe56e4b5b6e25157, 0x281e73379a03802, 0x39ad8ce0b6a8421, 0x2694d1e8810b436, 0x24204c240f02586, 0x85448a50f7479f1, 0x224a2197840d772, 0x29914d80c609840, 0x2b49eac26038081, 0x3e5d2689c182129, 0xc19854120501000, 0xd4447542e87ed42, 0xb208a3b0ea413aa, 0xd090641d359a4cc, 0x4a07a9d40541af, 0xcc63650575ac911]
def page142 : List Nat := [0xeb6a58af6c41056, 0xc5b5736c5cae36, 0x2c15b95c771c3e1, 0x3a15027e122bef5, 0x100400104191d4, 0x58f1b58b4661504, 0xf7ea2d061104220, 0x8e47e41192a0200, 0x5f65313102b007f, 0x1078380803afcf5, 0xa3c420e984bc4e8, 0x61007848197f26, 0x2d845fa8b1f905, 0x259d6ea1503dd24, 0x3e0e028bf336cdc, 0xd6e365b0240aca1, 0x5a2077a460dcd8d, 0xd0d4c32e86e6992, 0xb083cc845c08c7a, 0xf930156e3d5e82, 0xdb71d96c42a0c6c, 0x2b95b5880ab76e0, 0x6a773add139122, 0x701dbb86af0158b]
def page143 : List Nat := [0x12c1ec2a0c09521, 0x96c5816803fdfa6, 0xdeee6f184b00857, 0x3044d0201f11a75, 0xda5a9865d8e0e57, 0xc662368541db28f, 0xf3a49c1335c1d92, 0x401c0501d7a72a, 0x2b3b9d1382a0c30, 0x9028025a0200988, 0xc617811c6a216c0, 0x3c5a3b8394e2366, 0xf2026aa29baa4d1, 0x489611aad4ea54, 0x517d58332f6427b, 0x54bdb8200e0280d, 0x5862ceb852d241, 0x9cc99158c0ce976, 0x634cd669332c826, 0x849189ad66ac108, 0x6158dc1a077a1a, 0x190590acc9b3e06, 0x3cd726044d2452, 0x26108b9a8d0a815]
def page144 : List Nat := [0xe0e1784522a51c0, 0x48aece0b4f3784, 0x2552a038192b96, 0xd159ceac26056, 0x909435251557920, 0x6bb5d552a751a7, 0x4cc17c181309038, 0x17d80c6080343f9, 0x200501b55e44a0b, 0x79b6e49a88109f4, 0xc8a4320b2159873, 0x93b8810401e2391, 0x40f848865d0fdca, 0x98dc44823c04930, 0x1243078380803ce, 0x19c6ec9a1c2e885, 0x50e85409fcf9654, 0xa555942601c0417, 0xfaa54ea35050a8a, 0xa12430d861156c1, 0xf134217cb0043fe, 0x7fb0aa9fd102217, 0x57fb0283fe10c81, 0xa7fa90a217e8b48]
def page145 : List Nat := [0x4a17f834437fb12, 0x34a3fb10a217e8b, 0xab2437e8b6417f8, 0xd10421ff18a81fe, 0xff214637e30265f, 0x1ff28221fa88021, 0x21feaa621ff9002, 0xc417e8b4a5ff934, 0x8ca1fe90c41ff18, 0x1b243fea9463ff1, 0xea9221ff20621ee, 0x7fb12a9ff2b221f, 0x1fea0e41ff10c41, 0x81ff10ca1fe90a8, 0x4a3ff20e417fb0a, 0xa221ff286417e93, 0xa3043ff18e41fea, 0xea3621fea94435e, 0xfea0a437e8b4215, 0x37f834637e93421, 0x43ff10a81feaa04, 0x285fea9e41feaa4, 0xa6417fb02a37e30, 0xa14637eb0043fea]
def page146 : List Nat := [0xf082217e93443fe, 0x7e934a1fe994a1f, 0x37e302a3fea8a21, 0x437fb02a9fea144, 0x2a57fb12873eab0, 0x243ee9b4217e30, 0x83021ff232217e3, 0xf23243fe90a217f, 0xfea92657e834a5f, 0x3fea0a21fe90ca1, 0x217e30283ff2946, 0x243fea8e41fea12, 0xa265ff2b243ef1b, 0xb0aa17f83483fea, 0xe93481ffb02437f, 0x3eab6217e834837, 0x3fea9243fea1265, 0x43fa90e217fb128, 0xe417fb0a857e836, 0x2217e302a7ff28, 0x10ca1feaa243ff2, 0xe934637fb12a3fe, 0x7e934837e930217, 0x1ff28621feaa463]
def page147 : List Nat := [0x81feaa6437e8b44, 0x4857e302a9ff10c, 0x3461ff206417e83, 0x8b481ff18c817e9, 0xea8a43ef9b4217e, 0xff18aa1ff90ca1f, 0x3ff90421fea9621, 0xa1fb08221fe3024, 0x4a3fea8e43ff10a, 0xaa5fe994817e83, 0xa0e43fea16217fb, 0xe90c817e30287fe, 0xfea3243fe93421f, 0x1ff90c81ff30243, 0x21fe90aa1fe90c2, 0x15ffea1e41ff90c, 0x7c80, 0xc80146000000000, 0xaa003bbc400005, 0x1280000000000, 0x25400832880000, 0x60, 0x4026a80, 0x350013400]
def page148 : List Nat := [0x40000118009e000, 0xd0000056000048, 0x780000000000113, 0x1ea64007f8, 0x7400d70000, 0x9c1400000d80000, 0xe2001, 0x5680, 0xe80000000000000, 0xdb71f00001a2004, 0x32c00002dc4, 0x7d80000, 0x18a000000000000, 0xbe000000, 0x72, 0x982000004c00290, 0x9353801d2750000, 0x21c00730022c00, 0x400003480000000, 0x8d0000000020036, 0x983cda000023c00, 0x23a005db962b037, 0x570000000b70000, 0x19e0000000b2]
def page149 : List Nat := [0x58800ce000, 0x1090000, 0x6801ea00000000a, 0x8b808badf6, 0xfd3d8008e003280, 0x380000410100000, 0x400000000000001, 0x28400004f84, 0xd800f2000038c00, 0xab0180000008, 0x5400000000, 0x0, 0x1000000001000, 0xa00000001000000, 0x600000000, 0x280000000480, 0xe00000001a0000, 0x78000000, 0x22000000040, 0x9800000012000, 0xa00000005000000, 0x1600000002, 0x600000000b80, 0x1a0000000320000]
def page150 : List Nat := [0xd8000000, 0x3a000000070, 0xf80000001e000, 0x200000008000000, 0x2200000004, 0x900000001180, 0x2600000004a0000, 0x138000000, 0x520000000a0, 0x8000000002a000, 0x800002040400004, 0x810500001020, 0x204380000408300, 0x110000102200000, 0x80828000081, 0x2022a000040418, 0x482000010901000, 0xc00004241400008, 0x1090f00002120, 0x424440000848800, 0xd0000302000000, 0x100800000191, 0x4022a000080418, 0x82800028100000]
def page151 : List Nat := [0xa045400014, 0x8810200011020, 0x204140004408200, 0xe00011020c0002, 0x440878000881, 0x110222000220440, 0x83000090105000, 0x200024045400048, 0x9090200012120, 0x424100004848180, 0x600012120a0002, 0x484838000909, 0x121220000242420, 0x882800090911000, 0x2644180004c, 0x9911100013222, 0x804180005008100, 0xe00014021a0002, 0x500878000a01, 0x14022a000280444, 0x4808000a0900000, 0x800028240c00050, 0xa090600014120, 0x824440005048700]
def page152 : List Nat := [0x20001422020002, 0x508818000a11, 0x14220c000284410, 0x8878000a110d000, 0xa00028444400050, 0xa190000014222, 0x8643800050c8300, 0x20001432220002, 0x540828000a81, 0x15021c0002a0434, 0x880000a810f000, 0x2a045400054, 0xa890100015120, 0xa24100005448180, 0xe00015120a0002, 0x544880000a89, 0x1522040002a4404, 0x8820000a9103000, 0xa0002a441400054, 0xa910f00015221, 0xa44540005488800, 0x50001532000002, 0x54c870000a99, 0x1542000002a6440]
def page153 : List Nat := [0x810000aa101000, 0x80002a840c00055, 0xaa10d00015420, 0xa843c0005508700, 0x150001542240002, 0x840800000aa1, 0x210204000420404, 0x82000108103000, 0xc00042041400084, 0x10810e00021020, 0x204440008408800, 0x50002202040004, 0x880830001101, 0x22021e000440434, 0x88800110110000, 0x200044045400088, 0x11090400022120, 0x424180008848280, 0x800022120e0004, 0x884878001109, 0x221222000442440, 0x80000110914000, 0xa0004624000008c, 0x11890600023120]
def page154 : List Nat := [0x624200008c48380, 0x1000023121c0004, 0x8c4888001189, 0x240202000480400, 0x81800120102000, 0xc00048041000090, 0x12010d00024020, 0x8043c0009008700, 0x150002402220004, 0x904800001201, 0x241208000482404, 0x487000120906000, 0x200048244400090, 0x12110400024220, 0x844340009088300, 0x150002422220004, 0x940800001211, 0x2502040004a0404, 0x82000128103000, 0xa0004a041400094, 0x12810e00025021, 0xa04400009408780, 0x25022a0004, 0x944808001289]
def page155 : List Nat := [0x25120a0004a2410, 0x48800012890e000, 0x80004a440400094, 0x12910500025220, 0xa44400009488680, 0x25222a0004, 0xc40808001881, 0x31020a000620410, 0x87000188106000, 0x62043c000c4, 0x18811100031022, 0x40408000c808080, 0x50003202080006, 0xc80830001901, 0x32021e000640434, 0x88800190110000, 0x8000640454000c8, 0x19090500032120, 0x42424000c848300, 0x100003212140006, 0xc84888001909, 0x34022a000660434, 0x4870001a0906000, 0xa000684418000d0]
def page156 : List Nat := [0x1a810000034222, 0xa2414000d408a80, 0x500035121c0006, 0xd488a8001a91, 0x240402020420800, 0x100808121201010, 0xa0204a480404094, 0x819020601032040, 0x428180d84850280, 0x506012140806c2, 0x18048503030090a, 0x1424020c0282810, 0x5020300a1202060, 0x40c02a480418054, 0xaa20206015240, 0xa88101805510183, 0x510624140c0c02, 0x418c8502083128a, 0x32140c20c642814, 0x102088108202106, 0xc22044281444084, 0x812020411022140, 0x808004409410208, 0x411624040822c4]
def page157 : List Nat := [0x4589410008b1212, 0x25240822c4a0810, 0x10288b190204116, 0xa22c640818458c8, 0x88820612111040, 0x20818484c410289, 0x41260104022426, 0x4988c5028931082, 0x24040424c462818, 0x500093120206126, 0xa24c4a080849890, 0x3128a0012625040, 0x208004d88410009, 0x41420104022822, 0x508885018a10882, 0x310408284442810, 0x5030a3010a06142, 0x28c62081851848, 0x900820115111040, 0x4280c548441020a, 0x41522214082a44, 0x550441000a91882, 0x12140a2ac042814, 0x5028ab188205156]
def page158 : List Nat := [0x2c004281858008, 0x811020321001040, 0x8080c8848810210, 0x32212404084424, 0x884941021109282, 0x12140a44c420810, 0x10011b090a06236, 0xc48c22081090084, 0x3090a0624611040, 0x208109408410012, 0x525611040a4ac2, 0x9804850212b090a, 0x12140c4c0242814, 0x500183118a00260, 0x860c4a2800c1890, 0x812820431024040, 0x20804c800410098, 0x43202404086404, 0xc84901021901282, 0x2104006424a0810, 0x5031b0090a05336, 0xc6c2280810d8048, 0x8a120436114040, 0xa0814d84541021b]
def page159 : List Nat := [0x3611524086c22, 0xd84551021b08aa2, 0x1414086c4282800, 0x5001b10a1a06362, 0xa6c42a2810d8854, 0x10aa20036215340, 0xa8808d88551009b, 0x3621544086c42, 0x9188410031b1082, 0x240400cac420801, 0xc005b0928200b61, 0x780b81101e02803, 0x85b0aa13c250420, 0x404407a0de1a432, 0x1762b85509c12e2, 0x20f71d43886c8c9, 0x5049b92b24444c8, 0xc2fe5d4b3158294, 0xe11b7352688ca18, 0x67b8f49e43ae744, 0x32448851042013f, 0x931a5c49c9211f2, 0x34a49442824f49c, 0xabd56eac55629f5]
def page160 : List Nat := [0xb9722dc5a6b3163, 0x63ac5583b005f4b, 0xe350692ce99832b, 0xe19be3746d8d99a, 0x275ce95cb390716, 0xf3bda7acf21debb, 0x306a0b40b804fd1, 0x568930fa1cc2d84, 0x24547b8ed1a2314, 0x8f2f25a4a893725, 0x5059f73ae73cda9, 0xd298526a3744285, 0xae3596abd49a854, 0xa054b41652c4d7f, 0xf36050126a091c0, 0x5a8aa51271a4106, 0x2a14afd781e0908, 0x4d0980401b3aac, 0x904a2455849424, 0x122205e2933090f, 0x31b317130f07830, 0xb1184c15f86d8c3, 0x24251b8d4683107, 0x504894180802c20]
def page161 : List Nat := [0x8ca1350586c24d, 0x46100c8227a099e, 0x60a840280ec806c, 0x86dc01422268022, 0x2536203b4181f9b, 0x50040293097840, 0x4e41eff04ddc020, 0x4e030602d353b9d, 0x27268348b28844, 0x154a90426874365, 0xb6b90a2e0b823ae, 0x14d05556142faf8, 0x2d82a100a58480a, 0x28135c345a6bc1c, 0x45f2f5a4b9682dc, 0x481a100a04a2ad, 0x86d7044c8880e24, 0xb0737c8e4678b6c, 0x9dec9a8cc61f62, 0x2a2d7f0b1fafc14, 0x7839eaf078bd1, 0xa59e44377a49229, 0x34157fa84289879, 0xc048913c2620059]
def page162 : List Nat := [0x88ca3380606c24e, 0x4cb85289c140e53, 0x711aa952bb5d2e5, 0x9954a95329534a, 0xb8be29948a25052, 0x96badc1c0a5cb69, 0x5962cdf5eb6d70d, 0x6e15052e50c885f, 0x55ea29708742a0d, 0x93e371a1c88eaf5, 0xe0f409134341808, 0x121b02f0c40db15, 0x1111648093d5e6f, 0x248a23a810e43ab, 0x70ddc2dee022120, 0xe52222210091464, 0x230b0602c140886, 0x54d5894e12c9e4b, 0x2a162b057a995ca, 0x1ef9333f554a959, 0x47c3dcc40e04184, 0x14046677f195f46, 0xa25a4d17cb6142e, 0xeb32bc24dc5a154]
def page163 : List Nat := [0xacd64de28b6d5c0, 0x7840d848c0146f, 0xe653e59cfb1302f, 0x335f4cc7bb2c1e0, 0x3621120419efe7e, 0x67d3f9ba05a48f4, 0xb71b6f96b8f6fad, 0x8899123f5befc7d, 0x52125928900791c, 0x396ef87daf2b44, 0xfabd7d2e570f97b, 0x205824217a7f2f9, 0x495e885a544361, 0x12b243ab82a09ac, 0x30d8481610452cd, 0x150884304108255, 0xce6530850cc5008, 0x212154a26309024, 0x2782826a092c4a1, 0x6c95ba89c001504, 0x719a4d24904b0d0, 0x2b9665c1a8c8243, 0x5a5a560996a5d0a, 0x55a17cbc5b57941]
def page164 : List Nat := [0x5024b4572bd669, 0x64974b1415a9248, 0x60c83918fa473fd, 0x8551efd46be5f0f, 0x7408008b8142305, 0x802438242490c80, 0xbf9f2fa7ea58160, 0xf6947c2441c9007, 0xfaf0241e107e255, 0x2e0d66d5e830175, 0xd8b9351a16e1405, 0x913e9d4c37af8, 0x504c4d4d020a25, 0x5d2d4e104101509, 0x32c15cac597008e, 0x2043480d838182, 0xf844080928e4a05, 0xf15052a84507a04, 0x8495c6d59802443, 0x646e362bc2809a7, 0x50204c24245a1bd, 0xd6c361206024200, 0x280ec686c46100b, 0xd040045e0a11830]
def page165 : List Nat := [0x42a100a492463, 0x351c130c02a14a5, 0xcb5b248647090ad, 0x27d3c0d24288376, 0x202313898109a50, 0x4049208f3d9e268, 0x8619cd528150aa5, 0x2c5527848381bb6, 0x305810000909893, 0x960ae5604965162, 0xb60e6c945c0122a, 0x42836098110437d, 0x83ccc61218404a5, 0x26b9743a9794b22, 0xd75ae1d2e75b854, 0x47c78290ac5d7cb, 0x3f4d219c08e1200, 0xa40bf8906f36111, 0xbdcfa0e041f01ef, 0x20fd41201f2f83f, 0x5ca93822bcb4da0, 0x86ee21a72bb0a25, 0xb099cb9509e120e, 0x60a164ac124a15c]
def page166 : List Nat := [0x4009f08055201, 0xd870d848f615bb, 0xbc1605342313033, 0x83816232a9504cf, 0x88490502041450d, 0xc0803250430804a, 0x160e023ae86c240, 0x248b28954b2572b, 0x4042290e1504a14, 0x4304b6e2a1409c8, 0x1600c5883181b57, 0xb0483c213f9f08c, 0x180b964ae544, 0xa1b809c04a0502, 0xbcc42880ed0f02f, 0xb881e0e70be9caf, 0xfae67e391f2e37b, 0x323848000c08051, 0x111e0c0044c41c4, 0x32512a320904662, 0x14805126554b141, 0x8d06edc27a48241, 0x1edb6cb61ac1b6e, 0xf890906c35198c4]
def page167 : List Nat := [0x830018e10e3c36a, 0xe06a1d089e0811, 0x512042804e26838, 0xe8362012840242, 0x70945caf52a04a3, 0xc49a4428135f25d, 0xb6c36dc78bd424b, 0x24f479911e0d7bc, 0x282a59dcab12890, 0x401201283405330, 0xc8ae0931566504a, 0x463ac988af2803a, 0x2a4e0c1f03990b, 0x4d251d82c100100, 0x606014000909896, 0x300757c5fbe5fac, 0x90fe7e315f6fa62, 0x55e8180a240808d, 0x3016e0e052e186c, 0xc714642f972c461, 0xb0f4d036c90a90e, 0x8c2a1499901da0, 0xa2102ae004f074f, 0x204a09007c0aa04]
def page168 : List Nat := [0x40a0cdd2a140fc1, 0xa2db80b581f7f70, 0x60aae4ee2382b7c, 0xa21ea125e9e9707, 0xe6f041d650e1b78, 0xb7bbd934a1073d1, 0x27df29e4d89880f, 0xf6a37f3f544a07d, 0xc8e0463d1d1804a, 0x36c0552a075341, 0x5eb43bcb8201409, 0xd3aab04cb53c055, 0x2ccf47928ab8eca, 0x27c09408208183, 0x922040250541202, 0x95cac586488c172, 0x19880dc0916242c, 0x40966620407687c, 0x9a2a06c0dbc0daf, 0x21033415eaf378, 0x533c18cb023084a, 0x32424540002c201, 0x2208643101cc228, 0x509050aa5160930]
def page169 : List Nat := [0x140229aa0c4c961, 0x381b28939341838, 0x208d48aa5481934, 0x872e97326035561, 0x8d722a9509a9a0e, 0x5f83efcc980c15, 0x26820c883409885, 0x44a028a7ca00d09, 0x111a7498a32a951, 0x1d5347a3b054ee5, 0x5014d040465428, 0xf51a89409f83416, 0x3d82e0e38be4e6f, 0xfd437f1d1f4727c, 0x51feaa7f507fc83, 0xff887f943fe41fe, 0x187f487fc85fd40, 0xff50bfaa5fe31ff, 0x4cbfaa3fe10fea9, 0xbf843fe20ff10ff, 0x821fe40ff90ff94, 0x82c0fea87f443f, 0x420c20100883100, 0x80000200000c]
def page170 : List Nat := [0xa000040000180, 0xe0000680001800, 0x88000400001e000, 0xc0002a000120000, 0x190000c00005, 0x1400008000034, 0x40000054000290, 0x20c109050408082, 0x54408222040021, 0x2a424111020c881, 0x93220a909064848, 0xa01065008126441, 0x880a8241141200, 0x640142208a11025, 0x200a81055408128, 0x254880aa241151, 0x2a640152208a91, 0xd54204aa1015508, 0x8100550822a840, 0x8481c4040a10209, 0x24022120d109058, 0x201189068c482c6, 0x39008148040640, 0x148240240209201]
def page171 : List Nat := [0xa50203281009088, 0x2810494081ca040, 0x4082ca440a51201, 0x4172020588106c, 0x20b90904c808364, 0x240a0064241b21, 0x622a92878311487, 0xaaad3a8f421e8de, 0x5e8e86e35198c25, 0x8d9c4ae43188540, 0x50b0c101812414a, 0xa30b10189052a35, 0x2c40624153151a2, 0x1c58528dc30a4a, 0xc506b66ad19891, 0x3a43c44d1420292, 0xba22c507080405, 0x5090e140120d308, 0x284f1c365ca9320, 0x4c50c16284060a0, 0x1c201004029248, 0x48415262918b1, 0x81b1c5870c14203, 0x82002c538407cf0]
def page172 : List Nat := [0x305005409328341, 0xc0be80fc2071628, 0x2189416ecb8b140, 0xf205090e140120c, 0x4828852545305, 0x41aa13c11624386, 0x321414203024831, 0x58a0c15c392a34a, 0x97141a2c6020200, 0x8498d5a28405241, 0xaf040d162800444, 0x2a009942c2c5007, 0xd742c5090e18281, 0x50608700326040, 0x12105098b16283, 0x444e141c305080c, 0x2858a003ab55a83, 0x62438600482c522, 0x54a0d890e1411, 0xc36386961628305, 0x13166858a1000e9, 0x40708040110c496, 0x359c6b1a23f5628, 0x1a2]
def storagePage (p : Nat) : List Nat := (if p < 86 then (if p < 43 then (if p < 21 then (if p < 10 then (if p < 5 then (if p < 2 then (if p < 1 then page0 else page1) else (if p < 3 then page2 else (if p < 4 then page3 else page4))) else (if p < 7 then (if p < 6 then page5 else page6) else (if p < 8 then page7 else (if p < 9 then page8 else page9)))) else (if p < 15 then (if p < 12 then (if p < 11 then page10 else page11) else (if p < 13 then page12 else (if p < 14 then page13 else page14))) else (if p < 18 then (if p < 16 then page15 else (if p < 17 then page16 else page17)) else (if p < 19 then page18 else (if p < 20 then page19 else page20))))) else (if p < 32 then (if p < 26 then (if p < 23 then (if p < 22 then page21 else page22) else (if p < 24 then page23 else (if p < 25 then page24 else page25))) else (if p < 29 then (if p < 27 then page26 else (if p < 28 then page27 else page28)) else (if p < 30 then page29 else (if p < 31 then page30 else page31)))) else (if p < 37 then (if p < 34 then (if p < 33 then page32 else page33) else (if p < 35 then page34 else (if p < 36 then page35 else page36))) else (if p < 40 then (if p < 38 then page37 else (if p < 39 then page38 else page39)) else (if p < 41 then page40 else (if p < 42 then page41 else page42)))))) else (if p < 64 then (if p < 53 then (if p < 48 then (if p < 45 then (if p < 44 then page43 else page44) else (if p < 46 then page45 else (if p < 47 then page46 else page47))) else (if p < 50 then (if p < 49 then page48 else page49) else (if p < 51 then page50 else (if p < 52 then page51 else page52)))) else (if p < 58 then (if p < 55 then (if p < 54 then page53 else page54) else (if p < 56 then page55 else (if p < 57 then page56 else page57))) else (if p < 61 then (if p < 59 then page58 else (if p < 60 then page59 else page60)) else (if p < 62 then page61 else (if p < 63 then page62 else page63))))) else (if p < 75 then (if p < 69 then (if p < 66 then (if p < 65 then page64 else page65) else (if p < 67 then page66 else (if p < 68 then page67 else page68))) else (if p < 72 then (if p < 70 then page69 else (if p < 71 then page70 else page71)) else (if p < 73 then page72 else (if p < 74 then page73 else page74)))) else (if p < 80 then (if p < 77 then (if p < 76 then page75 else page76) else (if p < 78 then page77 else (if p < 79 then page78 else page79))) else (if p < 83 then (if p < 81 then page80 else (if p < 82 then page81 else page82)) else (if p < 84 then page83 else (if p < 85 then page84 else page85))))))) else (if p < 129 then (if p < 107 then (if p < 96 then (if p < 91 then (if p < 88 then (if p < 87 then page86 else page87) else (if p < 89 then page88 else (if p < 90 then page89 else page90))) else (if p < 93 then (if p < 92 then page91 else page92) else (if p < 94 then page93 else (if p < 95 then page94 else page95)))) else (if p < 101 then (if p < 98 then (if p < 97 then page96 else page97) else (if p < 99 then page98 else (if p < 100 then page99 else page100))) else (if p < 104 then (if p < 102 then page101 else (if p < 103 then page102 else page103)) else (if p < 105 then page104 else (if p < 106 then page105 else page106))))) else (if p < 118 then (if p < 112 then (if p < 109 then (if p < 108 then page107 else page108) else (if p < 110 then page109 else (if p < 111 then page110 else page111))) else (if p < 115 then (if p < 113 then page112 else (if p < 114 then page113 else page114)) else (if p < 116 then page115 else (if p < 117 then page116 else page117)))) else (if p < 123 then (if p < 120 then (if p < 119 then page118 else page119) else (if p < 121 then page120 else (if p < 122 then page121 else page122))) else (if p < 126 then (if p < 124 then page123 else (if p < 125 then page124 else page125)) else (if p < 127 then page126 else (if p < 128 then page127 else page128)))))) else (if p < 151 then (if p < 140 then (if p < 134 then (if p < 131 then (if p < 130 then page129 else page130) else (if p < 132 then page131 else (if p < 133 then page132 else page133))) else (if p < 137 then (if p < 135 then page134 else (if p < 136 then page135 else page136)) else (if p < 138 then page137 else (if p < 139 then page138 else page139)))) else (if p < 145 then (if p < 142 then (if p < 141 then page140 else page141) else (if p < 143 then page142 else (if p < 144 then page143 else page144))) else (if p < 148 then (if p < 146 then page145 else (if p < 147 then page146 else page147)) else (if p < 149 then page148 else (if p < 150 then page149 else page150))))) else (if p < 162 then (if p < 156 then (if p < 153 then (if p < 152 then page151 else page152) else (if p < 154 then page153 else (if p < 155 then page154 else page155))) else (if p < 159 then (if p < 157 then page156 else (if p < 158 then page157 else page158)) else (if p < 160 then page159 else (if p < 161 then page160 else page161)))) else (if p < 167 then (if p < 164 then (if p < 163 then page162 else page163) else (if p < 165 then page164 else (if p < 166 then page165 else page166))) else (if p < 170 then (if p < 168 then page167 else (if p < 169 then page168 else page169)) else (if p < 171 then page170 else (if p < 172 then page171 else page172))))))))
def storageWord (i : Nat) := (storagePage (i / 24)).getD (i % 24) 0
def a0Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x7cfb7cfb7cfb7cf, 0xcfb7cfb7cfb7cfb, 0xcfb7cfb7])
  | 1 => BitVec.ofNat 152 (big [0xf73ef73ef73ef73, 0x73ef73ef73ef73e, 0x73ef73ef])
  | 5 => BitVec.ofNat 152 (big [0x43804380438043, 0x438043804380438, 0x43804380])
  | _ => 0

def a0Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x409440944094409, 0x94409440944094, 0x9440944])
  | 1 => BitVec.ofNat 152 (big [0x212121212121212, 0x121212121212121, 0x12121212])
  | 5 => BitVec.ofNat 152 (big [0xedb7edb7edb7edb, 0xdb7edb7edb7edb7, 0xdb7edb7e])
  | _ => 0

def a0Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a0Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (0+i*3) 3
  | _ => 0

def a0Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a0Hints : Hints := fun _ _ => []
def a0 : Atlas := ⟨3,rawDecor 35 a0Pos a0Neg,repeatWord 9838263507696414446,a0Count,a0Rec,(fun _ _ => 0),a0Loc⟩
def a0Domains : Catalog := []
def a1Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xec79bdfaaf3bc1, 0xf0763cdefd579de, 0x6f7eabce])
  | 1 => BitVec.ofNat 152 (big [0x9f98ef5df1ee473, 0x1cfcc77aef8f723, 0xbd77c7b9])
  | 2 => BitVec.ofNat 152 (big [0x73f9bbe2c73fe0e, 0x839fcddf1639ff0, 0xef8b1cff])
  | 4 => BitVec.ofNat 152 (big [0xe776d7737f941bc, 0x6f3bb6bb9bfca0d, 0x5dcdfe50])
  | _ => 0

def a1Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x92805010030881, 0x204940280801844, 0x140400c2])
  | 1 => BitVec.ofNat 152 (big [0x904400e06002052, 0x148220070300102, 0x3818008])
  | 2 => BitVec.ofNat 152 (big [0x440242068100608, 0x822012103408030, 0x81a0401])
  | 4 => BitVec.ofNat 152 (big [0x2081a0080284124, 0x49040d004014209, 0x80200a10])
  | _ => 0

def a1Count (k : Nat) : Nat :=
  match k with
  | 3 => 8
  | 4 => 28
  | 5 => 6
  | 6 => 1
  | _ => 0

def a1Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (3+i*37) 37
  | 4 => field storageWord (389+i*26) 26
  | 5 => field storageWord (1662+i*15) 15
  | 6 => field storageWord (1851+i*4) 4
  | _ => 0

def a1Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 8 8 (field storageWord (299+(tag % 8)*4) 4) tag
  | 4 => hashRow 28 56 (field storageWord (1117+(tag % 56)*6) 6) tag
  | 5 => hashRow 6 2 (field storageWord (1752+(tag % 2)*4) 4) tag
  | 6 => 0
  | _ => 0

def a1Hints (k i : Nat) : List Nat :=
  match k with
  | 3 => hintsAt storageWord 337 4 373 2 331 2 i
  | 4 => hintsAt storageWord 1461 5 1606 2 1453 2 i
  | 5 => hintsAt storageWord 1768 5 1803 2 1760 2 i
  | 6 => hintsAt storageWord 1863 3 1869 2 1855 2 i
  | _ => []

def a1 : Atlas := ⟨6,rawDecor 23 a1Pos a1Neg,repeatWord 18374379617126377704,a1Count,a1Rec,(fun _ _ => 0),a1Loc⟩
def a1Domains : Catalog := [(repeatWord 6148914691236517205, 4), (repeatWord 3689348814741910323, 4), (repeatWord 1085102592571150095, 4), (repeatWord 281470681808895, 4)]
def a2Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xd4b8d4b8d4b8d4b, 0x4b8d4b8d4b8d4b8, 0x4b8d4b8d])
  | 4 => BitVec.ofNat 152 (big [0x7b5f7b5f7b5f7b5, 0xb5f7b5f7b5f7b5f, 0xb5f7b5f7])
  | 5 => BitVec.ofNat 152 (big [0xb010b010b010b0, 0xb010b010b010b01, 0xb010b010])
  | _ => 0

def a2Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xc137c137c137c13, 0x137c137c137c137, 0x137c137c])
  | 4 => BitVec.ofNat 152 (big [0x811281128112811, 0x112811281128112, 0x11281128])
  | 5 => BitVec.ofNat 152 (big [0xe73fe73fe73fe73, 0x73fe73fe73fe73f, 0x73fe73fe])
  | _ => 0

def a2Count (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def a2Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (1877+i*3) 3
  | _ => 0

def a2Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => 0
  | _ => 0

def a2Hints : Hints := fun _ _ => []
def a2 : Atlas := ⟨2,rawDecor 52 a2Pos a2Neg,repeatWord 1085086039514542320,a2Count,a2Rec,(fun _ _ => 0),a2Loc⟩
def a2Domains : Catalog := []
def a3Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xeadfd52997f169d, 0xa756fea94cbf8b4, 0x54a65fc5])
  | 3 => BitVec.ofNat 152 (big [0xeeffd7eb9ffbf9d, 0xe777febf5cffdfc, 0x5fae7fef])
  | 4 => BitVec.ofNat 152 (big [0x55edfbfef97ffea, 0xfaaf6fdff7cbfff, 0xeffbe5ff])
  | 5 => BitVec.ofNat 152 (big [0xffbeaff77fde97f, 0x5ffdf57fbbfef4b, 0xbfddff7a])
  | _ => 0

def a3Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xe5301b7d83484dc, 0x372980dbec1a426, 0x6df60d21])
  | 3 => BitVec.ofNat 152 (big [0x8901a4405457b91, 0xe4480d2202a2bdc, 0x9101515e])
  | 4 => BitVec.ofNat 152 (big [0x521806384a38e4a, 0x9290c031c251c72, 0x18e128e3])
  | 5 => BitVec.ofNat 152 (big [0x6865100e138c16d, 0x5b432880709c60b, 0x40384e30])
  | _ => 0

def a3Count (k : Nat) : Nat :=
  match k with
  | 2 => 2
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 0

def a3Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (1880+i*37) 37
  | 3 => field storageWord (1958+i*26) 26
  | 4 => field storageWord (2126+i*15) 15
  | 5 => field storageWord (2277+i*4) 4
  | _ => 0

def a3Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => hashRow 2 2 (field storageWord (1954+(tag % 2)*2) 2) tag
  | 3 => hashRow 6 3 (field storageWord (2114+(tag % 3)*4) 4) tag
  | 4 => hashRow 6 3 (field storageWord (2216+(tag % 3)*3) 3) tag
  | 5 => 0
  | _ => 0

def a3Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2233 4 2261 2 2225 2 i
  | 5 => hintsAt storageWord 2287 2 2291 2 2281 2 i
  | _ => []

def a3 : Atlas := ⟨5,rawDecor 60 a3Pos a3Neg,repeatWord 18379172491139481600,a3Count,a3Rec,(fun _ _ => 0),a3Loc⟩
def a3Domains : Catalog := [(repeatWord 18374966859414961920, 4), (repeatWord 17298308644996116495, 4), (repeatWord 18446462603027742720, 3), (repeatWord 18446744069414584320, 3)]
def a4Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xeffdfff7dfdfbf3, 0xffdfff7dfdfbf3f, 0xfdfbf3fe])
  | 3 => BitVec.ofNat 152 (big [0x2ea856d74e4c8e1, 0xea856d74e4c8e17, 0xe4c8e172])
  | 4 => BitVec.ofNat 152 (big [0xf5e36daabaf643f, 0x5e36daabaf643f6, 0xaf643f6f])
  | 5 => BitVec.ofNat 152 (big [0x7d96aeacfda9f0d, 0xd96aeacfda9f0dd, 0xda9f0dd7])
  | _ => 0

def a4Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x8200204040182, 0x82002040401820, 0x4018200])
  | 3 => BitVec.ofNat 152 (big [0xdd5471cbac0fc61, 0xd5471cbac0fc618, 0xc0fc618d])
  | 4 => BitVec.ofNat 152 (big [0xb109589828e435, 0xb109589828e4359, 0x28e43590])
  | 5 => BitVec.ofNat 152 (big [0xa0197144b80de09, 0x197144b80de092, 0x80de092a])
  | _ => 0

def a4Count (k : Nat) : Nat :=
  match k with
  | 3 => 15
  | 4 => 12
  | 5 => 1
  | _ => 0

def a4Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (2297+i*26) 26
  | 4 => field storageWord (2762+i*15) 15
  | 5 => field storageWord (3048+i*4) 4
  | _ => 0

def a4Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 15 15 (field storageWord (2687+(tag % 15)*5) 5) tag
  | 4 => hashRow 12 12 (field storageWord (2942+(tag % 12)*5) 5) tag
  | 5 => 0
  | _ => 0

def a4Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3003 3 3042 1 3002 1 i
  | 5 => hintsAt storageWord 3053 1 3055 1 3052 1 i
  | _ => []

def a4 : Atlas := ⟨5,rawDecor 58 a4Pos a4Neg,repeatWord 14771750482779884544,a4Count,a4Rec,(fun _ _ => 0),a4Loc⟩
def a4Domains : Catalog := [(repeatWord 71777214294589695, 4)]
def a5Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbd8debb36aeecec, 0xd8debb36aeececa, 0xaeececab])
  | 2 => BitVec.ofNat 152 (big [0xe7fffffeff3f7f3, 0x7fffffeff3f7f3f, 0xf3f7f3fe])
  | 3 => BitVec.ofNat 152 (big [0xa7032262a6286a1, 0x7032262a6286a14, 0x6286a14a])
  | 4 => BitVec.ofNat 152 (big [0x3f7e83e5dfe0a2f, 0xf7e83e5dfe0a2f7, 0xfe0a2f73])
  | _ => 0

def a5Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x40528e03ea120ec, 0x528e03ea120ec5, 0xa120ec54])
  | 2 => BitVec.ofNat 152 (big [0x100800201004700, 0x8002010047000, 0x470001])
  | 3 => BitVec.ofNat 152 (big [0x596efc2dbe6e7a9, 0x96efc2dbe6e7a9b, 0xe6e7a9b5])
  | 4 => BitVec.ofNat 152 (big [0xc4c438c4a86182b, 0x4c438c4a86182b8, 0x86182b8c])
  | _ => 0

def a5Count (k : Nat) : Nat :=
  match k with
  | 4 => 12
  | 5 => 1
  | _ => 0

def a5Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (3056+i*15) 15
  | 5 => field storageWord (3356+i*4) 4
  | _ => 0

def a5Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 12 12 (field storageWord (3236+(tag % 12)*5) 5) tag
  | 5 => 0
  | _ => 0

def a5Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3305 3 3344 2 3296 3 i
  | 5 => hintsAt storageWord 3378 3 3384 3 3360 3 i
  | _ => []

def a5 : Atlas := ⟨5,rawDecor 29 a5Pos a5Neg,repeatWord 17364368269975920880,a5Count,a5Rec,(fun _ _ => 0),a5Loc⟩
def a5Domains : Catalog := [(repeatWord 6510615555426900570, 4), (repeatWord 6172840429334713770, 4), (repeatWord 12297735558912431445, 4), (repeatWord 17298308644996116495, 4), (repeatWord 1085350949055099120, 4), (repeatWord 72056494543077120, 4)]
def a6Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfdefffffdefbddb, 0xef7ffffef7deedb, 0x7bef76df])
  | 3 => BitVec.ofNat 152 (big [0x537d8b7c299dabc, 0x9bec5be14ced5e6, 0xa676af32])
  | 4 => BitVec.ofNat 152 (big [0x3733ffe8bfafb6d, 0xb99fff45fd7db6f, 0xfebedb79])
  | 5 => BitVec.ofNat 152 (big [0x42142a082a8849, 0x210a1504154424b, 0xaa21258])
  | _ => 0

def a6Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x2009005800b0ca, 0x1004802c0058654, 0x2c32a0])
  | 3 => BitVec.ofNat 152 (big [0xa2c25e41ca95a9c, 0x1612f20e54ad4e1, 0x2a56a70d])
  | 4 => BitVec.ofNat 152 (big [0xc968046a3220b21, 0x4b4023519105908, 0xc882c846])
  | 5 => BitVec.ofNat 152 (big [0xfbd5fce5b2dfacb, 0xdeafe72d96fd65c, 0xcb7eb2e7])
  | _ => 0

def a6Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a6Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (3402+i*4) 4
  | _ => 0

def a6Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a6Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3407 1 3409 1 3406 1 i
  | _ => []

def a6 : Atlas := ⟨4,rawDecor 57 a6Pos a6Neg,repeatWord 12297641736777935530,a6Count,a6Rec,(fun _ _ => 0),a6Loc⟩
def a6Domains : Catalog := [(repeatWord 18374966859414961920, 4)]
def a7Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x0])
  | 3 => BitVec.ofNat 152 (big [0xfd9b7debd3bffd9, 0x3bffd9b7debd3bf, 0xd9b7debd])
  | 4 => BitVec.ofNat 152 (big [0xcfee9bfe6fdbcfe, 0xfdbcfee9bfe6fdb, 0xfee9bfe6])
  | 5 => BitVec.ofNat 152 (big [0xd02006a03820d0, 0x3820d02006a0382, 0xd02006a0])
  | _ => 0

def a7Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x84dfdd7df7f084d, 0x7f084dfdd7df7f0, 0x4dfdd7df])
  | 3 => BitVec.ofNat 152 (big [0xac948e18a1b8ac9, 0x1b8ac948e18a1b8, 0xc948e18a])
  | 4 => BitVec.ofNat 152 (big [0x85e1b421e68185e, 0x68185e1b421e681, 0x5e1b421e])
  | 5 => BitVec.ofNat 152 (big [0xad2dfec40f2fad2, 0xf2fad2dfec40f2f, 0xd2dfec40])
  | _ => 0

def a7Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a7Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (3410+i*4) 4
  | _ => 0

def a7Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a7Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3415 1 3417 1 3414 1 i
  | _ => []

def a7 : Atlas := ⟨4,rawDecor 58 a7Pos a7Neg,repeatWord 3674937296793318144,a7Count,a7Rec,(fun _ _ => 0),a7Loc⟩
def a7Domains : Catalog := [(repeatWord 3689348814741910323, 4)]
def a8Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x61040018008b00, 0x61040018008b00, 0x18008b00])
  | 3 => BitVec.ofNat 152 (big [0x9f1cfeff8ee8f2e, 0x9f1cfeff8ee8f2e, 0xf8ee8f2e])
  | 4 => BitVec.ofNat 152 (big [0x7ff7edfffb3fbdb, 0x7ff7edfffb3fbdb, 0xffb3fbdb])
  | 5 => BitVec.ofNat 152 (big [0x29c4240a72060ca, 0x29c4240a72060ca, 0xa72060ca])
  | _ => 0

def a8Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf9cbffa9eafdb8d, 0xf9cbffa9eafdb8d, 0x9eafdb8d])
  | 3 => BitVec.ofNat 152 (big [0x60b33819486232e, 0x60b33819486232e, 0x9486232e])
  | 4 => BitVec.ofNat 152 (big [0x810112a0ea01a89, 0x810112a0ea01a89, 0xea01a89])
  | 5 => BitVec.ofNat 152 (big [0xd4b95ddbcf472ea, 0xd4b95ddbcf472ea, 0xbcf472ea])
  | _ => 0

def a8Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a8Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (3418+i*4) 4
  | _ => 0

def a8Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a8Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3423 1 3425 1 3422 1 i
  | _ => []

def a8 : Atlas := ⟨4,rawDecor 57 a8Pos a8Neg,repeatWord 6148820870528062720,a8Count,a8Rec,(fun _ _ => 0),a8Loc⟩
def a8Domains : Catalog := [(repeatWord 18374966859414961920, 4)]
def a9Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x70cf9ffdc36f70c, 0x36f70cf9ffdc36f, 0xcf9ffdc])
  | 2 => BitVec.ofNat 152 (big [0xb329c3684ec7b32, 0xec7b329c3684ec7, 0x329c3684])
  | 3 => BitVec.ofNat 152 (big [0xc377eb983dc6c37, 0xdc6c377eb983dc6, 0x377eb983])
  | 4 => BitVec.ofNat 152 (big [0x6e1b7dab34f16e1, 0x4f16e1b7dab34f1, 0xe1b7dab3])
  | _ => 0

def a9Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x0])
  | 2 => BitVec.ofNat 152 (big [0x3706ad146c7d370, 0xc7d3706ad146c7d, 0x706ad146])
  | 3 => BitVec.ofNat 152 (big [0x4078104a8082407, 0x824078104a8082, 0x78104a8])
  | 4 => BitVec.ofNat 152 (big [0x260488046860260, 0x860260488046860, 0x60488046])
  | _ => 0

def a9Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a9Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (3426+i*4) 4
  | _ => 0

def a9Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a9Hints : Hints := fun _ _ => []
def a9 : Atlas := ⟨3,rawDecor 30 a9Pos a9Neg,repeatWord 18433229757246078156,a9Count,a9Rec,(fun _ _ => 0),a9Loc⟩
def a9Domains : Catalog := []
def a10Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x8cedcd6af718b3c, 0xf6fed7fb9f773fe, 0x5dfef6ff])
  | 2 => BitVec.ofNat 152 (big [0xf6507faa6ba8e43, 0xa56c8bdecde148c, 0xb8956335])
  | 3 => BitVec.ofNat 152 (big [0x7a1d3286acb44db, 0x5ff69cde6bcdf5e, 0xb3534bf4])
  | 4 => BitVec.ofNat 152 (big [0x65e336f709477e9, 0xe921f5f2649efab, 0xd3a3ffc3])
  | 5 => BitVec.ofNat 152 (big [0x13ffaf9553e7496, 0x98376a6db08dc3d, 0xafbe3fd8])
  | _ => 0

def a10Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x8000204400904, 0x420000040110, 0x11800000])
  | 2 => BitVec.ofNat 152 (big [0xbd425cca2389643, 0xaa7b051c9581c28, 0x8015dc7a])
  | 3 => BitVec.ofNat 152 (big [0x4a05620728b40d8, 0x552283430a07645, 0x202c0300])
  | 4 => BitVec.ofNat 152 (big [0x4421ac809036a9, 0x100804f6420e8ab, 0x24400cf2])
  | 5 => BitVec.ofNat 152 (big [0x85393d011365412, 0x6dd8020d308086c, 0x40233252])
  | _ => 0

def a10Count (k : Nat) : Nat :=
  match k with
  | 5 => 36
  | 6 => 58
  | 7 => 12
  | 8 => 1
  | _ => 0

def a10Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (3430+i*38) 38
  | 6 => field storageWord (6382+i*27) 27
  | 7 => field storageWord (13538+i*16) 16
  | 8 => field storageWord (15195+i*5) 5
  | _ => 0

def a10Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 36 72 (field storageWord (4798+(tag % 72)*7) 7) tag
  | 6 => hashRow 58 29 (field storageWord (7948+(tag % 29)*7) 7) tag
  | 7 => hashRow 12 12 (field storageWord (13730+(tag % 12)*5) 5) tag
  | 8 => 0
  | _ => 0

def a10Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 5995 6 6217 5 5302 33 i
  | 6 => hintsAt storageWord 10956 9 11487 7 8151 33 i
  | 7 => hintsAt storageWord 14630 7 14721 6 13790 21 i
  | 8 => hintsAt storageWord 15218 3 15224 3 15200 3 i
  | _ => []

def a10 : Atlas := ⟨8,rawDecor 62 a10Pos a10Neg,repeatWord 18433229757195537600,a10Count,a10Rec,(fun _ _ => 0),a10Loc⟩
def a10Domains : Catalog := [(repeatWord 3732415143318664140, 7), (repeatWord 17298308644996116495, 7), (repeatWord 3689348814741910323, 6), (repeatWord 71777214294589695, 6), (repeatWord 281470681808895, 6), (repeatWord 4294967295, 6), (repeatWord 3689517697150995660, 6), (repeatWord 3689348817318890700, 6), (repeatWord 1085102592571150095, 5), (repeatWord 18374966859414961920, 5), (repeatWord 4340410370284600380, 5), (repeatWord 18446462603027742720, 4), (repeatWord 18446744069414584320, 4), (repeatWord 3674993371882992384, 4), (repeatWord 4222189076152335, 4), (repeatWord 3689292520605548544, 3), (repeatWord 3689348813882916864, 3)]
def a11Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xfbdb7d4b6dfeec3, 0xfbdb7d4b6dfeec3, 0xb6dfeec3])
  | 2 => BitVec.ofNat 152 (big [0xdfe4ffbcf64f17e, 0xdfe4ffbcf64f17e, 0xcf64f17e])
  | 3 => BitVec.ofNat 152 (big [0x56590f606db5b8a, 0x56590f606db5b8a, 0x6db5b8a])
  | 4 => BitVec.ofNat 152 (big [0x6fde933758d75a9, 0x6fde933758d75a9, 0x758d75a9])
  | _ => 0

def a11Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x60080802012841, 0x60080802012841, 0x2012841])
  | 2 => BitVec.ofNat 152 (big [0x21080044000c01a, 0x21080044000c01a, 0x4000c01a])
  | 3 => BitVec.ofNat 152 (big [0xa96e5865d4ac39a, 0xa96e5865d4ac39a, 0x5d4ac39a])
  | 4 => BitVec.ofNat 152 (big [0x902139015a615a0, 0x902139015a615a0, 0x15a615a0])
  | _ => 0

def a11Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a11Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (15242+i*4) 4
  | _ => 0

def a11Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a11Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 15247 1 15249 1 15246 1 i
  | _ => []

def a11 : Atlas := ⟨4,rawDecor 30 a11Pos a11Neg,repeatWord 18229670727097568496,a11Count,a11Rec,(fun _ _ => 0),a11Loc⟩
def a11Domains : Catalog := [(repeatWord 281470681808895, 3)]
def a12Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x665665665665665, 0x665665665665665, 0x65665665])
  | 3 => BitVec.ofNat 152 (big [0x5b85b85b85b85b8, 0x5b85b85b85b85b8, 0xb85b85b8])
  | 5 => BitVec.ofNat 152 (big [0xfe2fe2fe2fe2fe2, 0xfe2fe2fe2fe2fe2, 0xe2fe2fe2])
  | _ => 0

def a12Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xab1ab1ab1ab1ab1, 0xab1ab1ab1ab1ab1, 0xb1ab1ab1])
  | 3 => BitVec.ofNat 152 (big [0xab1ab1ab1ab1ab1, 0xab1ab1ab1ab1ab1, 0xb1ab1ab1])
  | 5 => BitVec.ofNat 152 (big [0x0])
  | _ => 0

def a12Count (k : Nat) : Nat :=
  match k with
  | 1 => 2
  | 2 => 4
  | 3 => 1
  | _ => 0

def a12Rec (k i : Nat) : Nat :=
  match k with
  | 1 => field storageWord (15250+i*25) 25
  | 2 => field storageWord (15310+i*14) 14
  | 3 => field storageWord (15370+i*3) 3
  | _ => 0

def a12Loc (k tag : Nat) : Nat :=
  match k with
  | 1 => hashRow 2 5 (field storageWord (15300+(tag % 5)*2) 2) tag
  | 2 => hashRow 4 2 (field storageWord (15366+(tag % 2)*2) 2) tag
  | 3 => 0
  | _ => 0

def a12Hints : Hints := fun _ _ => []
def a12 : Atlas := ⟨3,rawDecor 44 a12Pos a12Neg,repeatWord 18446744069681975280,a12Count,a12Rec,(fun _ _ => 0),a12Loc⟩
def a12Domains : Catalog := []
def a13Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xe5b3168e5b3168e, 0x8e5b3168e5b3168, 0x68e5b316])
  | 3 => BitVec.ofNat 152 (big [0x96d1c9a96d1c9a9, 0xa96d1c9a96d1c9a, 0x9a96d1c9])
  | 4 => BitVec.ofNat 152 (big [0x8fe7b848fe7b848, 0x48fe7b848fe7b84, 0x848fe7b8])
  | 5 => BitVec.ofNat 152 (big [0xf796790f796790, 0x90f796790f79679, 0x790f7967])
  | _ => 0

def a13Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xcb0f83acb0f83ac, 0xacb0f83acb0f83a, 0x3acb0f83])
  | 3 => BitVec.ofNat 152 (big [0xcb0f83acb0f83ac, 0xacb0f83acb0f83a, 0x3acb0f83])
  | 4 => BitVec.ofNat 152 (big [0x0])
  | 5 => BitVec.ofNat 152 (big [0x0])
  | _ => 0

def a13Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a13Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (15373+i*4) 4
  | _ => 0

def a13Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a13Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 15378 1 15380 1 15377 1 i
  | _ => []

def a13 : Atlas := ⟨4,rawDecor 60 a13Pos a13Neg,repeatWord 18446744073709490160,a13Count,a13Rec,(fun _ _ => 0),a13Loc⟩
def a13Domains : Catalog := [(repeatWord 281470681808895, 4)]
def a14Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xf1e4f57e9a4f8c9, 0xfb5d371a990f36c, 0x7f6d7dfd])
  | 2 => BitVec.ofNat 152 (big [0x855bdb8371903f6, 0x7f37d8f5f6faeb1, 0xa7b7e743])
  | 3 => BitVec.ofNat 152 (big [0xe076fdd48b4a07e, 0xd021a33eca35f00, 0xa56c7866])
  | 4 => BitVec.ofNat 152 (big [0xba2f5aa66ce6c34, 0x799de4ef4164c6e, 0xea983ef0])
  | 5 => BitVec.ofNat 152 (big [0x9ad00bf96d2b613, 0x8de6168e5e1f9c6, 0x9f33ea7a])
  | _ => 0

def a14Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x200000000200881, 0x408440000009261, 0x1020800])
  | 2 => BitVec.ofNat 152 (big [0x414140810010046, 0x200000001800000, 0x1200])
  | 3 => BitVec.ofNat 152 (big [0xc9e7fdd14d5a07e, 0xb0630862be7481e, 0xce9df7dc])
  | 4 => BitVec.ofNat 152 (big [0x942238166cc6430, 0x97620844824040e, 0x3e4004e4])
  | 5 => BitVec.ofNat 152 (big [0x88b20730452b210, 0x184a01696686904, 0x63d2095])
  | _ => 0

def a14Count (k : Nat) : Nat :=
  match k with
  | 4 => 118
  | 5 => 672
  | 6 => 269
  | 7 => 24
  | 8 => 1
  | _ => 0

def a14Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (15381+i*49) 49
  | 5 => field storageWord (22618+i*38) 38
  | 6 => field storageWord (68797+i*27) 27
  | 7 => field storageWord (93428+i*16) 16
  | 8 => field storageWord (95950+i*5) 5
  | _ => 0

def a14Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 118 59 (field storageWord (21163+(tag % 59)*8) 8) tag
  | 5 => hashRow 672 672 (field storageWord (48154+(tag % 672)*11) 11) tag
  | 6 => hashRow 269 90 (field storageWord (76060+(tag % 90)*9) 9) tag
  | 7 => hashRow 24 12 (field storageWord (93812+(tag % 12)*6) 6) tag
  | 8 => 0
  | _ => 0

def a14Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 21955 5 22550 4 21635 32 i
  | 5 => hintsAt storageWord 59191 9 65248 7 55546 45 i
  | 6 => hintsAt storageWord 81226 11 84196 8 76870 33 i
  | 7 => hintsAt storageWord 94934 8 95134 6 93884 21 i
  | 8 => hintsAt storageWord 95961 2 95965 2 95955 2 i
  | _ => []

def a14 : Atlas := ⟨8,rawDecor 62 a14Pos a14Neg,repeatWord 18230567980125441264,a14Count,a14Rec,(fun _ _ => 0),a14Loc⟩
def a14Domains : Catalog := [(repeatWord 17298308644996116495, 7), (repeatWord 3689348814741910323, 6), (repeatWord 1085102592571150095, 6), (repeatWord 18446462598732906495, 6), (repeatWord 71777214294589695, 5), (repeatWord 281470681808895, 5), (repeatWord 4294967295, 5), (repeatWord 4340410370284600380, 5), (repeatWord 3732415143318664140, 5), (repeatWord 1085350949055099120, 5), (repeatWord 1085102596360827120, 5), (repeatWord 72056494543077120, 5), (repeatWord 71777218556133120, 5), (repeatWord 4222189076152335, 4), (repeatWord 65535, 3)]
def a15Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x2dfb5abd0f423df, 0x5f6d677d7429d5f, 0x7c4b2f96])
  | 2 => BitVec.ofNat 152 (big [0xf7eda7daf0bfd6a, 0xeff69fe7ebd7ff1, 0xe3f5f7ff])
  | 3 => BitVec.ofNat 152 (big [0x33c1104015a3952, 0x4444f4467f7f94, 0x82214c09])
  | 4 => BitVec.ofNat 152 (big [0x3e5e9d771f249b1, 0x965761320de97dc, 0x9b67dfc2])
  | 5 => BitVec.ofNat 152 (big [0xeb8a5e4ba5e92b6, 0x4b1dfcdb1637e8e, 0xc79b49c9])
  | _ => 0

def a15Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x150312b0094015f, 0x42a20955003438, 0xc8e46488])
  | 2 => BitVec.ofNat 152 (big [0x26080003082400, 0x200000800, 0x1010000])
  | 3 => BitVec.ofNat 152 (big [0x3fe3d2e6b5a3d57, 0x9cfca6e0ff73f18, 0xed7f71aa])
  | 4 => BitVec.ofNat 152 (big [0x7c0c044746249b1, 0xe2dc91404f885ce, 0x20c6b87])
  | 5 => BitVec.ofNat 152 (big [0x688f6a0a85292a6, 0xec60c2c2032f286, 0x980a8331])
  | _ => 0

def a15Count (k : Nat) : Nat :=
  match k with
  | 3 => 3
  | 4 => 60
  | 5 => 375
  | 6 => 148
  | 7 => 17
  | 8 => 1
  | _ => 0

def a15Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (95971+i*60) 60
  | 4 => field storageWord (96154+i*49) 49
  | 5 => field storageWord (99861+i*38) 38
  | 6 => field storageWord (124721+i*27) 27
  | 7 => field storageWord (140793+i*16) 16
  | 8 => field storageWord (142851+i*5) 5
  | _ => 0

def a15Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 3 3 (field storageWord (96151+(tag % 3)*1) 1) tag
  | 4 => hashRow 60 60 (field storageWord (99094+(tag % 60)*7) 7) tag
  | 5 => hashRow 375 188 (field storageWord (114111+(tag % 188)*10) 10) tag
  | 6 => hashRow 148 50 (field storageWord (128717+(tag % 50)*9) 9) tag
  | 7 => hashRow 17 17 (field storageWord (141065+(tag % 17)*5) 5) tag
  | 8 => 0
  | _ => 0

def a15Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 99520 5 99825 2 99514 2 i
  | 5 => hintsAt storageWord 119321 9 122705 7 115991 45 i
  | 6 => hintsAt storageWord 133655 10 135145 8 129167 33 i
  | 7 => hintsAt storageWord 142221 7 142347 6 141150 21 i
  | 8 => hintsAt storageWord 142864 3 142870 2 142856 2 i
  | _ => []

def a15 : Atlas := ⟨8,rawDecor 61 a15Pos a15Neg,repeatWord 18085032214235095280,a15Count,a15Rec,(fun _ _ => 0),a15Loc⟩
def a15Domains : Catalog := [(repeatWord 6510615555426900570, 7), (repeatWord 18374966859414961920, 6), (repeatWord 281470681808895, 6), (repeatWord 4294967295, 6), (repeatWord 12297829382473034410, 5), (repeatWord 1085102592571150095, 5), (repeatWord 6172840429334713770, 5), (repeatWord 12297735558912431445, 5), (repeatWord 12297829381041378645, 5), (repeatWord 17298308644996116495, 5), (repeatWord 1085350949055099120, 5), (repeatWord 1085102596360827120, 5), (repeatWord 723401728380766730, 4)]
def a16Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf93bdef375f2ef5, 0x4bbfdf76f3f97ea, 0xffbfbb9e])
  | 1 => BitVec.ofNat 152 (big [0x1feff5dcaf2df4a, 0xfdebbddb3dde857, 0x1d4adcef])
  | 2 => BitVec.ofNat 152 (big [0xb6dc653dde5d1be, 0xffeaebbfcebfbff, 0x7bfef7e7])
  | 4 => BitVec.ofNat 152 (big [0xcdaf3a7ba997a1d, 0xcffd9f38a7c0e61, 0xea595af9])
  | 5 => BitVec.ofNat 152 (big [0x5df1bee3b0ab47b, 0x313dc5539a33691, 0xb6af5e53])
  | _ => 0

def a16Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x390a901145b2ca0, 0xd000c600803c408, 0x8428102a])
  | 1 => BitVec.ofNat 152 (big [0x1a1459a6c29b40, 0x10de99412596005, 0xa0200424])
  | 2 => BitVec.ofNat 152 (big [0x84142824124401e, 0xf20209a4a001f2, 0x110080d0])
  | 4 => BitVec.ofNat 152 (big [0x44b818eaa99521d, 0xa11869b9c9c0a6c, 0x6f045d84])
  | 5 => BitVec.ofNat 152 (big [0x38512fcfb00b47b, 0x2667391b1b01321, 0x600ea299])
  | _ => 0

def a16Count (k : Nat) : Nat :=
  match k with
  | 5 => 2
  | 6 => 12
  | 7 => 1
  | _ => 0

def a16Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (142878+i*27) 27
  | 6 => field storageWord (142945+i*16) 16
  | 7 => field storageWord (144036+i*5) 5
  | _ => 0

def a16Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 2 2 (field storageWord (142932+(tag % 2)*2) 2) tag
  | 6 => hashRow 12 24 (field storageWord (143137+(tag % 24)*5) 5) tag
  | 7 => 0
  | _ => 0

def a16Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 142937 2 142943 1 142936 1 i
  | 6 => hintsAt storageWord 143698 6 143776 5 143257 21 i
  | 7 => hintsAt storageWord 144056 3 144062 3 144041 3 i
  | _ => []

def a16 : Atlas := ⟨7,rawDecor 55 a16Pos a16Neg,repeatWord 16927598236463063264,a16Count,a16Rec,(fun _ _ => 0),a16Loc⟩
def a16Domains : Catalog := [(repeatWord 6510615555426900570, 6), (repeatWord 281470681808895, 5), (repeatWord 18446462603027742720, 5), (repeatWord 4294967295, 5), (repeatWord 18446744069414584320, 5), (repeatWord 723401728380766730, 4)]
def a17Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbb7d861b5db770f, 0xb7d861b5db770f7, 0xdb770f7b])
  | 1 => BitVec.ofNat 152 (big [0x5dcffff4bafb9fa, 0xdcffff4bafb9faf, 0xafb9faf5])
  | 2 => BitVec.ofNat 152 (big [0xebfdfb7fdf85f35, 0xbfdfb7fdf85f35e, 0xf85f35ee])
  | 3 => BitVec.ofNat 152 (big [0x95bbe6f0e47feca, 0x5bbe6f0e47fecad, 0x47fecad9])
  | _ => 0

def a17Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x4c28691a0c4b50b, 0xc28691a0c4b50b8, 0xc4b50b84])
  | 1 => BitVec.ofNat 152 (big [0xa120210280d1168, 0x120210280d11680, 0xd11680a])
  | 2 => BitVec.ofNat 152 (big [0x104302a45100a14, 0x4302a45100a141, 0x100a1411])
  | 3 => BitVec.ofNat 152 (big [0x5a40d2dc012ce82, 0xa40d2dc012ce822, 0x12ce8225])
  | _ => 0

def a17Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a17Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (144077+i*4) 4
  | _ => 0

def a17Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a17Hints : Hints := fun _ _ => []
def a17 : Atlas := ⟨3,rawDecor 15 a17Pos a17Neg,repeatWord 17068903038525172960,a17Count,a17Rec,(fun _ _ => 0),a17Loc⟩
def a17Domains : Catalog := []
def a18Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x9fab1e759bac92d, 0xf6ceb5a7766d732, 0xe5cc95aa])
  | 1 => BitVec.ofNat 152 (big [0xeec5fd9ba47ddea, 0x7fff6b7cafdae9e, 0xf87bffff])
  | 2 => BitVec.ofNat 152 (big [0x73bf63ecdfd3355, 0xdf2db5f3f6e796b, 0xefefaf23])
  | 3 => BitVec.ofNat 152 (big [0x9650f5936e0e69e, 0x73df5e89dfbcbf7, 0x72bfcafd])
  | 4 => BitVec.ofNat 152 (big [0xabc7cb2d332ef8, 0x9afdb367903c55d, 0x97d99b1c])
  | _ => 0

def a18Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x92581a6c83ac12c, 0x1c2c20575c610, 0x84044430])
  | 1 => BitVec.ofNat 152 (big [0xc105498035d02, 0x904604448a02014, 0x24020202])
  | 2 => BitVec.ofNat 152 (big [0x412420805c42241, 0x62051992021802, 0x50208904])
  | 3 => BitVec.ofNat 152 (big [0x97105ab02e0a09c, 0x4e282a1815b01a3, 0x109209d])
  | 4 => BitVec.ofNat 152 (big [0xda906c361310ef8, 0x98932923881f1c8, 0x19ee84c3])
  | _ => 0

def a18Count (k : Nat) : Nat :=
  match k with
  | 4 => 4
  | 5 => 31
  | 6 => 13
  | 7 => 1
  | _ => 0

def a18Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (144081+i*38) 38
  | 5 => field storageWord (144272+i*27) 27
  | 6 => field storageWord (146005+i*16) 16
  | 7 => field storageWord (147217+i*5) 5
  | _ => 0

def a18Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 4 13 (field storageWord (144233+(tag % 13)*3) 3) tag
  | 5 => hashRow 31 16 (field storageWord (145109+(tag % 16)*6) 6) tag
  | 6 => hashRow 13 13 (field storageWord (146213+(tag % 13)*5) 5) tag
  | 7 => 0
  | _ => 0

def a18Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 145583 6 145775 5 145205 21 i
  | 6 => hintsAt storageWord 146719 7 146817 5 146278 21 i
  | 7 => hintsAt storageWord 147252 3 147258 3 147222 5 i
  | _ => []

def a18 : Atlas := ⟨7,rawDecor 31 a18Pos a18Neg,repeatWord 18224076343214664928,a18Count,a18Rec,(fun _ _ => 0),a18Loc⟩
def a18Domains : Catalog := [(repeatWord 11068046444225730969, 6), (repeatWord 6510615555426900570, 6), (repeatWord 3732415143318664140, 6), (repeatWord 17298308644996116495, 6), (repeatWord 6148914691236517205, 5), (repeatWord 71777214294589695, 5), (repeatWord 18446462603027742720, 5), (repeatWord 6172840429334713770, 5), (repeatWord 12297735558912431445, 5), (repeatWord 4340410370284600380, 5), (repeatWord 14757226376558555955, 5), (repeatWord 3689517697150995660, 5), (repeatWord 17361393124654452495, 5), (repeatWord 1085350949055099120, 5), (repeatWord 18374687579166474495, 5), (repeatWord 281470681808895, 4), (repeatWord 6148820867675914240, 4), (repeatWord 71776119077928960, 4)]
def a19Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x77c1baaf1e4f123, 0xf9ab3f3fff2792e, 0xfa50f7d7])
  | 1 => BitVec.ofNat 152 (big [0xdc36df56e2a0aff, 0x5ee6d1ce54ea6eb, 0xc5fefffb])
  | 3 => BitVec.ofNat 152 (big [0x8e2c6ff055b5cb0, 0xb6f7edcb48fbb35, 0xaa4f5a89])
  | 4 => BitVec.ofNat 152 (big [0x37dd3c2fd9f9445, 0x1f13f53928d8376, 0xbe8d0569])
  | 5 => BitVec.ofNat 152 (big [0xfcc47e5b1aa9833, 0x4f20e048102232c, 0x32024a93])
  | _ => 0

def a19Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x9800282020d120, 0xac015421d00120, 0x2000])
  | 1 => BitVec.ofNat 152 (big [0x44001041802080f, 0x1a20140028603, 0x50044401])
  | 3 => BitVec.ofNat 152 (big [0xa884692035854b0, 0x5a4149035bd3020, 0x25c82284])
  | 4 => BitVec.ofNat 152 (big [0xf6520c4559f0045, 0x24162a19208c416, 0xcaa0c982])
  | 5 => BitVec.ofNat 152 (big [0xfd943fdb9bad93f, 0xcafbbfffbdbb7bf, 0x59fd6da7])
  | _ => 0

def a19Count (k : Nat) : Nat :=
  match k with
  | 4 => 3
  | 5 => 17
  | 6 => 9
  | 7 => 1
  | _ => 0

def a19Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (147276+i*38) 38
  | 5 => field storageWord (147394+i*27) 27
  | 6 => field storageWord (148272+i*16) 16
  | 7 => field storageWord (148963+i*5) 5
  | _ => 0

def a19Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 3 2 (field storageWord (147390+(tag % 2)*2) 2) tag
  | 5 => hashRow 17 9 (field storageWord (147853+(tag % 9)*5) 5) tag
  | 6 => hashRow 9 9 (field storageWord (148416+(tag % 9)*5) 5) tag
  | 7 => 0
  | _ => 0

def a19Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 148098 5 148188 4 147898 20 i
  | 6 => hintsAt storageWord 148755 6 148815 4 148461 21 i
  | 7 => hintsAt storageWord 148986 3 148992 3 148968 3 i
  | _ => []

def a19 : Atlas := ⟨7,rawDecor 59 a19Pos a19Neg,repeatWord 17197783015849127662,a19Count,a19Rec,(fun _ _ => 0),a19Loc⟩
def a19Domains : Catalog := [(repeatWord 6148914691236517205, 5), (repeatWord 3689348814741910323, 5), (repeatWord 71777214294589695, 5), (repeatWord 18374966859414961920, 5), (repeatWord 281470681808895, 5), (repeatWord 18446462603027742720, 5), (repeatWord 18446744069414584320, 4), (repeatWord 6148820867675914240, 4), (repeatWord 3674993371882992384, 4), (repeatWord 1095216660735, 4)]
def a20Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfe29124e3132d9d, 0x139a7ba65ecdffa, 0x27df5fd4])
  | 1 => BitVec.ofNat 152 (big [0x73dd1d85ebad54a, 0xdc2682f9fda7e65, 0x7effaf7f])
  | 2 => BitVec.ofNat 152 (big [0xccbff9fb9c4be65, 0x7afbffff8a7cab6, 0xdda8d89e])
  | 4 => BitVec.ofNat 152 (big [0xf546ee7646f4aba, 0xbdc5f5d9f59a71f, 0xbe772ca9])
  | 5 => BitVec.ofNat 152 (big [0xb3de5aa279923f2, 0xe7f092ba464dd58, 0xf5621fe4])
  | _ => 0

def a20Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xd02804042022d9c, 0xa02405844873f92, 0x29040878])
  | 1 => BitVec.ofNat 152 (big [0x38015002b28402, 0x2109081520ea4, 0x960a102c])
  | 2 => BitVec.ofNat 152 (big [0xc1308129041061, 0xc8000330004000, 0x800001])
  | 4 => BitVec.ofNat 152 (big [0x700462404494a88, 0x9018b004809a011, 0x49500a42])
  | 5 => BitVec.ofNat 152 (big [0xa86c39b29992372, 0x2c102288470c049, 0xc6bcf690])
  | _ => 0

def a20Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a20Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (149010+i*5) 5
  | _ => 0

def a20Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a20Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 149016 1 149018 1 149015 1 i
  | _ => []

def a20 : Atlas := ⟨7,rawDecor 55 a20Pos a20Neg,repeatWord 18374379617092690144,a20Count,a20Rec,(fun _ _ => 0),a20Loc⟩
def a20Domains : Catalog := [(repeatWord 18446744069414584320, 7)]
def a21Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbecffbb3e5fcd77, 0xe7dddffc3b7fa7d, 0xfd47ff4e])
  | 2 => BitVec.ofNat 152 (big [0xff3fffff9efb6cf, 0xff3befdbef9afcf, 0xffffe1ff])
  | 3 => BitVec.ofNat 152 (big [0xd3b5c54e9e1f39c, 0xfefbb07bd6eb5c7, 0x8fb958ff])
  | 4 => BitVec.ofNat 152 (big [0xa5f51728ebccfb8, 0x6df432adf7ff932, 0xb83b3fbd])
  | 5 => BitVec.ofNat 152 (big [0xe0dc41fe7547b3b, 0x32fe50f67c777f2, 0xfedf9f96])
  | _ => 0

def a21Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x42c32bb2a52c526, 0x33224411d2005, 0xa0711042])
  | 2 => BitVec.ofNat 152 (big [0xb838500502d30c9, 0x914c84914e0c888, 0x1804841c])
  | 3 => BitVec.ofNat 152 (big [0x4b54a3189c1e394, 0x6732287e90aa456, 0x2f146b01])
  | 4 => BitVec.ofNat 152 (big [0x87050e2d0acce38, 0x5ae8848f6ae7930, 0x636ba548])
  | 5 => BitVec.ofNat 152 (big [0xe1c641565541b1b, 0xea4d16232c15b5e, 0xc010438d])
  | _ => 0

def a21Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a21Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (149019+i*5) 5
  | _ => 0

def a21Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a21Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 149025 1 149027 1 149024 1 i
  | _ => []

def a21 : Atlas := ⟨6,rawDecor 61 a21Pos a21Neg,repeatWord 18062513829545287840,a21Count,a21Rec,(fun _ _ => 0),a21Loc⟩
def a21Domains : Catalog := [(repeatWord 18374966859414961920, 6)]
def a22Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xc21ddddf6ecbefc, 0x77ffdde9ff4e677, 0xc86fddb9])
  | 1 => BitVec.ofNat 152 (big [0xfff3ff7fff7fd53, 0xff673f3ef5bdbaf, 0x7ff3fb7f])
  | 3 => BitVec.ofNat 152 (big [0xfdeb67f5b5b5b17, 0xeb47e7d661f5b9b, 0x7ff77ece])
  | 4 => BitVec.ofNat 152 (big [0x90dcbcf634ae6ed, 0xffbdc2dfbf4357d, 0xaa6fa5a6])
  | 5 => BitVec.ofNat 152 (big [0x569f7c8afac63be, 0x3bfdbed3b7f4d0, 0xd7ecbdf3])
  | _ => 0

def a22Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x2154bdc0cc9af0, 0x4a4c66d1b9842a2, 0x52a8b25])
  | 1 => BitVec.ofNat 152 (big [0xb010a642d273442, 0x8089092a4024c0c, 0x1e015080])
  | 3 => BitVec.ofNat 152 (big [0x47eb01912584b15, 0x3830221529823b1, 0x607e815a])
  | 4 => BitVec.ofNat 152 (big [0xa0aa3d24f42e62d, 0x31342c9b2443565, 0x585065c5])
  | 5 => BitVec.ofNat 152 (big [0x53025402fa8619e, 0xa3e383461b5bf94, 0x69128098])
  | _ => 0

def a22Count (k : Nat) : Nat :=
  match k with
  | 4 => 2
  | 5 => 6
  | 6 => 1
  | _ => 0

def a22Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (149028+i*27) 27
  | 5 => field storageWord (149086+i*16) 16
  | 6 => field storageWord (149390+i*5) 5
  | _ => 0

def a22Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 2 4 (field storageWord (149082+(tag % 4)*1) 1) tag
  | 5 => hashRow 6 12 (field storageWord (149182+(tag % 12)*4) 4) tag
  | 6 => 0
  | _ => 0

def a22Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 149335 4 149363 3 149230 21 i
  | 6 => hintsAt storageWord 149407 3 149413 2 149395 3 i
  | _ => []

def a22 : Atlas := ⟨6,rawDecor 59 a22Pos a22Neg,repeatWord 17197783014986796032,a22Count,a22Rec,(fun _ _ => 0),a22Loc⟩
def a22Domains : Catalog := [(repeatWord 12297829382473034410, 5), (repeatWord 71777214294589695, 5), (repeatWord 3732415143318664140, 5), (repeatWord 18446462603027742720, 4), (repeatWord 18446744069414584320, 4)]
def a23Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xc18be65550c64cb, 0x9d45adca9337c7b, 0xdbeb2d65])
  | 1 => BitVec.ofNat 152 (big [0x22051df6ba53825, 0xeddf67edfdffbe7, 0xe65d7a1c])
  | 2 => BitVec.ofNat 152 (big [0xfd7ece6957a8b5a, 0x77e0fc174fa801a, 0x8fcfbde3])
  | 4 => BitVec.ofNat 152 (big [0x2de82a57655c7e0, 0x43a83ee996bcf34, 0xdaba1dda])
  | 5 => BitVec.ofNat 152 (big [0x1abcec9a4e3e496, 0x402ffcb35994679, 0xb9fbc247])
  | _ => 0

def a23Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xc049064828c24c3, 0x66b1c2e7066cfa, 0x24099410])
  | 1 => BitVec.ofNat 152 (big [0x0])
  | 2 => BitVec.ofNat 152 (big [0x10041001600a18, 0x1000088000, 0x50c04808])
  | 4 => BitVec.ofNat 152 (big [0xaed00855e05c560, 0x91f9a0d32a02234, 0xa30e1204])
  | 5 => BitVec.ofNat 152 (big [0x463dbc1a483e086, 0x6c90b6684b54005, 0x60004e4])
  | _ => 0

def a23Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a23Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (149421+i*5) 5
  | _ => 0

def a23Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a23Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 149427 1 149429 1 149426 1 i
  | _ => []

def a23 : Atlas := ⟨6,rawDecor 55 a23Pos a23Neg,repeatWord 18374401693224594668,a23Count,a23Rec,(fun _ _ => 0),a23Loc⟩
def a23Domains : Catalog := [(repeatWord 3689348814741910323, 6)]
def a24Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf8904ddfc65f161, 0x7b1f9ecbf1f7b26, 0xfeafe5bc])
  | 1 => BitVec.ofNat 152 (big [0x2e6ae6b51121fd9, 0x66e7adec534fcfd, 0x5c99fa4f])
  | 2 => BitVec.ofNat 152 (big [0x9377f04abd984ae, 0xbd7fc33d2fe8d2f, 0xa7f97c79])
  | 3 => BitVec.ofNat 152 (big [0x770dbb3cb8e3a36, 0x99f1ee383c8e8d3, 0x134eb747])
  | 4 => BitVec.ofNat 152 (big [0x48c769fcca56c5c, 0xbeed92c79b39353, 0x3f6781c0])
  | _ => 0

def a24Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x800811050249021, 0x800042298083922, 0xc800802])
  | 1 => BitVec.ofNat 152 (big [0x284082300120158, 0x200910104148208, 0x426025])
  | 2 => BitVec.ofNat 152 (big [0x1384400a0410486, 0x900a0820220405, 0x40050048])
  | 3 => BitVec.ofNat 152 (big [0xc408300598c3a20, 0xc6500521bc14812, 0xaa888080])
  | 4 => BitVec.ofNat 152 (big [0x5836ada8816c5c, 0x173d84805518649, 0x3056421d])
  | _ => 0

def a24Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a24Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (149430+i*5) 5
  | _ => 0

def a24Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a24Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 149436 1 149438 1 149435 1 i
  | _ => []

def a24 : Atlas := ⟨6,rawDecor 31 a24Pos a24Neg,repeatWord 18368772107823414504,a24Count,a24Rec,(fun _ _ => 0),a24Loc⟩
def a24Domains : Catalog := [(repeatWord 18374687579166474495, 7)]
def a25Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xffdef65fffcafa6, 0xffffffff6d737dc, 0x5cbaf7ff])
  | 2 => BitVec.ofNat 152 (big [0xf37359b970357df, 0xcec84bc89bcf86f, 0xa34fee0d])
  | 3 => BitVec.ofNat 152 (big [0x47f93de10b7585b, 0xcce55e2cff9ccb7, 0xffcdf874])
  | 4 => BitVec.ofNat 152 (big [0xed2d0b34d53993c, 0xe6f764facaa3db5, 0x17bc4dcc])
  | 5 => BitVec.ofNat 152 (big [0x6e3cedc6c1de551, 0x794ffc0513cdb5e, 0xe64760db])
  | _ => 0

def a25Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x4020040802220, 0x80100200002040, 0x8])
  | 2 => BitVec.ofNat 152 (big [0xf932400b50115cf, 0x2ca540a9784009, 0x1a89e383])
  | 3 => BitVec.ofNat 152 (big [0x68318e08365813, 0x77087b1d6f08c14, 0x20b00444])
  | 4 => BitVec.ofNat 152 (big [0xf90c0b70853891c, 0x8160a45238896bd, 0xf41b0fa7])
  | 5 => BitVec.ofNat 152 (big [0xceb8076ac1dc550, 0x613606411049f0f, 0xc01edb06])
  | _ => 0

def a25Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a25Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (149439+i*5) 5
  | _ => 0

def a25Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a25Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 149445 1 149447 1 149444 1 i
  | _ => []

def a25 : Atlas := ⟨6,rawDecor 62 a25Pos a25Neg,repeatWord 18216212550151621824,a25Count,a25Rec,(fun _ _ => 0),a25Loc⟩
def a25Domains : Catalog := [(repeatWord 281470681808895, 6)]
def a26Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x25ff77edffb349f, 0x7dbffafdb6fff6f, 0x69fe7dff])
  | 2 => BitVec.ofNat 152 (big [0xfb8fdfdfd66dbf6, 0xf37f7f6a6f3d7d1, 0xbee7bb36])
  | 3 => BitVec.ofNat 152 (big [0xfef5ba3a29def79, 0xefec8df7fdc2aff, 0xd7fbfecd])
  | 4 => BitVec.ofNat 152 (big [0x297b9c123c86b4e, 0xc81394ce6df159d, 0x1675eacf])
  | 5 => BitVec.ofNat 152 (big [0xd31c2e7cee68e2b, 0x17f2c7544ec3693, 0xc8a7a2d7])
  | _ => 0

def a26Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x1dd20401d23400, 0x2018209102bc021, 0x4620a19])
  | 2 => BitVec.ofNat 152 (big [0x200d30f42083f6, 0xc98141683801590, 0x9817020])
  | 3 => BitVec.ofNat 152 (big [0xec00103900dc919, 0x10a508045542acc, 0xaa04c484])
  | 4 => BitVec.ofNat 152 (big [0xa63bec407c86a4e, 0x6b2460c76d2b109, 0xd4742676])
  | 5 => BitVec.ofNat 152 (big [0x9304af50ee60e2b, 0xd32aacc005e6f3b, 0x525c1728])
  | _ => 0

def a26Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a26Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (149448+i*5) 5
  | _ => 0

def a26Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a26Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 149454 1 149456 1 149453 1 i
  | _ => []

def a26 : Atlas := ⟨5,rawDecor 62 a26Pos a26Neg,repeatWord 18212834798890699968,a26Count,a26Rec,(fun _ _ => 0),a26Loc⟩
def a26Domains : Catalog := [(repeatWord 281470681808895, 5)]
def a27Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x99f4141c5f57861, 0xd7dcdcb9dd53ed5, 0x3f9f7983])
  | 2 => BitVec.ofNat 152 (big [0x2e0b5f6775e8498, 0xad717fe66f77938, 0xbf7fce7c])
  | 3 => BitVec.ofNat 152 (big [0xa1326cda729c993, 0xc69c27ebc86b4f3, 0x55f6b4b8])
  | 4 => BitVec.ofNat 152 (big [0x42f2a3f4ae013cf, 0xa9eac3bda98eab6, 0xfeb3713b])
  | 5 => BitVec.ofNat 152 (big [0x5da6e2bab912736, 0x32fef77cda98b42, 0xfd6fa225])
  | _ => 0

def a27Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x94f42840, 0x80520000a020000, 0xc4008004])
  | 2 => BitVec.ofNat 152 (big [0x0])
  | 3 => BitVec.ofNat 152 (big [0xe67e8412309c193, 0x360100fd4bd4472, 0x29004971])
  | 4 => BitVec.ofNat 152 (big [0xe2632064000128b, 0x668109621102a90, 0x94a0201])
  | 5 => BitVec.ofNat 152 (big [0xd84c2903090534, 0x80846150c50408, 0x328004d2])
  | _ => 0

def a27Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a27Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (149457+i*5) 5
  | _ => 0

def a27Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a27Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 149463 1 149465 1 149462 1 i
  | _ => []

def a27 : Atlas := ⟨5,rawDecor 62 a27Pos a27Neg,repeatWord 18446740762239237360,a27Count,a27Rec,(fun _ _ => 0),a27Loc⟩
def a27Domains : Catalog := [(repeatWord 1085102592571150095, 5)]
def a28Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x4175bb5bea77259, 0x1e5dde57c34beff, 0xdf1ee78e])
  | 2 => BitVec.ofNat 152 (big [0x18e03ac9e6064ef, 0x571fd5f1aa6c9be, 0x4f030ccc])
  | 3 => BitVec.ofNat 152 (big [0xbefac7a4158adb6, 0xe9a6e7fe7cfd365, 0xedf3dcf3])
  | 4 => BitVec.ofNat 152 (big [0x758c5f9d2c35d46, 0x4ffe490b68aa639, 0x8eef6643])
  | 5 => BitVec.ofNat 152 (big [0x7909faf2025caa4, 0x72c116e97576bd4, 0x391b1fe7])
  | _ => 0

def a28Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xc02001010060011, 0x20404000000c0, 0x20])
  | 2 => BitVec.ofNat 152 (big [0xc4b12ec8f064ee, 0x98d52b196a7b93e, 0x7f6fdd80])
  | 3 => BitVec.ofNat 152 (big [0x40102082, 0x100000080071022, 0x2024000])
  | 4 => BitVec.ofNat 152 (big [0x178c4e48ac15d44, 0x29cd3894710a311, 0x90401cd8])
  | 5 => BitVec.ofNat 152 (big [0x300dbef8161ca24, 0xc31c1f80d306304, 0xd8c83092])
  | _ => 0

def a28Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a28Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (149466+i*5) 5
  | _ => 0

def a28Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a28Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 149472 1 149474 1 149471 1 i
  | _ => []

def a28 : Atlas := ⟨5,rawDecor 61 a28Pos a28Neg,repeatWord 18422818335611334560,a28Count,a28Rec,(fun _ _ => 0),a28Loc⟩
def a28Domains : Catalog := [(repeatWord 281470681808895, 5)]
def a29Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbde3bb39cd5e10a, 0x7473fa3dd0e9394, 0x775f56b7])
  | 1 => BitVec.ofNat 152 (big [0x79bd5874e3216e7, 0xfeac4deb7b76e7f, 0xfb3a44e])
  | 2 => BitVec.ofNat 152 (big [0xd60a87c77cb5979, 0xdb36ff1fa74a9a8, 0xf00feb89])
  | 3 => BitVec.ofNat 152 (big [0x5a37448a9af8e9e, 0xa98b5ee88c9ecf7, 0x9de49df3])
  | 4 => BitVec.ofNat 152 (big [0xa36cb6dc0bcabc0, 0x854dc42644ffaad, 0xe6db9ebd])
  | 5 => BitVec.ofNat 152 (big [0xdad8a92a935e8f5, 0x747d0580d5a53ca, 0x1c48b73b])
  | _ => 0

def a29Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x1de31121c85a102, 0x3003d81c68b1084, 0x87130460])
  | 1 => BitVec.ofNat 152 (big [0x211948344101281, 0xe000017a2840250, 0x82a008])
  | 2 => BitVec.ofNat 152 (big [0xc200864234a4068, 0x2202001860a128, 0x700c4880])
  | 3 => BitVec.ofNat 152 (big [0x1426008a8af8c1e, 0x8c35e848614ca3, 0x855045d3])
  | 4 => BitVec.ofNat 152 (big [0x26cb6dc0b08bc0, 0x85ce446640da8ce, 0xa4d9ba0d])
  | 5 => BitVec.ofNat 152 (big [0xda98a90893568f5, 0x567c34021124642, 0x3980be33])
  | _ => 0

def a29Count (k : Nat) : Nat :=
  match k with
  | 5 => 5
  | 6 => 94
  | 7 => 244
  | 8 => 146
  | 9 => 28
  | 10 => 1
  | _ => 0

def a29Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (149475+i*61) 61
  | 6 => field storageWord (149826+i*50) 50
  | 7 => field storageWord (159907+i*39) 39
  | 8 => field storageWord (208541+i*28) 28
  | 9 => field storageWord (244184+i*17) 17
  | 10 => field storageWord (249016+i*6) 6
  | _ => 0

def a29Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 5 3 (field storageWord (149780+(tag % 3)*3) 3) tag
  | 6 => hashRow 94 47 (field storageWord (154526+(tag % 47)*8) 8) tag
  | 7 => hashRow 244 244 (field storageWord (169423+(tag % 244)*9) 9) tag
  | 8 => hashRow 146 292 (field storageWord (212629+(tag % 292)*9) 9) tag
  | 9 => hashRow 28 14 (field storageWord (244660+(tag % 14)*6) 6) tag
  | 10 => 0
  | _ => 0

def a29Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 149819 1 149825 1 149789 30 i
  | 6 => hintsAt storageWord 158542 7 159207 7 154902 56 i
  | 7 => hintsAt storageWord 192949 11 195644 9 171619 45 i
  | 8 => hintsAt storageWord 229607 11 231224 9 215257 35 i
  | 9 => hintsAt storageWord 246571 9 246832 7 244744 21 i
  | 10 => hintsAt storageWord 249043 3 249049 3 249022 3 i
  | _ => []

def a29 : Atlas := ⟨10,rawDecor 63 a29Pos a29Neg,repeatWord 18368772107789724896,a29Count,a29Rec,(fun _ _ => 0),a29Loc⟩
def a29Domains : Catalog := [(repeatWord 6510615555426900570, 9), (repeatWord 6172840429334713770, 9), (repeatWord 3732415143318664140, 9), (repeatWord 17298308644996116495, 9), (repeatWord 71777214294589695, 8), (repeatWord 281470681808895, 8), (repeatWord 4294967295, 8), (repeatWord 12297735558912431445, 8), (repeatWord 12297829381041378645, 8), (repeatWord 1085350949055099120, 8), (repeatWord 1085102596360827120, 8), (repeatWord 18374687579166474495, 8), (repeatWord 18374966855153418495, 8), (repeatWord 3689348814741910323, 7), (repeatWord 1085102592571150095, 7), (repeatWord 18374966859414961920, 7), (repeatWord 18446462603027742720, 7), (repeatWord 18446744069414584320, 7), (repeatWord 11068046444225730969, 7), (repeatWord 6148914691236517205, 6), (repeatWord 12297829382473034410, 6), (repeatWord 3674993371882992384, 6), (repeatWord 4340410370284600380, 6), (repeatWord 723401728380766730, 5), (repeatWord 47851476196393130, 5), (repeatWord 93823560602965, 5), (repeatWord 1431655765, 5), (repeatWord 4222189076152335, 5), (repeatWord 1095216660735, 5), (repeatWord 71776119077928960, 5), (repeatWord 16711935, 5), (repeatWord 71777214277877760, 5), (repeatWord 18446462598732840960, 5), (repeatWord 6148820867675914240, 4), (repeatWord 6148914689804861440, 4), (repeatWord 3689292520605548544, 4), (repeatWord 3689348813882916864, 4), (repeatWord 1085086035472220160, 4), (repeatWord 1085102592318504960, 4), (repeatWord 65535, 4), (repeatWord 2814792717434890, 4), (repeatWord 93823560581120, 4), (repeatWord 1431633920, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0S3P0 : segment (checkRow a0 a0Domains a0Hints 3) 0 1 = true := by decide +kernel
theorem a0S3 (j : Nat) (hj : j < 1) : (checkRow a0 a0Domains a0Hints 3) j = true := by
  exact segmentRange a0S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0Complete : Complete a0 a0Domains a0Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a0S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S3P0 : segment (checkRow a1 a1Domains a1Hints 3) 0 8 = true := by decide +kernel
theorem a1S3 (j : Nat) (hj : j < 8) : (checkRow a1 a1Domains a1Hints 3) j = true := by
  exact segmentRange a1S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S4P0 : segment (checkRow a1 a1Domains a1Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S4P1 : segment (checkRow a1 a1Domains a1Hints 4) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S4P2 : segment (checkRow a1 a1Domains a1Hints 4) 20 8 = true := by decide +kernel
theorem a1S4 (j : Nat) (hj : j < 28) : (checkRow a1 a1Domains a1Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a1S4P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 20
    ·
      exact segmentRange a1S4P1 j (by omega) (by omega)
    ·
      exact segmentRange a1S4P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S5P0 : segment (checkRow a1 a1Domains a1Hints 5) 0 6 = true := by decide +kernel
theorem a1S5 (j : Nat) (hj : j < 6) : (checkRow a1 a1Domains a1Hints 5) j = true := by
  exact segmentRange a1S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S6P0 : segment (checkRow a1 a1Domains a1Hints 6) 0 1 = true := by decide +kernel
theorem a1S6 (j : Nat) (hj : j < 1) : (checkRow a1 a1Domains a1Hints 6) j = true := by
  exact segmentRange a1S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Complete : Complete a1 a1Domains a1Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a1S3 j hj
  · exact a1S4 j hj
  · exact a1S5 j hj
  · exact a1S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2S2P0 : segment (checkRow a2 a2Domains a2Hints 2) 0 1 = true := by decide +kernel
theorem a2S2 (j : Nat) (hj : j < 1) : (checkRow a2 a2Domains a2Hints 2) j = true := by
  exact segmentRange a2S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Complete : Complete a2 a2Domains a2Hints := by
  intro k hk j hj
  change k ≤ 2 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a2S2 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S2P0 : segment (checkRow a3 a3Domains a3Hints 2) 0 2 = true := by decide +kernel
theorem a3S2 (j : Nat) (hj : j < 2) : (checkRow a3 a3Domains a3Hints 2) j = true := by
  exact segmentRange a3S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S3P0 : segment (checkRow a3 a3Domains a3Hints 3) 0 6 = true := by decide +kernel
theorem a3S3 (j : Nat) (hj : j < 6) : (checkRow a3 a3Domains a3Hints 3) j = true := by
  exact segmentRange a3S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S4P0 : segment (checkRow a3 a3Domains a3Hints 4) 0 6 = true := by decide +kernel
theorem a3S4 (j : Nat) (hj : j < 6) : (checkRow a3 a3Domains a3Hints 4) j = true := by
  exact segmentRange a3S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S5P0 : segment (checkRow a3 a3Domains a3Hints 5) 0 1 = true := by decide +kernel
theorem a3S5 (j : Nat) (hj : j < 1) : (checkRow a3 a3Domains a3Hints 5) j = true := by
  exact segmentRange a3S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Complete : Complete a3 a3Domains a3Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a3S2 j hj
  · exact a3S3 j hj
  · exact a3S4 j hj
  · exact a3S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S3P0 : segment (checkRow a4 a4Domains a4Hints 3) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S3P1 : segment (checkRow a4 a4Domains a4Hints 3) 10 5 = true := by decide +kernel
theorem a4S3 (j : Nat) (hj : j < 15) : (checkRow a4 a4Domains a4Hints 3) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a4S3P0 j (by omega) (by omega)
  ·
    exact segmentRange a4S3P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S4P0 : segment (checkRow a4 a4Domains a4Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S4P1 : segment (checkRow a4 a4Domains a4Hints 4) 10 2 = true := by decide +kernel
theorem a4S4 (j : Nat) (hj : j < 12) : (checkRow a4 a4Domains a4Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a4S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a4S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S5P0 : segment (checkRow a4 a4Domains a4Hints 5) 0 1 = true := by decide +kernel
theorem a4S5 (j : Nat) (hj : j < 1) : (checkRow a4 a4Domains a4Hints 5) j = true := by
  exact segmentRange a4S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Complete : Complete a4 a4Domains a4Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a4S3 j hj
  · exact a4S4 j hj
  · exact a4S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S4P0 : segment (checkRow a5 a5Domains a5Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S4P1 : segment (checkRow a5 a5Domains a5Hints 4) 10 2 = true := by decide +kernel
theorem a5S4 (j : Nat) (hj : j < 12) : (checkRow a5 a5Domains a5Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a5S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a5S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S5P0 : segment (checkRow a5 a5Domains a5Hints 5) 0 1 = true := by decide +kernel
theorem a5S5 (j : Nat) (hj : j < 1) : (checkRow a5 a5Domains a5Hints 5) j = true := by
  exact segmentRange a5S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Complete : Complete a5 a5Domains a5Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a5S4 j hj
  · exact a5S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S4P0 : segment (checkRow a6 a6Domains a6Hints 4) 0 1 = true := by decide +kernel
theorem a6S4 (j : Nat) (hj : j < 1) : (checkRow a6 a6Domains a6Hints 4) j = true := by
  exact segmentRange a6S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Complete : Complete a6 a6Domains a6Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a6S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7S4P0 : segment (checkRow a7 a7Domains a7Hints 4) 0 1 = true := by decide +kernel
theorem a7S4 (j : Nat) (hj : j < 1) : (checkRow a7 a7Domains a7Hints 4) j = true := by
  exact segmentRange a7S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Complete : Complete a7 a7Domains a7Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a7S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S4P0 : segment (checkRow a8 a8Domains a8Hints 4) 0 1 = true := by decide +kernel
theorem a8S4 (j : Nat) (hj : j < 1) : (checkRow a8 a8Domains a8Hints 4) j = true := by
  exact segmentRange a8S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Complete : Complete a8 a8Domains a8Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a8S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P0 : segment (checkRow a9 a9Domains a9Hints 3) 0 1 = true := by decide +kernel
theorem a9S3 (j : Nat) (hj : j < 1) : (checkRow a9 a9Domains a9Hints 3) j = true := by
  exact segmentRange a9S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Complete : Complete a9 a9Domains a9Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a9S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S5P0 : segment (checkRow a10 a10Domains a10Hints 5) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S5P1 : segment (checkRow a10 a10Domains a10Hints 5) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S5P2 : segment (checkRow a10 a10Domains a10Hints 5) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S5P3 : segment (checkRow a10 a10Domains a10Hints 5) 30 6 = true := by decide +kernel
theorem a10S5 (j : Nat) (hj : j < 36) : (checkRow a10 a10Domains a10Hints 5) j = true := by
  by_cases bound : j < 20
  ·
    by_cases bound : j < 10
    ·
      exact segmentRange a10S5P0 j (by omega) (by omega)
    ·
      exact segmentRange a10S5P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 30
    ·
      exact segmentRange a10S5P2 j (by omega) (by omega)
    ·
      exact segmentRange a10S5P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S6P0 : segment (checkRow a10 a10Domains a10Hints 6) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S6P1 : segment (checkRow a10 a10Domains a10Hints 6) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S6P2 : segment (checkRow a10 a10Domains a10Hints 6) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S6P3 : segment (checkRow a10 a10Domains a10Hints 6) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S6P4 : segment (checkRow a10 a10Domains a10Hints 6) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S6P5 : segment (checkRow a10 a10Domains a10Hints 6) 50 8 = true := by decide +kernel
theorem a10S6 (j : Nat) (hj : j < 58) : (checkRow a10 a10Domains a10Hints 6) j = true := by
  by_cases bound : j < 30
  ·
    by_cases bound : j < 10
    ·
      exact segmentRange a10S6P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 20
      ·
        exact segmentRange a10S6P1 j (by omega) (by omega)
      ·
        exact segmentRange a10S6P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 40
    ·
      exact segmentRange a10S6P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 50
      ·
        exact segmentRange a10S6P4 j (by omega) (by omega)
      ·
        exact segmentRange a10S6P5 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S7P0 : segment (checkRow a10 a10Domains a10Hints 7) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S7P1 : segment (checkRow a10 a10Domains a10Hints 7) 10 2 = true := by decide +kernel
theorem a10S7 (j : Nat) (hj : j < 12) : (checkRow a10 a10Domains a10Hints 7) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a10S7P0 j (by omega) (by omega)
  ·
    exact segmentRange a10S7P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S8P0 : segment (checkRow a10 a10Domains a10Hints 8) 0 1 = true := by decide +kernel
theorem a10S8 (j : Nat) (hj : j < 1) : (checkRow a10 a10Domains a10Hints 8) j = true := by
  exact segmentRange a10S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Complete : Complete a10 a10Domains a10Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a10S5 j hj
  · exact a10S6 j hj
  · exact a10S7 j hj
  · exact a10S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S4P0 : segment (checkRow a11 a11Domains a11Hints 4) 0 1 = true := by decide +kernel
theorem a11S4 (j : Nat) (hj : j < 1) : (checkRow a11 a11Domains a11Hints 4) j = true := by
  exact segmentRange a11S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Complete : Complete a11 a11Domains a11Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a11S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S1P0 : segment (checkRow a12 a12Domains a12Hints 1) 0 2 = true := by decide +kernel
theorem a12S1 (j : Nat) (hj : j < 2) : (checkRow a12 a12Domains a12Hints 1) j = true := by
  exact segmentRange a12S1P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S2P0 : segment (checkRow a12 a12Domains a12Hints 2) 0 4 = true := by decide +kernel
theorem a12S2 (j : Nat) (hj : j < 4) : (checkRow a12 a12Domains a12Hints 2) j = true := by
  exact segmentRange a12S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S3P0 : segment (checkRow a12 a12Domains a12Hints 3) 0 1 = true := by decide +kernel
theorem a12S3 (j : Nat) (hj : j < 1) : (checkRow a12 a12Domains a12Hints 3) j = true := by
  exact segmentRange a12S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Complete : Complete a12 a12Domains a12Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a12S1 j hj
  · exact a12S2 j hj
  · exact a12S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S4P0 : segment (checkRow a13 a13Domains a13Hints 4) 0 1 = true := by decide +kernel
theorem a13S4 (j : Nat) (hj : j < 1) : (checkRow a13 a13Domains a13Hints 4) j = true := by
  exact segmentRange a13S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Complete : Complete a13 a13Domains a13Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a13S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P0 : segment (checkRow a14 a14Domains a14Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P1 : segment (checkRow a14 a14Domains a14Hints 4) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P2 : segment (checkRow a14 a14Domains a14Hints 4) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P3 : segment (checkRow a14 a14Domains a14Hints 4) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P4 : segment (checkRow a14 a14Domains a14Hints 4) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P5 : segment (checkRow a14 a14Domains a14Hints 4) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P6 : segment (checkRow a14 a14Domains a14Hints 4) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P7 : segment (checkRow a14 a14Domains a14Hints 4) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P8 : segment (checkRow a14 a14Domains a14Hints 4) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P9 : segment (checkRow a14 a14Domains a14Hints 4) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P10 : segment (checkRow a14 a14Domains a14Hints 4) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P11 : segment (checkRow a14 a14Domains a14Hints 4) 110 8 = true := by decide +kernel
theorem a14S4 (j : Nat) (hj : j < 118) : (checkRow a14 a14Domains a14Hints 4) j = true := by
  by_cases bound : j < 60
  ·
    by_cases bound : j < 30
    ·
      by_cases bound : j < 10
      ·
        exact segmentRange a14S4P0 j (by omega) (by omega)
      ·
        by_cases bound : j < 20
        ·
          exact segmentRange a14S4P1 j (by omega) (by omega)
        ·
          exact segmentRange a14S4P2 j (by omega) (by omega)
    ·
      by_cases bound : j < 40
      ·
        exact segmentRange a14S4P3 j (by omega) (by omega)
      ·
        by_cases bound : j < 50
        ·
          exact segmentRange a14S4P4 j (by omega) (by omega)
        ·
          exact segmentRange a14S4P5 j (by omega) (by omega)
  ·
    by_cases bound : j < 90
    ·
      by_cases bound : j < 70
      ·
        exact segmentRange a14S4P6 j (by omega) (by omega)
      ·
        by_cases bound : j < 80
        ·
          exact segmentRange a14S4P7 j (by omega) (by omega)
        ·
          exact segmentRange a14S4P8 j (by omega) (by omega)
    ·
      by_cases bound : j < 100
      ·
        exact segmentRange a14S4P9 j (by omega) (by omega)
      ·
        by_cases bound : j < 110
        ·
          exact segmentRange a14S4P10 j (by omega) (by omega)
        ·
          exact segmentRange a14S4P11 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P0 : segment (checkRow a14 a14Domains a14Hints 5) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P1 : segment (checkRow a14 a14Domains a14Hints 5) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P2 : segment (checkRow a14 a14Domains a14Hints 5) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P3 : segment (checkRow a14 a14Domains a14Hints 5) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P4 : segment (checkRow a14 a14Domains a14Hints 5) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P5 : segment (checkRow a14 a14Domains a14Hints 5) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P6 : segment (checkRow a14 a14Domains a14Hints 5) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P7 : segment (checkRow a14 a14Domains a14Hints 5) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P8 : segment (checkRow a14 a14Domains a14Hints 5) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P9 : segment (checkRow a14 a14Domains a14Hints 5) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P10 : segment (checkRow a14 a14Domains a14Hints 5) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P11 : segment (checkRow a14 a14Domains a14Hints 5) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P12 : segment (checkRow a14 a14Domains a14Hints 5) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P13 : segment (checkRow a14 a14Domains a14Hints 5) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P14 : segment (checkRow a14 a14Domains a14Hints 5) 140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P15 : segment (checkRow a14 a14Domains a14Hints 5) 150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P16 : segment (checkRow a14 a14Domains a14Hints 5) 160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P17 : segment (checkRow a14 a14Domains a14Hints 5) 170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P18 : segment (checkRow a14 a14Domains a14Hints 5) 180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P19 : segment (checkRow a14 a14Domains a14Hints 5) 190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P20 : segment (checkRow a14 a14Domains a14Hints 5) 200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P21 : segment (checkRow a14 a14Domains a14Hints 5) 210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P22 : segment (checkRow a14 a14Domains a14Hints 5) 220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P23 : segment (checkRow a14 a14Domains a14Hints 5) 230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P24 : segment (checkRow a14 a14Domains a14Hints 5) 240 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P25 : segment (checkRow a14 a14Domains a14Hints 5) 250 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P26 : segment (checkRow a14 a14Domains a14Hints 5) 260 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P27 : segment (checkRow a14 a14Domains a14Hints 5) 270 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P28 : segment (checkRow a14 a14Domains a14Hints 5) 280 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P29 : segment (checkRow a14 a14Domains a14Hints 5) 290 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P30 : segment (checkRow a14 a14Domains a14Hints 5) 300 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P31 : segment (checkRow a14 a14Domains a14Hints 5) 310 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P32 : segment (checkRow a14 a14Domains a14Hints 5) 320 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P33 : segment (checkRow a14 a14Domains a14Hints 5) 330 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P34 : segment (checkRow a14 a14Domains a14Hints 5) 340 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P35 : segment (checkRow a14 a14Domains a14Hints 5) 350 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P36 : segment (checkRow a14 a14Domains a14Hints 5) 360 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P37 : segment (checkRow a14 a14Domains a14Hints 5) 370 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P38 : segment (checkRow a14 a14Domains a14Hints 5) 380 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P39 : segment (checkRow a14 a14Domains a14Hints 5) 390 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P40 : segment (checkRow a14 a14Domains a14Hints 5) 400 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P41 : segment (checkRow a14 a14Domains a14Hints 5) 410 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P42 : segment (checkRow a14 a14Domains a14Hints 5) 420 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P43 : segment (checkRow a14 a14Domains a14Hints 5) 430 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P44 : segment (checkRow a14 a14Domains a14Hints 5) 440 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P45 : segment (checkRow a14 a14Domains a14Hints 5) 450 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P46 : segment (checkRow a14 a14Domains a14Hints 5) 460 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P47 : segment (checkRow a14 a14Domains a14Hints 5) 470 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P48 : segment (checkRow a14 a14Domains a14Hints 5) 480 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P49 : segment (checkRow a14 a14Domains a14Hints 5) 490 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P50 : segment (checkRow a14 a14Domains a14Hints 5) 500 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P51 : segment (checkRow a14 a14Domains a14Hints 5) 510 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P52 : segment (checkRow a14 a14Domains a14Hints 5) 520 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P53 : segment (checkRow a14 a14Domains a14Hints 5) 530 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P54 : segment (checkRow a14 a14Domains a14Hints 5) 540 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P55 : segment (checkRow a14 a14Domains a14Hints 5) 550 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P56 : segment (checkRow a14 a14Domains a14Hints 5) 560 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P57 : segment (checkRow a14 a14Domains a14Hints 5) 570 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P58 : segment (checkRow a14 a14Domains a14Hints 5) 580 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P59 : segment (checkRow a14 a14Domains a14Hints 5) 590 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P60 : segment (checkRow a14 a14Domains a14Hints 5) 600 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P61 : segment (checkRow a14 a14Domains a14Hints 5) 610 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P62 : segment (checkRow a14 a14Domains a14Hints 5) 620 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P63 : segment (checkRow a14 a14Domains a14Hints 5) 630 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P64 : segment (checkRow a14 a14Domains a14Hints 5) 640 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P65 : segment (checkRow a14 a14Domains a14Hints 5) 650 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P66 : segment (checkRow a14 a14Domains a14Hints 5) 660 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P67 : segment (checkRow a14 a14Domains a14Hints 5) 670 2 = true := by decide +kernel
theorem a14S5 (j : Nat) (hj : j < 672) : (checkRow a14 a14Domains a14Hints 5) j = true := by
  by_cases bound : j < 340
  ·
    by_cases bound : j < 170
    ·
      by_cases bound : j < 80
      ·
        by_cases bound : j < 40
        ·
          by_cases bound : j < 20
          ·
            by_cases bound : j < 10
            ·
              exact segmentRange a14S5P0 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P1 j (by omega) (by omega)
          ·
            by_cases bound : j < 30
            ·
              exact segmentRange a14S5P2 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P3 j (by omega) (by omega)
        ·
          by_cases bound : j < 60
          ·
            by_cases bound : j < 50
            ·
              exact segmentRange a14S5P4 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P5 j (by omega) (by omega)
          ·
            by_cases bound : j < 70
            ·
              exact segmentRange a14S5P6 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 120
        ·
          by_cases bound : j < 100
          ·
            by_cases bound : j < 90
            ·
              exact segmentRange a14S5P8 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P9 j (by omega) (by omega)
          ·
            by_cases bound : j < 110
            ·
              exact segmentRange a14S5P10 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P11 j (by omega) (by omega)
        ·
          by_cases bound : j < 140
          ·
            by_cases bound : j < 130
            ·
              exact segmentRange a14S5P12 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P13 j (by omega) (by omega)
          ·
            by_cases bound : j < 150
            ·
              exact segmentRange a14S5P14 j (by omega) (by omega)
            ·
              by_cases bound : j < 160
              ·
                exact segmentRange a14S5P15 j (by omega) (by omega)
              ·
                exact segmentRange a14S5P16 j (by omega) (by omega)
    ·
      by_cases bound : j < 250
      ·
        by_cases bound : j < 210
        ·
          by_cases bound : j < 190
          ·
            by_cases bound : j < 180
            ·
              exact segmentRange a14S5P17 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P18 j (by omega) (by omega)
          ·
            by_cases bound : j < 200
            ·
              exact segmentRange a14S5P19 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P20 j (by omega) (by omega)
        ·
          by_cases bound : j < 230
          ·
            by_cases bound : j < 220
            ·
              exact segmentRange a14S5P21 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P22 j (by omega) (by omega)
          ·
            by_cases bound : j < 240
            ·
              exact segmentRange a14S5P23 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P24 j (by omega) (by omega)
      ·
        by_cases bound : j < 290
        ·
          by_cases bound : j < 270
          ·
            by_cases bound : j < 260
            ·
              exact segmentRange a14S5P25 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P26 j (by omega) (by omega)
          ·
            by_cases bound : j < 280
            ·
              exact segmentRange a14S5P27 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P28 j (by omega) (by omega)
        ·
          by_cases bound : j < 310
          ·
            by_cases bound : j < 300
            ·
              exact segmentRange a14S5P29 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P30 j (by omega) (by omega)
          ·
            by_cases bound : j < 320
            ·
              exact segmentRange a14S5P31 j (by omega) (by omega)
            ·
              by_cases bound : j < 330
              ·
                exact segmentRange a14S5P32 j (by omega) (by omega)
              ·
                exact segmentRange a14S5P33 j (by omega) (by omega)
  ·
    by_cases bound : j < 510
    ·
      by_cases bound : j < 420
      ·
        by_cases bound : j < 380
        ·
          by_cases bound : j < 360
          ·
            by_cases bound : j < 350
            ·
              exact segmentRange a14S5P34 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P35 j (by omega) (by omega)
          ·
            by_cases bound : j < 370
            ·
              exact segmentRange a14S5P36 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P37 j (by omega) (by omega)
        ·
          by_cases bound : j < 400
          ·
            by_cases bound : j < 390
            ·
              exact segmentRange a14S5P38 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P39 j (by omega) (by omega)
          ·
            by_cases bound : j < 410
            ·
              exact segmentRange a14S5P40 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P41 j (by omega) (by omega)
      ·
        by_cases bound : j < 460
        ·
          by_cases bound : j < 440
          ·
            by_cases bound : j < 430
            ·
              exact segmentRange a14S5P42 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P43 j (by omega) (by omega)
          ·
            by_cases bound : j < 450
            ·
              exact segmentRange a14S5P44 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P45 j (by omega) (by omega)
        ·
          by_cases bound : j < 480
          ·
            by_cases bound : j < 470
            ·
              exact segmentRange a14S5P46 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P47 j (by omega) (by omega)
          ·
            by_cases bound : j < 490
            ·
              exact segmentRange a14S5P48 j (by omega) (by omega)
            ·
              by_cases bound : j < 500
              ·
                exact segmentRange a14S5P49 j (by omega) (by omega)
              ·
                exact segmentRange a14S5P50 j (by omega) (by omega)
    ·
      by_cases bound : j < 590
      ·
        by_cases bound : j < 550
        ·
          by_cases bound : j < 530
          ·
            by_cases bound : j < 520
            ·
              exact segmentRange a14S5P51 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P52 j (by omega) (by omega)
          ·
            by_cases bound : j < 540
            ·
              exact segmentRange a14S5P53 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P54 j (by omega) (by omega)
        ·
          by_cases bound : j < 570
          ·
            by_cases bound : j < 560
            ·
              exact segmentRange a14S5P55 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P56 j (by omega) (by omega)
          ·
            by_cases bound : j < 580
            ·
              exact segmentRange a14S5P57 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P58 j (by omega) (by omega)
      ·
        by_cases bound : j < 630
        ·
          by_cases bound : j < 610
          ·
            by_cases bound : j < 600
            ·
              exact segmentRange a14S5P59 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P60 j (by omega) (by omega)
          ·
            by_cases bound : j < 620
            ·
              exact segmentRange a14S5P61 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P62 j (by omega) (by omega)
        ·
          by_cases bound : j < 650
          ·
            by_cases bound : j < 640
            ·
              exact segmentRange a14S5P63 j (by omega) (by omega)
            ·
              exact segmentRange a14S5P64 j (by omega) (by omega)
          ·
            by_cases bound : j < 660
            ·
              exact segmentRange a14S5P65 j (by omega) (by omega)
            ·
              by_cases bound : j < 670
              ·
                exact segmentRange a14S5P66 j (by omega) (by omega)
              ·
                exact segmentRange a14S5P67 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P0 : segment (checkRow a14 a14Domains a14Hints 6) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P1 : segment (checkRow a14 a14Domains a14Hints 6) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P2 : segment (checkRow a14 a14Domains a14Hints 6) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P3 : segment (checkRow a14 a14Domains a14Hints 6) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P4 : segment (checkRow a14 a14Domains a14Hints 6) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P5 : segment (checkRow a14 a14Domains a14Hints 6) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P6 : segment (checkRow a14 a14Domains a14Hints 6) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P7 : segment (checkRow a14 a14Domains a14Hints 6) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P8 : segment (checkRow a14 a14Domains a14Hints 6) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P9 : segment (checkRow a14 a14Domains a14Hints 6) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P10 : segment (checkRow a14 a14Domains a14Hints 6) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P11 : segment (checkRow a14 a14Domains a14Hints 6) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P12 : segment (checkRow a14 a14Domains a14Hints 6) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P13 : segment (checkRow a14 a14Domains a14Hints 6) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P14 : segment (checkRow a14 a14Domains a14Hints 6) 140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P15 : segment (checkRow a14 a14Domains a14Hints 6) 150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P16 : segment (checkRow a14 a14Domains a14Hints 6) 160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P17 : segment (checkRow a14 a14Domains a14Hints 6) 170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P18 : segment (checkRow a14 a14Domains a14Hints 6) 180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P19 : segment (checkRow a14 a14Domains a14Hints 6) 190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P20 : segment (checkRow a14 a14Domains a14Hints 6) 200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P21 : segment (checkRow a14 a14Domains a14Hints 6) 210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P22 : segment (checkRow a14 a14Domains a14Hints 6) 220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P23 : segment (checkRow a14 a14Domains a14Hints 6) 230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P24 : segment (checkRow a14 a14Domains a14Hints 6) 240 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P25 : segment (checkRow a14 a14Domains a14Hints 6) 250 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P26 : segment (checkRow a14 a14Domains a14Hints 6) 260 9 = true := by decide +kernel
theorem a14S6 (j : Nat) (hj : j < 269) : (checkRow a14 a14Domains a14Hints 6) j = true := by
  by_cases bound : j < 130
  ·
    by_cases bound : j < 60
    ·
      by_cases bound : j < 30
      ·
        by_cases bound : j < 10
        ·
          exact segmentRange a14S6P0 j (by omega) (by omega)
        ·
          by_cases bound : j < 20
          ·
            exact segmentRange a14S6P1 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 40
        ·
          exact segmentRange a14S6P3 j (by omega) (by omega)
        ·
          by_cases bound : j < 50
          ·
            exact segmentRange a14S6P4 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P5 j (by omega) (by omega)
    ·
      by_cases bound : j < 90
      ·
        by_cases bound : j < 70
        ·
          exact segmentRange a14S6P6 j (by omega) (by omega)
        ·
          by_cases bound : j < 80
          ·
            exact segmentRange a14S6P7 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P8 j (by omega) (by omega)
      ·
        by_cases bound : j < 110
        ·
          by_cases bound : j < 100
          ·
            exact segmentRange a14S6P9 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P10 j (by omega) (by omega)
        ·
          by_cases bound : j < 120
          ·
            exact segmentRange a14S6P11 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P12 j (by omega) (by omega)
  ·
    by_cases bound : j < 200
    ·
      by_cases bound : j < 160
      ·
        by_cases bound : j < 140
        ·
          exact segmentRange a14S6P13 j (by omega) (by omega)
        ·
          by_cases bound : j < 150
          ·
            exact segmentRange a14S6P14 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P15 j (by omega) (by omega)
      ·
        by_cases bound : j < 180
        ·
          by_cases bound : j < 170
          ·
            exact segmentRange a14S6P16 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P17 j (by omega) (by omega)
        ·
          by_cases bound : j < 190
          ·
            exact segmentRange a14S6P18 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P19 j (by omega) (by omega)
    ·
      by_cases bound : j < 230
      ·
        by_cases bound : j < 210
        ·
          exact segmentRange a14S6P20 j (by omega) (by omega)
        ·
          by_cases bound : j < 220
          ·
            exact segmentRange a14S6P21 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P22 j (by omega) (by omega)
      ·
        by_cases bound : j < 250
        ·
          by_cases bound : j < 240
          ·
            exact segmentRange a14S6P23 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P24 j (by omega) (by omega)
        ·
          by_cases bound : j < 260
          ·
            exact segmentRange a14S6P25 j (by omega) (by omega)
          ·
            exact segmentRange a14S6P26 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S7P0 : segment (checkRow a14 a14Domains a14Hints 7) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S7P1 : segment (checkRow a14 a14Domains a14Hints 7) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S7P2 : segment (checkRow a14 a14Domains a14Hints 7) 20 4 = true := by decide +kernel
theorem a14S7 (j : Nat) (hj : j < 24) : (checkRow a14 a14Domains a14Hints 7) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a14S7P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 20
    ·
      exact segmentRange a14S7P1 j (by omega) (by omega)
    ·
      exact segmentRange a14S7P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S8P0 : segment (checkRow a14 a14Domains a14Hints 8) 0 1 = true := by decide +kernel
theorem a14S8 (j : Nat) (hj : j < 1) : (checkRow a14 a14Domains a14Hints 8) j = true := by
  exact segmentRange a14S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Complete : Complete a14 a14Domains a14Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a14S4 j hj
  · exact a14S5 j hj
  · exact a14S6 j hj
  · exact a14S7 j hj
  · exact a14S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S3P0 : segment (checkRow a15 a15Domains a15Hints 3) 0 3 = true := by decide +kernel
theorem a15S3 (j : Nat) (hj : j < 3) : (checkRow a15 a15Domains a15Hints 3) j = true := by
  exact segmentRange a15S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P0 : segment (checkRow a15 a15Domains a15Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P1 : segment (checkRow a15 a15Domains a15Hints 4) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P2 : segment (checkRow a15 a15Domains a15Hints 4) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P3 : segment (checkRow a15 a15Domains a15Hints 4) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P4 : segment (checkRow a15 a15Domains a15Hints 4) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P5 : segment (checkRow a15 a15Domains a15Hints 4) 50 10 = true := by decide +kernel
theorem a15S4 (j : Nat) (hj : j < 60) : (checkRow a15 a15Domains a15Hints 4) j = true := by
  by_cases bound : j < 30
  ·
    by_cases bound : j < 10
    ·
      exact segmentRange a15S4P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 20
      ·
        exact segmentRange a15S4P1 j (by omega) (by omega)
      ·
        exact segmentRange a15S4P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 40
    ·
      exact segmentRange a15S4P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 50
      ·
        exact segmentRange a15S4P4 j (by omega) (by omega)
      ·
        exact segmentRange a15S4P5 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P0 : segment (checkRow a15 a15Domains a15Hints 5) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P1 : segment (checkRow a15 a15Domains a15Hints 5) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P2 : segment (checkRow a15 a15Domains a15Hints 5) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P3 : segment (checkRow a15 a15Domains a15Hints 5) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P4 : segment (checkRow a15 a15Domains a15Hints 5) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P5 : segment (checkRow a15 a15Domains a15Hints 5) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P6 : segment (checkRow a15 a15Domains a15Hints 5) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P7 : segment (checkRow a15 a15Domains a15Hints 5) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P8 : segment (checkRow a15 a15Domains a15Hints 5) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P9 : segment (checkRow a15 a15Domains a15Hints 5) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P10 : segment (checkRow a15 a15Domains a15Hints 5) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P11 : segment (checkRow a15 a15Domains a15Hints 5) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P12 : segment (checkRow a15 a15Domains a15Hints 5) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P13 : segment (checkRow a15 a15Domains a15Hints 5) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P14 : segment (checkRow a15 a15Domains a15Hints 5) 140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P15 : segment (checkRow a15 a15Domains a15Hints 5) 150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P16 : segment (checkRow a15 a15Domains a15Hints 5) 160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P17 : segment (checkRow a15 a15Domains a15Hints 5) 170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P18 : segment (checkRow a15 a15Domains a15Hints 5) 180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P19 : segment (checkRow a15 a15Domains a15Hints 5) 190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P20 : segment (checkRow a15 a15Domains a15Hints 5) 200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P21 : segment (checkRow a15 a15Domains a15Hints 5) 210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P22 : segment (checkRow a15 a15Domains a15Hints 5) 220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P23 : segment (checkRow a15 a15Domains a15Hints 5) 230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P24 : segment (checkRow a15 a15Domains a15Hints 5) 240 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P25 : segment (checkRow a15 a15Domains a15Hints 5) 250 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P26 : segment (checkRow a15 a15Domains a15Hints 5) 260 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P27 : segment (checkRow a15 a15Domains a15Hints 5) 270 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P28 : segment (checkRow a15 a15Domains a15Hints 5) 280 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P29 : segment (checkRow a15 a15Domains a15Hints 5) 290 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P30 : segment (checkRow a15 a15Domains a15Hints 5) 300 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P31 : segment (checkRow a15 a15Domains a15Hints 5) 310 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P32 : segment (checkRow a15 a15Domains a15Hints 5) 320 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P33 : segment (checkRow a15 a15Domains a15Hints 5) 330 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P34 : segment (checkRow a15 a15Domains a15Hints 5) 340 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P35 : segment (checkRow a15 a15Domains a15Hints 5) 350 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P36 : segment (checkRow a15 a15Domains a15Hints 5) 360 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P37 : segment (checkRow a15 a15Domains a15Hints 5) 370 5 = true := by decide +kernel
theorem a15S5 (j : Nat) (hj : j < 375) : (checkRow a15 a15Domains a15Hints 5) j = true := by
  by_cases bound : j < 190
  ·
    by_cases bound : j < 90
    ·
      by_cases bound : j < 40
      ·
        by_cases bound : j < 20
        ·
          by_cases bound : j < 10
          ·
            exact segmentRange a15S5P0 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P1 j (by omega) (by omega)
        ·
          by_cases bound : j < 30
          ·
            exact segmentRange a15S5P2 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P3 j (by omega) (by omega)
      ·
        by_cases bound : j < 60
        ·
          by_cases bound : j < 50
          ·
            exact segmentRange a15S5P4 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P5 j (by omega) (by omega)
        ·
          by_cases bound : j < 70
          ·
            exact segmentRange a15S5P6 j (by omega) (by omega)
          ·
            by_cases bound : j < 80
            ·
              exact segmentRange a15S5P7 j (by omega) (by omega)
            ·
              exact segmentRange a15S5P8 j (by omega) (by omega)
    ·
      by_cases bound : j < 140
      ·
        by_cases bound : j < 110
        ·
          by_cases bound : j < 100
          ·
            exact segmentRange a15S5P9 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P10 j (by omega) (by omega)
        ·
          by_cases bound : j < 120
          ·
            exact segmentRange a15S5P11 j (by omega) (by omega)
          ·
            by_cases bound : j < 130
            ·
              exact segmentRange a15S5P12 j (by omega) (by omega)
            ·
              exact segmentRange a15S5P13 j (by omega) (by omega)
      ·
        by_cases bound : j < 160
        ·
          by_cases bound : j < 150
          ·
            exact segmentRange a15S5P14 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P15 j (by omega) (by omega)
        ·
          by_cases bound : j < 170
          ·
            exact segmentRange a15S5P16 j (by omega) (by omega)
          ·
            by_cases bound : j < 180
            ·
              exact segmentRange a15S5P17 j (by omega) (by omega)
            ·
              exact segmentRange a15S5P18 j (by omega) (by omega)
  ·
    by_cases bound : j < 280
    ·
      by_cases bound : j < 230
      ·
        by_cases bound : j < 210
        ·
          by_cases bound : j < 200
          ·
            exact segmentRange a15S5P19 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P20 j (by omega) (by omega)
        ·
          by_cases bound : j < 220
          ·
            exact segmentRange a15S5P21 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P22 j (by omega) (by omega)
      ·
        by_cases bound : j < 250
        ·
          by_cases bound : j < 240
          ·
            exact segmentRange a15S5P23 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P24 j (by omega) (by omega)
        ·
          by_cases bound : j < 260
          ·
            exact segmentRange a15S5P25 j (by omega) (by omega)
          ·
            by_cases bound : j < 270
            ·
              exact segmentRange a15S5P26 j (by omega) (by omega)
            ·
              exact segmentRange a15S5P27 j (by omega) (by omega)
    ·
      by_cases bound : j < 330
      ·
        by_cases bound : j < 300
        ·
          by_cases bound : j < 290
          ·
            exact segmentRange a15S5P28 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P29 j (by omega) (by omega)
        ·
          by_cases bound : j < 310
          ·
            exact segmentRange a15S5P30 j (by omega) (by omega)
          ·
            by_cases bound : j < 320
            ·
              exact segmentRange a15S5P31 j (by omega) (by omega)
            ·
              exact segmentRange a15S5P32 j (by omega) (by omega)
      ·
        by_cases bound : j < 350
        ·
          by_cases bound : j < 340
          ·
            exact segmentRange a15S5P33 j (by omega) (by omega)
          ·
            exact segmentRange a15S5P34 j (by omega) (by omega)
        ·
          by_cases bound : j < 360
          ·
            exact segmentRange a15S5P35 j (by omega) (by omega)
          ·
            by_cases bound : j < 370
            ·
              exact segmentRange a15S5P36 j (by omega) (by omega)
            ·
              exact segmentRange a15S5P37 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P0 : segment (checkRow a15 a15Domains a15Hints 6) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P1 : segment (checkRow a15 a15Domains a15Hints 6) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P2 : segment (checkRow a15 a15Domains a15Hints 6) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P3 : segment (checkRow a15 a15Domains a15Hints 6) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P4 : segment (checkRow a15 a15Domains a15Hints 6) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P5 : segment (checkRow a15 a15Domains a15Hints 6) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P6 : segment (checkRow a15 a15Domains a15Hints 6) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P7 : segment (checkRow a15 a15Domains a15Hints 6) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P8 : segment (checkRow a15 a15Domains a15Hints 6) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P9 : segment (checkRow a15 a15Domains a15Hints 6) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P10 : segment (checkRow a15 a15Domains a15Hints 6) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P11 : segment (checkRow a15 a15Domains a15Hints 6) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P12 : segment (checkRow a15 a15Domains a15Hints 6) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P13 : segment (checkRow a15 a15Domains a15Hints 6) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P14 : segment (checkRow a15 a15Domains a15Hints 6) 140 8 = true := by decide +kernel
theorem a15S6 (j : Nat) (hj : j < 148) : (checkRow a15 a15Domains a15Hints 6) j = true := by
  by_cases bound : j < 70
  ·
    by_cases bound : j < 30
    ·
      by_cases bound : j < 10
      ·
        exact segmentRange a15S6P0 j (by omega) (by omega)
      ·
        by_cases bound : j < 20
        ·
          exact segmentRange a15S6P1 j (by omega) (by omega)
        ·
          exact segmentRange a15S6P2 j (by omega) (by omega)
    ·
      by_cases bound : j < 50
      ·
        by_cases bound : j < 40
        ·
          exact segmentRange a15S6P3 j (by omega) (by omega)
        ·
          exact segmentRange a15S6P4 j (by omega) (by omega)
      ·
        by_cases bound : j < 60
        ·
          exact segmentRange a15S6P5 j (by omega) (by omega)
        ·
          exact segmentRange a15S6P6 j (by omega) (by omega)
  ·
    by_cases bound : j < 110
    ·
      by_cases bound : j < 90
      ·
        by_cases bound : j < 80
        ·
          exact segmentRange a15S6P7 j (by omega) (by omega)
        ·
          exact segmentRange a15S6P8 j (by omega) (by omega)
      ·
        by_cases bound : j < 100
        ·
          exact segmentRange a15S6P9 j (by omega) (by omega)
        ·
          exact segmentRange a15S6P10 j (by omega) (by omega)
    ·
      by_cases bound : j < 130
      ·
        by_cases bound : j < 120
        ·
          exact segmentRange a15S6P11 j (by omega) (by omega)
        ·
          exact segmentRange a15S6P12 j (by omega) (by omega)
      ·
        by_cases bound : j < 140
        ·
          exact segmentRange a15S6P13 j (by omega) (by omega)
        ·
          exact segmentRange a15S6P14 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S7P0 : segment (checkRow a15 a15Domains a15Hints 7) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S7P1 : segment (checkRow a15 a15Domains a15Hints 7) 10 7 = true := by decide +kernel
theorem a15S7 (j : Nat) (hj : j < 17) : (checkRow a15 a15Domains a15Hints 7) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a15S7P0 j (by omega) (by omega)
  ·
    exact segmentRange a15S7P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S8P0 : segment (checkRow a15 a15Domains a15Hints 8) 0 1 = true := by decide +kernel
theorem a15S8 (j : Nat) (hj : j < 1) : (checkRow a15 a15Domains a15Hints 8) j = true := by
  exact segmentRange a15S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Complete : Complete a15 a15Domains a15Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a15S3 j hj
  · exact a15S4 j hj
  · exact a15S5 j hj
  · exact a15S6 j hj
  · exact a15S7 j hj
  · exact a15S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P0 : segment (checkRow a16 a16Domains a16Hints 5) 0 2 = true := by decide +kernel
theorem a16S5 (j : Nat) (hj : j < 2) : (checkRow a16 a16Domains a16Hints 5) j = true := by
  exact segmentRange a16S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P0 : segment (checkRow a16 a16Domains a16Hints 6) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P1 : segment (checkRow a16 a16Domains a16Hints 6) 10 2 = true := by decide +kernel
theorem a16S6 (j : Nat) (hj : j < 12) : (checkRow a16 a16Domains a16Hints 6) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a16S6P0 j (by omega) (by omega)
  ·
    exact segmentRange a16S6P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S7P0 : segment (checkRow a16 a16Domains a16Hints 7) 0 1 = true := by decide +kernel
theorem a16S7 (j : Nat) (hj : j < 1) : (checkRow a16 a16Domains a16Hints 7) j = true := by
  exact segmentRange a16S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Complete : Complete a16 a16Domains a16Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a16S5 j hj
  · exact a16S6 j hj
  · exact a16S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S3P0 : segment (checkRow a17 a17Domains a17Hints 3) 0 1 = true := by decide +kernel
theorem a17S3 (j : Nat) (hj : j < 1) : (checkRow a17 a17Domains a17Hints 3) j = true := by
  exact segmentRange a17S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Complete : Complete a17 a17Domains a17Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a17S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S4P0 : segment (checkRow a18 a18Domains a18Hints 4) 0 4 = true := by decide +kernel
theorem a18S4 (j : Nat) (hj : j < 4) : (checkRow a18 a18Domains a18Hints 4) j = true := by
  exact segmentRange a18S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P0 : segment (checkRow a18 a18Domains a18Hints 5) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P1 : segment (checkRow a18 a18Domains a18Hints 5) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P2 : segment (checkRow a18 a18Domains a18Hints 5) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P3 : segment (checkRow a18 a18Domains a18Hints 5) 30 1 = true := by decide +kernel
theorem a18S5 (j : Nat) (hj : j < 31) : (checkRow a18 a18Domains a18Hints 5) j = true := by
  by_cases bound : j < 20
  ·
    by_cases bound : j < 10
    ·
      exact segmentRange a18S5P0 j (by omega) (by omega)
    ·
      exact segmentRange a18S5P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 30
    ·
      exact segmentRange a18S5P2 j (by omega) (by omega)
    ·
      exact segmentRange a18S5P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P0 : segment (checkRow a18 a18Domains a18Hints 6) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P1 : segment (checkRow a18 a18Domains a18Hints 6) 10 3 = true := by decide +kernel
theorem a18S6 (j : Nat) (hj : j < 13) : (checkRow a18 a18Domains a18Hints 6) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a18S6P0 j (by omega) (by omega)
  ·
    exact segmentRange a18S6P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S7P0 : segment (checkRow a18 a18Domains a18Hints 7) 0 1 = true := by decide +kernel
theorem a18S7 (j : Nat) (hj : j < 1) : (checkRow a18 a18Domains a18Hints 7) j = true := by
  exact segmentRange a18S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Complete : Complete a18 a18Domains a18Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a18S4 j hj
  · exact a18S5 j hj
  · exact a18S6 j hj
  · exact a18S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S4P0 : segment (checkRow a19 a19Domains a19Hints 4) 0 3 = true := by decide +kernel
theorem a19S4 (j : Nat) (hj : j < 3) : (checkRow a19 a19Domains a19Hints 4) j = true := by
  exact segmentRange a19S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P0 : segment (checkRow a19 a19Domains a19Hints 5) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P1 : segment (checkRow a19 a19Domains a19Hints 5) 10 7 = true := by decide +kernel
theorem a19S5 (j : Nat) (hj : j < 17) : (checkRow a19 a19Domains a19Hints 5) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a19S5P0 j (by omega) (by omega)
  ·
    exact segmentRange a19S5P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P0 : segment (checkRow a19 a19Domains a19Hints 6) 0 9 = true := by decide +kernel
theorem a19S6 (j : Nat) (hj : j < 9) : (checkRow a19 a19Domains a19Hints 6) j = true := by
  exact segmentRange a19S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P0 : segment (checkRow a19 a19Domains a19Hints 7) 0 1 = true := by decide +kernel
theorem a19S7 (j : Nat) (hj : j < 1) : (checkRow a19 a19Domains a19Hints 7) j = true := by
  exact segmentRange a19S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19Complete : Complete a19 a19Domains a19Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a19S4 j hj
  · exact a19S5 j hj
  · exact a19S6 j hj
  · exact a19S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20S7P0 : segment (checkRow a20 a20Domains a20Hints 7) 0 1 = true := by decide +kernel
theorem a20S7 (j : Nat) (hj : j < 1) : (checkRow a20 a20Domains a20Hints 7) j = true := by
  exact segmentRange a20S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20Complete : Complete a20 a20Domains a20Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a20S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21S6P0 : segment (checkRow a21 a21Domains a21Hints 6) 0 1 = true := by decide +kernel
theorem a21S6 (j : Nat) (hj : j < 1) : (checkRow a21 a21Domains a21Hints 6) j = true := by
  exact segmentRange a21S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21Complete : Complete a21 a21Domains a21Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a21S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S4P0 : segment (checkRow a22 a22Domains a22Hints 4) 0 2 = true := by decide +kernel
theorem a22S4 (j : Nat) (hj : j < 2) : (checkRow a22 a22Domains a22Hints 4) j = true := by
  exact segmentRange a22S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S5P0 : segment (checkRow a22 a22Domains a22Hints 5) 0 6 = true := by decide +kernel
theorem a22S5 (j : Nat) (hj : j < 6) : (checkRow a22 a22Domains a22Hints 5) j = true := by
  exact segmentRange a22S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S6P0 : segment (checkRow a22 a22Domains a22Hints 6) 0 1 = true := by decide +kernel
theorem a22S6 (j : Nat) (hj : j < 1) : (checkRow a22 a22Domains a22Hints 6) j = true := by
  exact segmentRange a22S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22Complete : Complete a22 a22Domains a22Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a22S4 j hj
  · exact a22S5 j hj
  · exact a22S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23S6P0 : segment (checkRow a23 a23Domains a23Hints 6) 0 1 = true := by decide +kernel
theorem a23S6 (j : Nat) (hj : j < 1) : (checkRow a23 a23Domains a23Hints 6) j = true := by
  exact segmentRange a23S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23Complete : Complete a23 a23Domains a23Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a23S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S6P0 : segment (checkRow a24 a24Domains a24Hints 6) 0 1 = true := by decide +kernel
theorem a24S6 (j : Nat) (hj : j < 1) : (checkRow a24 a24Domains a24Hints 6) j = true := by
  exact segmentRange a24S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24Complete : Complete a24 a24Domains a24Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a24S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25S6P0 : segment (checkRow a25 a25Domains a25Hints 6) 0 1 = true := by decide +kernel
theorem a25S6 (j : Nat) (hj : j < 1) : (checkRow a25 a25Domains a25Hints 6) j = true := by
  exact segmentRange a25S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25Complete : Complete a25 a25Domains a25Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a25S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26S5P0 : segment (checkRow a26 a26Domains a26Hints 5) 0 1 = true := by decide +kernel
theorem a26S5 (j : Nat) (hj : j < 1) : (checkRow a26 a26Domains a26Hints 5) j = true := by
  exact segmentRange a26S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26Complete : Complete a26 a26Domains a26Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a26S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27S5P0 : segment (checkRow a27 a27Domains a27Hints 5) 0 1 = true := by decide +kernel
theorem a27S5 (j : Nat) (hj : j < 1) : (checkRow a27 a27Domains a27Hints 5) j = true := by
  exact segmentRange a27S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27Complete : Complete a27 a27Domains a27Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a27S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28S5P0 : segment (checkRow a28 a28Domains a28Hints 5) 0 1 = true := by decide +kernel
theorem a28S5 (j : Nat) (hj : j < 1) : (checkRow a28 a28Domains a28Hints 5) j = true := by
  exact segmentRange a28S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28Complete : Complete a28 a28Domains a28Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a28S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S5P0 : segment (checkRow a29 a29Domains a29Hints 5) 0 5 = true := by decide +kernel
theorem a29S5 (j : Nat) (hj : j < 5) : (checkRow a29 a29Domains a29Hints 5) j = true := by
  exact segmentRange a29S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P0 : segment (checkRow a29 a29Domains a29Hints 6) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P1 : segment (checkRow a29 a29Domains a29Hints 6) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P2 : segment (checkRow a29 a29Domains a29Hints 6) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P3 : segment (checkRow a29 a29Domains a29Hints 6) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P4 : segment (checkRow a29 a29Domains a29Hints 6) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P5 : segment (checkRow a29 a29Domains a29Hints 6) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P6 : segment (checkRow a29 a29Domains a29Hints 6) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P7 : segment (checkRow a29 a29Domains a29Hints 6) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P8 : segment (checkRow a29 a29Domains a29Hints 6) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P9 : segment (checkRow a29 a29Domains a29Hints 6) 90 4 = true := by decide +kernel
theorem a29S6 (j : Nat) (hj : j < 94) : (checkRow a29 a29Domains a29Hints 6) j = true := by
  by_cases bound : j < 50
  ·
    by_cases bound : j < 20
    ·
      by_cases bound : j < 10
      ·
        exact segmentRange a29S6P0 j (by omega) (by omega)
      ·
        exact segmentRange a29S6P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 30
      ·
        exact segmentRange a29S6P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 40
        ·
          exact segmentRange a29S6P3 j (by omega) (by omega)
        ·
          exact segmentRange a29S6P4 j (by omega) (by omega)
  ·
    by_cases bound : j < 70
    ·
      by_cases bound : j < 60
      ·
        exact segmentRange a29S6P5 j (by omega) (by omega)
      ·
        exact segmentRange a29S6P6 j (by omega) (by omega)
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a29S6P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 90
        ·
          exact segmentRange a29S6P8 j (by omega) (by omega)
        ·
          exact segmentRange a29S6P9 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P0 : segment (checkRow a29 a29Domains a29Hints 7) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P1 : segment (checkRow a29 a29Domains a29Hints 7) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P2 : segment (checkRow a29 a29Domains a29Hints 7) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P3 : segment (checkRow a29 a29Domains a29Hints 7) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P4 : segment (checkRow a29 a29Domains a29Hints 7) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P5 : segment (checkRow a29 a29Domains a29Hints 7) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P6 : segment (checkRow a29 a29Domains a29Hints 7) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P7 : segment (checkRow a29 a29Domains a29Hints 7) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P8 : segment (checkRow a29 a29Domains a29Hints 7) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P9 : segment (checkRow a29 a29Domains a29Hints 7) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P10 : segment (checkRow a29 a29Domains a29Hints 7) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P11 : segment (checkRow a29 a29Domains a29Hints 7) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P12 : segment (checkRow a29 a29Domains a29Hints 7) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P13 : segment (checkRow a29 a29Domains a29Hints 7) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P14 : segment (checkRow a29 a29Domains a29Hints 7) 140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P15 : segment (checkRow a29 a29Domains a29Hints 7) 150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P16 : segment (checkRow a29 a29Domains a29Hints 7) 160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P17 : segment (checkRow a29 a29Domains a29Hints 7) 170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P18 : segment (checkRow a29 a29Domains a29Hints 7) 180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P19 : segment (checkRow a29 a29Domains a29Hints 7) 190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P20 : segment (checkRow a29 a29Domains a29Hints 7) 200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P21 : segment (checkRow a29 a29Domains a29Hints 7) 210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P22 : segment (checkRow a29 a29Domains a29Hints 7) 220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P23 : segment (checkRow a29 a29Domains a29Hints 7) 230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S7P24 : segment (checkRow a29 a29Domains a29Hints 7) 240 4 = true := by decide +kernel
theorem a29S7 (j : Nat) (hj : j < 244) : (checkRow a29 a29Domains a29Hints 7) j = true := by
  by_cases bound : j < 120
  ·
    by_cases bound : j < 60
    ·
      by_cases bound : j < 30
      ·
        by_cases bound : j < 10
        ·
          exact segmentRange a29S7P0 j (by omega) (by omega)
        ·
          by_cases bound : j < 20
          ·
            exact segmentRange a29S7P1 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 40
        ·
          exact segmentRange a29S7P3 j (by omega) (by omega)
        ·
          by_cases bound : j < 50
          ·
            exact segmentRange a29S7P4 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P5 j (by omega) (by omega)
    ·
      by_cases bound : j < 90
      ·
        by_cases bound : j < 70
        ·
          exact segmentRange a29S7P6 j (by omega) (by omega)
        ·
          by_cases bound : j < 80
          ·
            exact segmentRange a29S7P7 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P8 j (by omega) (by omega)
      ·
        by_cases bound : j < 100
        ·
          exact segmentRange a29S7P9 j (by omega) (by omega)
        ·
          by_cases bound : j < 110
          ·
            exact segmentRange a29S7P10 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P11 j (by omega) (by omega)
  ·
    by_cases bound : j < 180
    ·
      by_cases bound : j < 150
      ·
        by_cases bound : j < 130
        ·
          exact segmentRange a29S7P12 j (by omega) (by omega)
        ·
          by_cases bound : j < 140
          ·
            exact segmentRange a29S7P13 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P14 j (by omega) (by omega)
      ·
        by_cases bound : j < 160
        ·
          exact segmentRange a29S7P15 j (by omega) (by omega)
        ·
          by_cases bound : j < 170
          ·
            exact segmentRange a29S7P16 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P17 j (by omega) (by omega)
    ·
      by_cases bound : j < 210
      ·
        by_cases bound : j < 190
        ·
          exact segmentRange a29S7P18 j (by omega) (by omega)
        ·
          by_cases bound : j < 200
          ·
            exact segmentRange a29S7P19 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P20 j (by omega) (by omega)
      ·
        by_cases bound : j < 230
        ·
          by_cases bound : j < 220
          ·
            exact segmentRange a29S7P21 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P22 j (by omega) (by omega)
        ·
          by_cases bound : j < 240
          ·
            exact segmentRange a29S7P23 j (by omega) (by omega)
          ·
            exact segmentRange a29S7P24 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P0 : segment (checkRow a29 a29Domains a29Hints 8) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P1 : segment (checkRow a29 a29Domains a29Hints 8) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P2 : segment (checkRow a29 a29Domains a29Hints 8) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P3 : segment (checkRow a29 a29Domains a29Hints 8) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P4 : segment (checkRow a29 a29Domains a29Hints 8) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P5 : segment (checkRow a29 a29Domains a29Hints 8) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P6 : segment (checkRow a29 a29Domains a29Hints 8) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P7 : segment (checkRow a29 a29Domains a29Hints 8) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P8 : segment (checkRow a29 a29Domains a29Hints 8) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P9 : segment (checkRow a29 a29Domains a29Hints 8) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P10 : segment (checkRow a29 a29Domains a29Hints 8) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P11 : segment (checkRow a29 a29Domains a29Hints 8) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P12 : segment (checkRow a29 a29Domains a29Hints 8) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P13 : segment (checkRow a29 a29Domains a29Hints 8) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S8P14 : segment (checkRow a29 a29Domains a29Hints 8) 140 6 = true := by decide +kernel
theorem a29S8 (j : Nat) (hj : j < 146) : (checkRow a29 a29Domains a29Hints 8) j = true := by
  by_cases bound : j < 70
  ·
    by_cases bound : j < 30
    ·
      by_cases bound : j < 10
      ·
        exact segmentRange a29S8P0 j (by omega) (by omega)
      ·
        by_cases bound : j < 20
        ·
          exact segmentRange a29S8P1 j (by omega) (by omega)
        ·
          exact segmentRange a29S8P2 j (by omega) (by omega)
    ·
      by_cases bound : j < 50
      ·
        by_cases bound : j < 40
        ·
          exact segmentRange a29S8P3 j (by omega) (by omega)
        ·
          exact segmentRange a29S8P4 j (by omega) (by omega)
      ·
        by_cases bound : j < 60
        ·
          exact segmentRange a29S8P5 j (by omega) (by omega)
        ·
          exact segmentRange a29S8P6 j (by omega) (by omega)
  ·
    by_cases bound : j < 110
    ·
      by_cases bound : j < 90
      ·
        by_cases bound : j < 80
        ·
          exact segmentRange a29S8P7 j (by omega) (by omega)
        ·
          exact segmentRange a29S8P8 j (by omega) (by omega)
      ·
        by_cases bound : j < 100
        ·
          exact segmentRange a29S8P9 j (by omega) (by omega)
        ·
          exact segmentRange a29S8P10 j (by omega) (by omega)
    ·
      by_cases bound : j < 130
      ·
        by_cases bound : j < 120
        ·
          exact segmentRange a29S8P11 j (by omega) (by omega)
        ·
          exact segmentRange a29S8P12 j (by omega) (by omega)
      ·
        by_cases bound : j < 140
        ·
          exact segmentRange a29S8P13 j (by omega) (by omega)
        ·
          exact segmentRange a29S8P14 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S9P0 : segment (checkRow a29 a29Domains a29Hints 9) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S9P1 : segment (checkRow a29 a29Domains a29Hints 9) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S9P2 : segment (checkRow a29 a29Domains a29Hints 9) 20 8 = true := by decide +kernel
theorem a29S9 (j : Nat) (hj : j < 28) : (checkRow a29 a29Domains a29Hints 9) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a29S9P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 20
    ·
      exact segmentRange a29S9P1 j (by omega) (by omega)
    ·
      exact segmentRange a29S9P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S10P0 : segment (checkRow a29 a29Domains a29Hints 10) 0 1 = true := by decide +kernel
theorem a29S10 (j : Nat) (hj : j < 1) : (checkRow a29 a29Domains a29Hints 10) j = true := by
  exact segmentRange a29S10P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29Complete : Complete a29 a29Domains a29Hints := by
  intro k hk j hj
  change k ≤ 10 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a29S5 j hj
  · exact a29S6 j hj
  · exact a29S7 j hj
  · exact a29S8 j hj
  · exact a29S9 j hj
  · exact a29S10 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0Bound : Lower true (roots a0) (target a0) 4 := by
  have ready : Ready a0 a0Domains (asRow a0Pos) (asRow a0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a0
  exact frozen ready a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 0, 2), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D0 : Slice true (roots a1) (target a1) (repeatWord 6148914691236517205) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 1 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D1 : Slice true (roots a1) (target a1) (repeatWord 3689348814741910323) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 2 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D2 : Slice true (roots a1) (target a1) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 84, flipInput 0, flipInput 1] ++ fixRows 4 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D3 : Slice true (roots a1) (target a1) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 16 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Bound : Lower true (roots a1) (target a1) 7 := by
  have ready : Ready a1 a1Domains (asRow a1Pos) (asRow a1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a1D0 (safeCons a1D1 (safeCons a1D2 (safeCons a1D3 (safeNil a1))))
  exact frozen ready a1Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Bound : Lower true (roots a2) (target a2) 3 := by
  have ready : Ready a2 a2Domains (asRow a2Pos) (asRow a2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a2
  exact frozen ready a2Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D0 : Slice true (roots a3) (target a3) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 67, flipInput 2, flipInput 4] ++ fixRows 0 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D1 : Slice true (roots a3) (target a3) (repeatWord 17298308644996116495) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 67, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D2 : Slice true (roots a3) (target a3) (repeatWord 18446462603027742720) 3 :=
  signedSlice (ms := ([swapRows 67, flipInput 2, flipInput 3] ++ fixRows 0 16)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D3 : Slice true (roots a3) (target a3) (repeatWord 18446744069414584320) 3 :=
  signedSlice (ms := ([swapRows 67, swapRows 84, flipInput 2, flipInput 3] ++ fixRows 0 32)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Bound : Lower true (roots a3) (target a3) 6 := by
  have ready : Ready a3 a3Domains (asRow a3Pos) (asRow a3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a3D0 (safeCons a3D1 (safeCons a3D2 (safeCons a3D3 (safeNil a3))))
  exact frozen ready a3Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 20, 28), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4D0 : Slice true (roots a4) (target a4) (repeatWord 71777214294589695) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 1, flipInput 4] ++ fixRows 8 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Bound : Lower true (roots a4) (target a4) 6 := by
  have ready : Ready a4 a4Domains (asRow a4Pos) (asRow a4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a4D0 (safeNil a4)
  exact frozen ready a4Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D0 : Slice true (roots a5) (target a5) (repeatWord 6510615555426900570) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D1 : Slice true (roots a5) (target a5) (repeatWord 6172840429334713770) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D2 : Slice true (roots a5) (target a5) (repeatWord 12297735558912431445) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D3 : Slice true (roots a5) (target a5) (repeatWord 17298308644996116495) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 84, flipInput 0, flipInput 3] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D4 : Slice true (roots a5) (target a5) (repeatWord 1085350949055099120) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D5 : Slice true (roots a5) (target a5) (repeatWord 72056494543077120) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 0 0 ++ identifyRows 3 4 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Bound : Lower true (roots a5) (target a5) 6 := by
  have ready : Ready a5 a5Domains (asRow a5Pos) (asRow a5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a5D0 (safeCons a5D1 (safeCons a5D2 (safeCons a5D3 (safeCons a5D4 (safeCons a5D5 (safeNil a5))))))
  exact frozen ready a5Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D0 : Slice true (roots a6) (target a6) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67] ++ fixRows 0 8)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Bound : Lower true (roots a6) (target a6) 5 := by
  have ready : Ready a6 a6Domains (asRow a6Pos) (asRow a6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a6D0 (safeNil a6)
  exact frozen ready a6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D0 : Slice true (roots a7) (target a7) (repeatWord 3689348814741910323) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 67] ++ fixRows 2 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Bound : Lower true (roots a7) (target a7) 5 := by
  have ready : Ready a7 a7Domains (asRow a7Pos) (asRow a7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a7D0 (safeNil a7)
  exact frozen ready a7Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D0 : Slice true (roots a8) (target a8) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67, flipInput 0] ++ fixRows 0 8)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Bound : Lower true (roots a8) (target a8) 5 := by
  have ready : Ready a8 a8Domains (asRow a8Pos) (asRow a8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a8D0 (safeNil a8)
  exact frozen ready a8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Bound : Lower true (roots a9) (target a9) 4 := by
  have ready : Ready a9 a9Domains (asRow a9Pos) (asRow a9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a9
  exact frozen ready a9Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 0, 16)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D0 : Slice true (roots a10) (target a10) (repeatWord 3732415143318664140) 7 :=
  signedSlice (ms := ([swapRows 48, swapRows 81, swapRows 50, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D1 : Slice true (roots a10) (target a10) (repeatWord 17298308644996116495) 7 :=
  signedSlice (ms := ([swapRows 48, swapRows 49, swapRows 82, swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D2 : Slice true (roots a10) (target a10) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([] ++ fixRows 2 0)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D3 : Slice true (roots a10) (target a10) (repeatWord 71777214294589695) 6 :=
  signedSlice (ms := ([swapRows 50] ++ fixRows 8 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D4 : Slice true (roots a10) (target a10) (repeatWord 281470681808895) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 84, flipInput 3] ++ fixRows 16 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D5 : Slice true (roots a10) (target a10) (repeatWord 4294967295) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 3] ++ fixRows 32 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D6 : Slice true (roots a10) (target a10) (repeatWord 3689517697150995660) 6 :=
  signedSlice (ms := ([swapRows 67, swapRows 84, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D7 : Slice true (roots a10) (target a10) (repeatWord 3689348817318890700) 6 :=
  signedSlice (ms := ([swapRows 67, flipInput 2, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D8 : Slice true (roots a10) (target a10) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 16, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 4 0)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D9 : Slice true (roots a10) (target a10) (repeatWord 18374966859414961920) 5 :=
  signedSlice (ms := ([swapRows 50, flipInput 2, flipInput 4] ++ fixRows 0 8)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D10 : Slice true (roots a10) (target a10) (repeatWord 4340410370284600380) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 67, flipInput 2, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D11 : Slice true (roots a10) (target a10) (repeatWord 18446462603027742720) 4 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 0 16)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D12 : Slice true (roots a10) (target a10) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D13 : Slice true (roots a10) (target a10) (repeatWord 3674993371882992384) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 67, flipInput 2, flipInput 4] ++ fixRows 2 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D14 : Slice true (roots a10) (target a10) (repeatWord 4222189076152335) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 1, flipInput 4] ++ fixRows 12 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D15 : Slice true (roots a10) (target a10) (repeatWord 3689292520605548544) 3 :=
  signedSlice (ms := ([swapRows 67, flipInput 2, flipInput 3] ++ fixRows 2 16)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D16 : Slice true (roots a10) (target a10) (repeatWord 3689348813882916864) 3 :=
  signedSlice (ms := ([swapRows 67, swapRows 84, flipInput 2, flipInput 3] ++ fixRows 2 32)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Bound : Lower true (roots a10) (target a10) 9 := by
  have ready : Ready a10 a10Domains (asRow a10Pos) (asRow a10Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a10D0 (safeCons a10D1 (safeCons a10D2 (safeCons a10D3 (safeCons a10D4 (safeCons a10D5 (safeCons a10D6 (safeCons a10D7 (safeCons a10D8 (safeCons a10D9 (safeCons a10D10 (safeCons a10D11 (safeCons a10D12 (safeCons a10D13 (safeCons a10D14 (safeCons a10D15 (safeCons a10D16 (safeNil a10)))))))))))))))))
  exact frozen ready a10Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D0 : Slice true (roots a11) (target a11) (repeatWord 281470681808895) 3 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 83, flipInput 1, flipInput 3] ++ fixRows 16 0)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Bound : Lower true (roots a11) (target a11) 5 := by
  have ready : Ready a11 a11Domains (asRow a11Pos) (asRow a11Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a11D0 (safeNil a11)
  exact frozen ready a11Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Bound : Lower true (roots a12) (target a12) 4 := by
  have ready : Ready a12 a12Domains (asRow a12Pos) (asRow a12Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a12
  exact frozen ready a12Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D0 : Slice true (roots a13) (target a13) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Bound : Lower true (roots a13) (target a13) 5 := by
  have ready : Ready a13 a13Domains (asRow a13Pos) (asRow a13Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a13D0 (safeNil a13)
  exact frozen ready a13Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D0 : Slice true (roots a14) (target a14) (repeatWord 17298308644996116495) 7 :=
  signedSlice (ms := ([swapRows 48, swapRows 49, swapRows 82, swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D1 : Slice true (roots a14) (target a14) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 81, swapRows 83, swapRows 84, flipInput 3, flipInput 4] ++ fixRows 2 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D2 : Slice true (roots a14) (target a14) (repeatWord 1085102592571150095) 6 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D3 : Slice true (roots a14) (target a14) (repeatWord 18446462598732906495) 6 :=
  signedSlice (ms := ([swapRows 49, swapRows 66, swapRows 67, flipInput 1, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D4 : Slice true (roots a14) (target a14) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, flipInput 1, flipInput 4] ++ fixRows 8 0)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D5 : Slice true (roots a14) (target a14) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 16 0)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D6 : Slice true (roots a14) (target a14) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D7 : Slice true (roots a14) (target a14) (repeatWord 4340410370284600380) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D8 : Slice true (roots a14) (target a14) (repeatWord 3732415143318664140) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 67, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D9 : Slice true (roots a14) (target a14) (repeatWord 1085350949055099120) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D10 : Slice true (roots a14) (target a14) (repeatWord 1085102596360827120) 5 :=
  signedSlice (ms := ([flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 5 true)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D11 : Slice true (roots a14) (target a14) (repeatWord 72056494543077120) 5 :=
  signedSlice (ms := ([swapRows 50, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 3 4 true)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D12 : Slice true (roots a14) (target a14) (repeatWord 71777218556133120) 5 :=
  signedSlice (ms := ([swapRows 50, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 3 5 true)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D13 : Slice true (roots a14) (target a14) (repeatWord 4222189076152335) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 1, flipInput 4] ++ fixRows 12 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D14 : Slice true (roots a14) (target a14) (repeatWord 65535) 3 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 83, flipInput 1, flipInput 3] ++ fixRows 48 0)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Bound : Lower true (roots a14) (target a14) 9 := by
  have ready : Ready a14 a14Domains (asRow a14Pos) (asRow a14Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a14D0 (safeCons a14D1 (safeCons a14D2 (safeCons a14D3 (safeCons a14D4 (safeCons a14D5 (safeCons a14D6 (safeCons a14D7 (safeCons a14D8 (safeCons a14D9 (safeCons a14D10 (safeCons a14D11 (safeCons a14D12 (safeCons a14D13 (safeCons a14D14 (safeNil a14)))))))))))))))
  exact frozen ready a14Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D0 : Slice true (roots a15) (target a15) (repeatWord 6510615555426900570) 7 :=
  signedSlice (ms := ([swapRows 48, swapRows 81, swapRows 50, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D1 : Slice true (roots a15) (target a15) (repeatWord 18374966859414961920) 6 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 4] ++ fixRows 0 8)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D2 : Slice true (roots a15) (target a15) (repeatWord 281470681808895) 6 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 16 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D3 : Slice true (roots a15) (target a15) (repeatWord 4294967295) 6 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D4 : Slice true (roots a15) (target a15) (repeatWord 12297829382473034410) 5 :=
  signedSlice (ms := ([swapRows 33, flipInput 4] ++ fixRows 0 1)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D5 : Slice true (roots a15) (target a15) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 16, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 4 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D6 : Slice true (roots a15) (target a15) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 67, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D7 : Slice true (roots a15) (target a15) (repeatWord 12297735558912431445) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D8 : Slice true (roots a15) (target a15) (repeatWord 12297829381041378645) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 84, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D9 : Slice true (roots a15) (target a15) (repeatWord 17298308644996116495) 5 :=
  signedSlice (ms := ([swapRows 67, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D10 : Slice true (roots a15) (target a15) (repeatWord 1085350949055099120) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D11 : Slice true (roots a15) (target a15) (repeatWord 1085102596360827120) 5 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 5 true)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D12 : Slice true (roots a15) (target a15) (repeatWord 723401728380766730) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 67, flipInput 4] ++ fixRows 4 1)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Bound : Lower true (roots a15) (target a15) 9 := by
  have ready : Ready a15 a15Domains (asRow a15Pos) (asRow a15Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a15D0 (safeCons a15D1 (safeCons a15D2 (safeCons a15D3 (safeCons a15D4 (safeCons a15D5 (safeCons a15D6 (safeCons a15D7 (safeCons a15D8 (safeCons a15D9 (safeCons a15D10 (safeCons a15D11 (safeCons a15D12 (safeNil a15)))))))))))))
  exact frozen ready a15Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 4, 12), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D0 : Slice true (roots a16) (target a16) (repeatWord 6510615555426900570) 6 :=
  signedSlice (ms := ([swapRows 50] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D1 : Slice true (roots a16) (target a16) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 81, swapRows 66, swapRows 83, flipInput 1] ++ fixRows 16 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D2 : Slice true (roots a16) (target a16) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 67, swapRows 84, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 0 16)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D3 : Slice true (roots a16) (target a16) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 81, swapRows 66, swapRows 83, swapRows 84, flipInput 1] ++ fixRows 32 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D4 : Slice true (roots a16) (target a16) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 67, flipInput 0, flipInput 1, flipInput 4] ++ fixRows 0 32)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D5 : Slice true (roots a16) (target a16) (repeatWord 723401728380766730) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 1, flipInput 4] ++ fixRows 4 1)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Bound : Lower true (roots a16) (target a16) 8 := by
  have ready : Ready a16 a16Domains (asRow a16Pos) (asRow a16Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a16D0 (safeCons a16D1 (safeCons a16D2 (safeCons a16D3 (safeCons a16D4 (safeCons a16D5 (safeNil a16))))))
  exact frozen ready a16Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Bound : Lower true (roots a17) (target a17) 4 := by
  have ready : Ready a17 a17Domains (asRow a17Pos) (asRow a17Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a17
  exact frozen ready a17Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D0 : Slice true (roots a18) (target a18) (repeatWord 11068046444225730969) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 3] ++ fixRows 0 0 ++ identifyRows 0 1 false)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D1 : Slice true (roots a18) (target a18) (repeatWord 6510615555426900570) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 3] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D2 : Slice true (roots a18) (target a18) (repeatWord 3732415143318664140) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D3 : Slice true (roots a18) (target a18) (repeatWord 17298308644996116495) 6 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, flipInput 1] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D4 : Slice true (roots a18) (target a18) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 1 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D5 : Slice true (roots a18) (target a18) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 81, swapRows 66, swapRows 83, swapRows 84, flipInput 1] ++ fixRows 8 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D6 : Slice true (roots a18) (target a18) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 49, swapRows 66, swapRows 83, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 0 16)) (base := roots a8) (G := (neg (target a8))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a8Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D7 : Slice true (roots a18) (target a18) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D8 : Slice true (roots a18) (target a18) (repeatWord 12297735558912431445) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 84, flipInput 1, flipInput 2, flipInput 3] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D9 : Slice true (roots a18) (target a18) (repeatWord 4340410370284600380) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 50] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D10 : Slice true (roots a18) (target a18) (repeatWord 14757226376558555955) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 82, flipInput 0, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 4 false)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D11 : Slice true (roots a18) (target a18) (repeatWord 3689517697150995660) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 2, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D12 : Slice true (roots a18) (target a18) (repeatWord 17361393124654452495) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 65, swapRows 66, swapRows 83, swapRows 84, flipInput 0, flipInput 1, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D13 : Slice true (roots a18) (target a18) (repeatWord 1085350949055099120) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 65, swapRows 66, swapRows 84, flipInput 0, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D14 : Slice true (roots a18) (target a18) (repeatWord 18374687579166474495) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 65, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 1, flipInput 2] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D15 : Slice true (roots a18) (target a18) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D16 : Slice true (roots a18) (target a18) (repeatWord 6148820867675914240) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 1 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D17 : Slice true (roots a18) (target a18) (repeatWord 71776119077928960) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 8 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Bound : Lower true (roots a18) (target a18) 8 := by
  have ready : Ready a18 a18Domains (asRow a18Pos) (asRow a18Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a18D0 (safeCons a18D1 (safeCons a18D2 (safeCons a18D3 (safeCons a18D4 (safeCons a18D5 (safeCons a18D6 (safeCons a18D7 (safeCons a18D8 (safeCons a18D9 (safeCons a18D10 (safeCons a18D11 (safeCons a18D12 (safeCons a18D13 (safeCons a18D14 (safeCons a18D15 (safeCons a18D16 (safeCons a18D17 (safeNil a18))))))))))))))))))
  exact frozen ready a18Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D0 : Slice true (roots a19) (target a19) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 67] ++ fixRows 1 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D1 : Slice true (roots a19) (target a19) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([] ++ fixRows 2 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D2 : Slice true (roots a19) (target a19) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 67, flipInput 0, flipInput 1, flipInput 4, flipInput 5] ++ fixRows 8 0)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D3 : Slice true (roots a19) (target a19) (repeatWord 18374966859414961920) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 50, flipInput 0, flipInput 4, flipInput 5] ++ fixRows 0 8)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D4 : Slice true (roots a19) (target a19) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 65, swapRows 66, flipInput 0, flipInput 1, flipInput 3, flipInput 5] ++ fixRows 16 0)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D5 : Slice true (roots a19) (target a19) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67, flipInput 1, flipInput 3, flipInput 5] ++ fixRows 0 16)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D6 : Slice true (roots a19) (target a19) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 66, swapRows 67] ++ fixRows 0 32)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D7 : Slice true (roots a19) (target a19) (repeatWord 6148820867675914240) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50] ++ fixRows 1 16)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D8 : Slice true (roots a19) (target a19) (repeatWord 3674993371882992384) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67] ++ fixRows 2 8)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D9 : Slice true (roots a19) (target a19) (repeatWord 1095216660735) 4 :=
  signedSlice (ms := ([] ++ fixRows 24 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19Bound : Lower true (roots a19) (target a19) 8 := by
  have ready : Ready a19 a19Domains (asRow a19Pos) (asRow a19Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a19D0 (safeCons a19D1 (safeCons a19D2 (safeCons a19D3 (safeCons a19D4 (safeCons a19D5 (safeCons a19D6 (safeCons a19D7 (safeCons a19D8 (safeCons a19D9 (safeNil a19))))))))))
  exact frozen ready a19Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20D0 : Slice true (roots a20) (target a20) (repeatWord 18446744069414584320) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20Bound : Lower true (roots a20) (target a20) 8 := by
  have ready : Ready a20 a20Domains (asRow a20Pos) (asRow a20Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a20D0 (safeNil a20)
  exact frozen ready a20Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21D0 : Slice true (roots a21) (target a21) (repeatWord 18374966859414961920) 6 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 4] ++ fixRows 0 8)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21Bound : Lower true (roots a21) (target a21) 7 := by
  have ready : Ready a21 a21Domains (asRow a21Pos) (asRow a21Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a21D0 (safeNil a21)
  exact frozen ready a21Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 20, 28), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D0 : Slice true (roots a22) (target a22) (repeatWord 12297829382473034410) 5 :=
  signedSlice (ms := ([swapRows 16, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 0 1)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D1 : Slice true (roots a22) (target a22) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, flipInput 0, flipInput 5] ++ fixRows 8 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D2 : Slice true (roots a22) (target a22) (repeatWord 3732415143318664140) 5 :=
  signedSlice (ms := ([swapRows 16, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D3 : Slice true (roots a22) (target a22) (repeatWord 18446462603027742720) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 0 16)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D4 : Slice true (roots a22) (target a22) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 66, swapRows 67] ++ fixRows 0 32)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22Bound : Lower true (roots a22) (target a22) 7 := by
  have ready : Ready a22 a22Domains (asRow a22Pos) (asRow a22Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a22D0 (safeCons a22D1 (safeCons a22D2 (safeCons a22D3 (safeCons a22D4 (safeNil a22)))))
  exact frozen ready a22Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19), (inputs.getD 1 zero, 8, 10), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23D0 : Slice true (roots a23) (target a23) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 4] ++ fixRows 2 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23Bound : Lower true (roots a23) (target a23) 7 := by
  have ready : Ready a23 a23Domains (asRow a23Pos) (asRow a23Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a23D0 (safeNil a23)
  exact frozen ready a23Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D0 : Slice true (roots a24) (target a24) (repeatWord 18374687579166474495) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24Bound : Lower true (roots a24) (target a24) 7 := by
  have ready : Ready a24 a24Domains (asRow a24Pos) (asRow a24Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a24D0 (safeNil a24)
  exact frozen ready a24Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D0 : Slice true (roots a25) (target a25) (repeatWord 281470681808895) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 84, flipInput 3] ++ fixRows 16 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25Bound : Lower true (roots a25) (target a25) 7 := by
  have ready : Ready a25 a25Domains (asRow a25Pos) (asRow a25Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a25D0 (safeNil a25)
  exact frozen ready a25Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D0 : Slice true (roots a26) (target a26) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 83, flipInput 3] ++ fixRows 16 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26Bound : Lower true (roots a26) (target a26) 6 := by
  have ready : Ready a26 a26Domains (asRow a26Pos) (asRow a26Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a26D0 (safeNil a26)
  exact frozen ready a26Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27D0 : Slice true (roots a27) (target a27) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 16, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 4 0)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27Bound : Lower true (roots a27) (target a27) 6 := by
  have ready : Ready a27 a27Domains (asRow a27Pos) (asRow a27Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a27D0 (safeNil a27)
  exact frozen ready a27Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28D0 : Slice true (roots a28) (target a28) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, swapRows 84] ++ fixRows 16 0)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28Bound : Lower true (roots a28) (target a28) 6 := by
  have ready : Ready a28 a28Domains (asRow a28Pos) (asRow a28Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a28D0 (safeNil a28)
  exact frozen ready a28Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D0 : Slice true (roots a29) (target a29) (repeatWord 6510615555426900570) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D1 : Slice true (roots a29) (target a29) (repeatWord 6172840429334713770) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a14) (G := (target a14)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a14Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D2 : Slice true (roots a29) (target a29) (repeatWord 3732415143318664140) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D3 : Slice true (roots a29) (target a29) (repeatWord 17298308644996116495) 9 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, flipInput 1] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D4 : Slice true (roots a29) (target a29) (repeatWord 71777214294589695) 8 :=
  signedSlice (ms := ([] ++ fixRows 8 0)) (base := roots a16) (G := (target a16)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a16Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D5 : Slice true (roots a29) (target a29) (repeatWord 281470681808895) 8 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 16 0)) (base := roots a18) (G := (target a18)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a18Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D6 : Slice true (roots a29) (target a29) (repeatWord 4294967295) 8 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a18) (G := (target a18)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a18Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D7 : Slice true (roots a29) (target a29) (repeatWord 12297735558912431445) 8 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 82, swapRows 67, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a19) (G := (target a19)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a19Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D8 : Slice true (roots a29) (target a29) (repeatWord 12297829381041378645) 8 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 82, swapRows 67, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a19) (G := (target a19)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a19Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D9 : Slice true (roots a29) (target a29) (repeatWord 1085350949055099120) 8 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a19) (G := (target a19)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a19Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D10 : Slice true (roots a29) (target a29) (repeatWord 1085102596360827120) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 5 true)) (base := roots a19) (G := (target a19)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a19Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D11 : Slice true (roots a29) (target a29) (repeatWord 18374687579166474495) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a20) (G := (target a20)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a20Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D12 : Slice true (roots a29) (target a29) (repeatWord 18374966855153418495) 8 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 0 0 ++ identifyRows 3 5 false)) (base := roots a20) (G := (target a20)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a20Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D13 : Slice true (roots a29) (target a29) (repeatWord 3689348814741910323) 7 :=
  signedSlice (ms := ([] ++ fixRows 2 0)) (base := roots a21) (G := (target a21)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a21Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D14 : Slice true (roots a29) (target a29) (repeatWord 1085102592571150095) 7 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a22) (G := (target a22)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a22Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D15 : Slice true (roots a29) (target a29) (repeatWord 18374966859414961920) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 8)) (base := roots a23) (G := (target a23)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a23Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D16 : Slice true (roots a29) (target a29) (repeatWord 18446462603027742720) 7 :=
  signedSlice (ms := ([swapRows 84] ++ fixRows 0 16)) (base := roots a24) (G := (target a24)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a24Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D17 : Slice true (roots a29) (target a29) (repeatWord 18446744069414584320) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a24) (G := (target a24)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a24Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D18 : Slice true (roots a29) (target a29) (repeatWord 11068046444225730969) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 false)) (base := roots a25) (G := (target a25)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a25Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D19 : Slice true (roots a29) (target a29) (repeatWord 6148914691236517205) 6 :=
  signedSlice (ms := ([] ++ fixRows 1 0)) (base := roots a26) (G := (target a26)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a26Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D20 : Slice true (roots a29) (target a29) (repeatWord 12297829382473034410) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 1)) (base := roots a27) (G := (target a27)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a27Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D21 : Slice true (roots a29) (target a29) (repeatWord 3674993371882992384) 6 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 4] ++ fixRows 2 8)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D22 : Slice true (roots a29) (target a29) (repeatWord 4340410370284600380) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a28) (G := (target a28)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a28Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D23 : Slice true (roots a29) (target a29) (repeatWord 723401728380766730) 5 :=
  signedSlice (ms := ([swapRows 16, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 4 1)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D24 : Slice true (roots a29) (target a29) (repeatWord 47851476196393130) 5 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, flipInput 1, flipInput 4] ++ fixRows 8 1)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D25 : Slice true (roots a29) (target a29) (repeatWord 93823560602965) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 83, flipInput 3] ++ fixRows 17 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D26 : Slice true (roots a29) (target a29) (repeatWord 1431655765) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 33 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D27 : Slice true (roots a29) (target a29) (repeatWord 4222189076152335) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, flipInput 0, flipInput 5] ++ fixRows 12 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D28 : Slice true (roots a29) (target a29) (repeatWord 1095216660735) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 81, swapRows 66, swapRows 83, flipInput 1] ++ fixRows 24 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D29 : Slice true (roots a29) (target a29) (repeatWord 71776119077928960) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 67, swapRows 84, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 8 16)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D30 : Slice true (roots a29) (target a29) (repeatWord 16711935) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 81, swapRows 66, swapRows 83, swapRows 84, flipInput 1] ++ fixRows 40 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D31 : Slice true (roots a29) (target a29) (repeatWord 71777214277877760) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 67, flipInput 0, flipInput 1, flipInput 4] ++ fixRows 8 32)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D32 : Slice true (roots a29) (target a29) (repeatWord 18446462598732840960) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 0 48)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D33 : Slice true (roots a29) (target a29) (repeatWord 6148820867675914240) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 33 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D34 : Slice true (roots a29) (target a29) (repeatWord 6148914689804861440) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 17 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D35 : Slice true (roots a29) (target a29) (repeatWord 3689292520605548544) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 65, swapRows 67, swapRows 84] ++ fixRows 2 16)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D36 : Slice true (roots a29) (target a29) (repeatWord 3689348813882916864) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 65, swapRows 67] ++ fixRows 2 32)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D37 : Slice true (roots a29) (target a29) (repeatWord 1085086035472220160) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 4 16)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D38 : Slice true (roots a29) (target a29) (repeatWord 1085102592318504960) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 66, swapRows 67] ++ fixRows 4 32)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D39 : Slice true (roots a29) (target a29) (repeatWord 65535) 4 :=
  signedSlice (ms := ([] ++ fixRows 48 0)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D40 : Slice true (roots a29) (target a29) (repeatWord 2814792717434890) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 1, flipInput 4] ++ fixRows 12 1)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D41 : Slice true (roots a29) (target a29) (repeatWord 93823560581120) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 17 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D42 : Slice true (roots a29) (target a29) (repeatWord 1431633920) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 33 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29Bound : Lower true (roots a29) (target a29) 11 := by
  have ready : Ready a29 a29Domains (asRow a29Pos) (asRow a29Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a29D0 (safeCons a29D1 (safeCons a29D2 (safeCons a29D3 (safeCons a29D4 (safeCons a29D5 (safeCons a29D6 (safeCons a29D7 (safeCons a29D8 (safeCons a29D9 (safeCons a29D10 (safeCons a29D11 (safeCons a29D12 (safeCons a29D13 (safeCons a29D14 (safeCons a29D15 (safeCons a29D16 (safeCons a29D17 (safeCons a29D18 (safeCons a29D19 (safeCons a29D20 (safeCons a29D21 (safeCons a29D22 (safeCons a29D23 (safeCons a29D24 (safeCons a29D25 (safeCons a29D26 (safeCons a29D27 (safeCons a29D28 (safeCons a29D29 (safeCons a29D30 (safeCons a29D31 (safeCons a29D32 (safeCons a29D33 (safeCons a29D34 (safeCons a29D35 (safeCons a29D36 (safeCons a29D37 (safeCons a29D38 (safeCons a29D39 (safeCons a29D40 (safeCons a29D41 (safeCons a29D42 (safeNil a29)))))))))))))))))))))))))))))))))))))))))))
  exact frozen ready a29Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots := roots a29
def fullWord := target a29
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813032 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_37627.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩, ⟨.and,[3,6]⟩, ⟨.and,[2,7]⟩, ⟨.or,[2,3]⟩, ⟨.and,[1,9]⟩, ⟨.or,[8,10]⟩, ⟨.and,[4,5]⟩, ⟨.and,[1,6]⟩, ⟨.or,[12,13]⟩, ⟨.or,[2,14]⟩, ⟨.and,[0,15]⟩, ⟨.or,[11,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 17⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 12 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_37627
open PEqualNP.Outside.L_meta_37627 in
theorem PEqualNP.Outside.L_meta_37627 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := solve a29Bound

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43906.Model
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

end PEqualNP.Outside.L_meta_43906.Model

namespace PEqualNP.Outside.L_meta_43906
open PEqualNP.Outside.L_meta_43906.Model
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

def consecutiveWords (ws : Nat → Nat) (first : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => ws first ||| (consecutiveWords ws (first+1) k <<< 60)

def field (ws : Nat → Nat) (pos width : Nat) : Nat :=
  let r := pos % 60
  let low := (ws (pos / 60)) >>> r
  let value := if r+width ≤ 60 then low else if r+width ≤ 120 then
    low ||| ((ws (pos/60+1)) <<< (60-r))
    else low ||| (consecutiveWords ws (pos/60+1) ((r+width-1)/60) <<< (60-r))
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

def page0 : List Nat := [0x1888620c242907, 0xa3ec43a90f241d1, 0x82411c3549110f8, 0x1de649021f96659, 0x665da42907c9022, 0x12221f660905e82, 0x5fa02437a49985f, 0x906f99661786890, 0x82905e922217e68, 0x6404001e001c57e, 0x9999954c4390000, 0xa41f487249221dd, 0x93f443f997f30f, 0x280520d51c608d1, 0xe96443d0814423, 0x6b92421e0204921, 0x498f808324842aa, 0x1d35c9210e3a126, 0x7424c6760ba1263, 0xb2e22126498dcc1, 0x98a00101082020, 0x42f49210aaa4099, 0x48754c931f8208, 0x724843ec1020bc4]
def page1 : List Nat := [0xbf04c87dd0931f, 0x931be34487c0821, 0x49210dd324c6fd0, 0x778c932bd34c87d, 0x4c6fc9210bc424c, 0xe826058060f442, 0x2e00141b03d0, 0x6000020000080, 0x24c48000001000, 0xc50c20231201081, 0x9c6585944903081, 0xc80c184b9a385f7, 0x3b6410fb318ad1c, 0x32e821f485a2996, 0x31ec21f4c7f90fd, 0x10ec63f083f1975, 0x88b880a013f107e, 0xcac9a0692308046, 0xb6618817242f38, 0xe18cc66170b85c4, 0xc439a440c43ecc2, 0x210058c17328870, 0x609997399443cc4, 0x1cc431072194437]
def page2 : List Nat := [0xe19481a85cf9a44, 0xe107e20fe65f0c3, 0xd50c8234445d887, 0x4326463c111b421, 0x21f083f997e32fc, 0x63f8c3e98ff21fc, 0xff483f987f10f8, 0x1a5000015800000, 0xc75000130000078, 0x1ea51b6d6c6da22, 0x8098d8d11858d1, 0x1748018d7122217, 0x63386888569246, 0x9a0215a4818dca0, 0xd7a12633c68884f, 0x86c98061768098, 0x49984e9a0215a48, 0x80000000500135a, 0xc3e087c3143500e, 0xc3e887d31fc21f0, 0x43f187f30fe63f4, 0x2001c0dfc63fc, 0x800304c09000170, 0xb5923491000000a]
def page3 : List Nat := [0x153c81138813c0d, 0x10a0a9e2091c214, 0x2460844d4d14080, 0x48c21442168a10, 0xc19062911821435, 0x60860d0c4048421, 0x8c2144306279260, 0x304200000307544, 0x31d0d210874c4f0, 0x4023843108513c8, 0x3043250f208834c, 0x26d0d2008320812, 0x123443808720c4, 0x38428d01210866d, 0x30c43238432c432, 0x82230432c8123c4, 0x14426d0d100432c, 0x38c4123842cc132, 0x931308664d30304, 0x108781012108694, 0x2c50f108438d012, 0x83138829c921044, 0x14434c43238430c, 0x3288730487188f2]
def page4 : List Nat := [0x8f030832c831388, 0x1483450f108432c, 0x65cd321442ac122, 0xd200829d012108, 0x3082a90021c823d, 0x71c4323842cc530, 0x8730486ad012108, 0x38423493030434c, 0x3108523c438c432, 0xd10042a50f2088, 0xc425c52230425d, 0x63c9303042c4532, 0x1230425d0d2108, 0x1086c90021c4261, 0x6cd01210863d0d2, 0x83138829d0d2108, 0x30429c52204831c, 0x2c45020042ac930, 0x81138831cc62148, 0x3883148c214438c, 0x74c83138838c831, 0xfa126e403d015, 0x46806f062cf1e, 0xbe0089de20006f0]
def page5 : List Nat := [0x114d9800040002, 0x8001b4d8053ac00, 0x17000003bae03c, 0x6c809200004d200, 0xd90621b484210ed, 0x20b66090fb20883, 0x23083d98243bc8c, 0x37c8c21b846885f, 0x6885d2384329084, 0x710241b48e10be4, 0x10e621085513883, 0x23843b90e21708e, 0x17c0c10e843885f, 0x6084d23842791c2, 0xe11e21b08720be2, 0x10e842885f30486, 0x23086e91c43dc85, 0x1748e20d842906f, 0x610f710842f89e4, 0xa88021dc4e20ee2, 0x10dc43905f23c43, 0x3886e89e41788d, 0x174c021be0790df, 0x7085f03882e89c2]
def page6 : List Nat := [0xd884217c4e20be0, 0x21be26105d13883, 0x20c43690041b885, 0x1788f10b8629078, 0x90fb03043b0822, 0xa90843dc8621b86, 0x20ba46887513883, 0x3083790441e480, 0x37c4e21bc47085f, 0x7085830486e81c4, 0xe91821b88520de4, 0x20f040085713882, 0x20482e81e43ac82, 0x17c8c10f06090fb, 0x610f910042f98a4, 0xe91e21708c10be2, 0x10f606105e30086, 0x20043790c43dc4c, 0x1dc8521ba26107b, 0x1597b10442f1182, 0x51704038f1eaf1, 0xd31060003004782, 0x153c854404034, 0x8995a8039060404]
def page7 : List Nat := [0xfe41f087841f880, 0x87a41e10fe43e90, 0x3bfc41f10fa21e0, 0x3f9403136a07ac1, 0x45cc3fd3d3d3d3d, 0x50087894852645b, 0x400c2d8e09434c5, 0x400c32645d76d0e, 0x15cca665e343086, 0x4308754c237350b, 0x310868be1543588, 0x25c425c56307d0d, 0x258c35849d170c1, 0x50087d04c721cc1, 0x304824ee1d4310d, 0x400c29cd6343458, 0x2510266de343486, 0x400c343d0e37485, 0x2590e36de363485, 0x400c30ed9d07d0d, 0x3548746d0d75086, 0x219031659d07d0c, 0x15ccb26d1c704d8, 0x50087544237350b]
def page8 : List Nat := [0x21503c4d0e434c5, 0x150c35149e17d4f, 0x400c28dd2026d95, 0x31086a68a176d0e, 0x308c2c55634390d, 0x25103544c575c87, 0x430864b21d43485, 0x500868b56343588, 0x400c34a50d7210d, 0x400c326c9d76d0e, 0x50086b4e0527d8d, 0x359069cda3434c5, 0x500869c46362d81, 0x2590ed8608434c5, 0x30c434ac9d07d0d, 0x8c1a748e171108, 0x18c2801ac085444, 0xd14cc1028000604, 0xeaa955555555554, 0xf6ea90e61181fff, 0x218f50d6508440a, 0x424823fabec6a12, 0x10c801865f630d5, 0xdd932d1730af2ea]
def page9 : List Nat := [0x2ae3828c9a8434f, 0x2886f3434583048, 0x210c21aeeafa1c6, 0xb06a90a41ab50d6, 0x54534c7215032f1, 0x43aba2e136a6a07, 0x108615d5c725c57, 0xd0e310c35d83e8c, 0xea68b664a05d517, 0x14fdc536d1730cb, 0x882dc23a64a006, 0x322a184fb764873, 0x5c604d442b6e8e1, 0x1fa1aad908815dc, 0x10e5f67d4d21503, 0x10c21a7e0f21e8a, 0xa6c10881abd0d62, 0xf57d8d414834fa1, 0x1ab60fa326a10c7, 0x1a852fdd94310c2, 0x5a321031fab20da, 0x4d0b6a6a047f754, 0x9e49906d4d42cba, 0xc29f3866da2843]
def page10 : List Nat := [0x687207642649515, 0xb6541743d722c83, 0xd83e87a8a419e09, 0x67426d95150c2b, 0xf21c7a86ab6422, 0xad908618fd0d569, 0x3748745cc33a98a, 0xe72433068b9853e, 0xc61d6ccb604d641, 0x525102b68bc6492, 0xa992622056e3748, 0x75c726d4d40abee, 0xc336236a4992635, 0x6210cdf67d0d218, 0x25c1743aeeeaa1a, 0xa1e43200615edc5, 0x63f6311542483cd, 0x21af2eb90e6118, 0x721843dc10d3154, 0x149b05d0e9eabe8, 0xbe87ab66498d7b7, 0x613e49f6350030c, 0x219027db3c64a00, 0x8aa0ba1cbd67d0c]
def page11 : List Nat := [0xd0e4354021af44e, 0x7b5a166092c61ce, 0xb186f116c1b4388, 0x354432ed0859824, 0xb8839a8415e41f4, 0x7f670d542486ae9, 0x40ee20fa1a2b994, 0x992811f55e36484, 0x181430875c230c0, 0x8e0a1e8a10c7d57, 0x3cb50d2149440a7, 0x2487b8a1a62a804, 0xb68b9853f57d0d4, 0x87654c030e3a629, 0xac83e861aa439e4, 0xa06b916c1b4350b, 0x88110c3ea7a3064, 0x8c09a8435ed5f43, 0xb5051a504caafa3, 0x1cbc4c8b6a6a063, 0xa86153dc9464d42, 0xc125c42ba93eca8, 0xea9b68488769270, 0x5ddc526d4d408f8]
def page12 : List Nat := [0x1032e21eca90861, 0xa8510d6d178c925, 0xe36485409f60fb1, 0x6236ca990651fd5, 0x53f714cb45cc33, 0x9630eb6e098e6a2, 0xda1c815b5c4424, 0x47d8115ccb5c932, 0xa7acf90e8b98577, 0xe434e41f4591532, 0xf35087749320da1, 0xe1824b8875907d0, 0x6cc8604d641ee22, 0x33cab20da1863d, 0x849063d16597439, 0x46c57328fece1aa, 0xb9a841aa219d595, 0xe7b62d8135906af, 0xc21e5a4fa1a4b21, 0xd21a639e9c156d0, 0x70d5414834fa1a4, 0xf0ac30262a047f6, 0x87ce11d06d4d42c, 0x400c2bd13a2d82e]
def page13 : List Nat := [0xa1aa010cf976c86, 0xd5926d0d42ad6e4, 0x6bc93e2b82e878f, 0x390e3c451814248, 0x5c1743f2e8721a6, 0xb20da1c435e5c72, 0x577149b53503788, 0x21a7ee498e8b987, 0x10c618f50d6510c, 0xd9541cc33d382ca, 0x486996a098e3f42, 0x15d55f434c721eb, 0x10c2baabe4c8a86, 0x124b184dd578d92, 0x1d56d0c10e5e87a, 0xb883e868a8619e4, 0x8855d37087450c3, 0xcd440af2af19061, 0xe8690c81574de21, 0x907d0f524c65fb3, 0xab8ae99262a057, 0x2e614f4df215173, 0x745cc38e99262a, 0xfa1ea29953f725]
def page14 : List Nat := [0x1fdd56110830af2, 0x502ba9be858a861, 0x22b9955f7158853, 0xc624d710e6e87a1, 0xc22a8c282634f51, 0x871f438d5424879, 0xc30cb886b28421, 0xc09a843b645906d, 0x630d5414832fa30, 0xed2439824b1865f, 0xc814f4dc4550920, 0x945cc33a98acb90, 0xc836861953d178c, 0xed59260c120cf2a, 0x29e9b88aa12439, 0x8b984bf67d0d211, 0x6d4d42a7c6e90a, 0xabe0d21a439ec5b, 0xe3f4359443c863f, 0xc21cf6ac8368690, 0xda12835e95d06d0, 0x7181434869e9bea, 0x7eeca188790c7f5, 0x61cbd0f21494409]
def page15 : List Nat := [0x359067dbb243200, 0xa1a410867b62181, 0xdd94310d219f6cf, 0xb1fa12ada08612f, 0x38857907d0d15cc, 0x349631aeeeaa126, 0x9a859ae215ec1f4, 0x78754c430482afb, 0x31dd6429360a185, 0x18441ce50f42d41, 0xd0d31086ed1ba42, 0xa2f9368b9857557, 0x17641f434cb31a7, 0x2482f8b88841862, 0x1a641847f678d54, 0xd5434c710abaafa, 0x3c8b60da9a855dd, 0xa053f470c935907, 0x8640cb8ac99262, 0x20da1c87a7d0d36, 0xd7610e354875c8b, 0xe6a6390a8b9865, 0xa8615d55e31c843, 0x5705d0f9ba188c8]
def page16 : List Nat := [0xae99662a057a274, 0x5ddd5424c431ab8, 0xd02ba93e868a861, 0xa0ba1c7f7648735, 0x53251730cf44db2, 0xfb388a992414fdc, 0x76b21cc1258c23, 0x4131cb8a7b1262a, 0x87a82635ed5c43d, 0x75119210c2bdb92, 0xc7c8ba36a09947d, 0x2415745e6214d40, 0x745cc3b82ba2c18, 0xf1968b9847f7648, 0xa8992541743a7ac, 0x42ba3aa8518a21d, 0x8490e792659430c, 0x16cc941e3e871ae, 0x90a4d828619dd5b, 0xee926c1b4348774, 0x510cf28dab0a098, 0xda1c435d1d5438c, 0x2c9b45cc33c832a, 0x7eeaa188610f2d3]
def page17 : List Nat := [0x616d11d2645430a, 0x45cc27cbb643828, 0xa9a42a063d2645b, 0x4c56508640e9a4f, 0x6baabe8498e219d, 0x2206e726c5b4348, 0x4c71097eeca184, 0x1eca90861bc1186, 0x7b57d0c304832fa, 0x32e5e86a124b98d, 0x10881cdd1b45c57, 0x4db414825eb3e86, 0xe87b2a859847c75, 0x14f8dd26d1730c7, 0x54423e3aac421a2, 0x368721f1f4350a3, 0x9f2150030e76ea8, 0xcda1a43200613ed, 0x904f8674c5400c3, 0xc310ce88a8b664, 0xeca90c615e55f42, 0xd27d4f215032fa1, 0xcb88d1aa6490f4, 0xae65cb48726d173]
def page18 : List Nat := [0xd8219039ba1c8c8, 0x4a9362a186d8704, 0xdc41f43c5430ece, 0x869eabe8c21843, 0xa0b195e77250d31, 0xf6350b10ad6e4a1, 0xe382869a8431f55, 0x8e575345b32502a, 0xc030e7686a16a09, 0x8c8ae659ec87654, 0x16c1b434879ba18, 0xeae869922a186f1, 0xe659e05b6541743, 0x932043b883e878a, 0xd92e2b1847d7511, 0x54c421cd440cda4, 0x23f3b08a90a61d, 0x6a2047c5745a325, 0x6d0d21cbeec98e, 0x93ec6a0061bc459, 0xd77478d9150c36c, 0x430cf2e0ab68610, 0xa82e876dd1c2145, 0x3584325033d0b6c]
def page19 : List Nat := [0x788d22aa29965f5, 0x815e89d650c310c, 0x15ccaafb8a659a8, 0xb1a8418f3543d09, 0xd0d6210e21db60f, 0x6ad83e871aa43ab, 0x490f974390d3108, 0x6c17438fece22a6, 0xba0da1a855e49f1, 0x787050d25c439c2, 0x30ee02c8aa0ba1d, 0xa1a43d94c721496, 0x18135907729322d, 0xead8b686a167862, 0x197d8c3550921c7, 0x1442bba3a648a86, 0x368721d7757d0a3, 0xd91541743d764c8, 0xba3b24a8a861d68, 0x205da37485400c2, 0x4c030aba6f90e6a, 0xe85a92639ed0b65, 0xd265974390f97a1, 0xe720fa1a4b21e3]
def page20 : List Nat := [0x2e21bc499160c31, 0x5b43c87b5938609, 0xcab68790e79065, 0xd94c72149440cf6, 0x482baabe8498863, 0x22a1847d7611732, 0xf6350831bac6e93, 0xba1a848ae65b641, 0x865f46d5b324c79, 0x1730bac6e9362a1, 0x859ae214fdd931d, 0x75d0b308c38fa1a, 0xeb2e1a366a10d79, 0xe615ddd5434c721, 0x7351029e8bc85a2, 0xfb1a8490c7d7608, 0xa09925417439f60, 0x2ae9be859a821d, 0x421865d32d5b315, 0x26d1730cf4e0b28, 0xb3e8610c61cbc85, 0x63f43597428c66e, 0x440a7c6e8b68b98, 0xda1a8557dc5324d]
def page21 : List Nat := [0x3d0b15ccad713a2, 0xcac4b088610f354, 0x658f18c4550921d, 0x32502bc83e868ac, 0x836871865f53d85, 0xdd921c1430db22c, 0x23e2bac2192813e, 0x498d5d370873510, 0x6c8540e5a87a16a, 0xba439ae819714d3, 0x7f754db42042af1, 0x409baec21842184, 0x9ae8157dc96114d, 0x55b438863e33a42, 0x8eaa1e8490e7b06, 0x1cd48516d1730a7, 0x54432eb3ea790a8, 0x1e840871f435083, 0xc926d1710a7aafa, 0x971924da2e619b8, 0x10c7d67cc845443, 0x4d641abe0f21a6a, 0xa6c108815d45f32, 0x537099150c34ea3]
def page22 : List Nat := [0x1cb88db2a6598dd, 0x2a211f5d845cc92, 0x9b5350396a1e851, 0xfa1a6a10d57714, 0x579c0438d521abe, 0x4c69eb908aa1a63, 0x8421857927d0c50, 0x5268c440cea62b2, 0xab8e4b8ac611fdd, 0x871f430d742486b, 0x8440aeeea9362a1, 0x8692c871fdd5360, 0x43d9542c431fb3e, 0xf368710c801863f, 0xe87d545c604d421, 0x5320cabc8be4d82, 0x71aa849066e46d9, 0x68d92541743e3e8, 0x86bd83c868ae41d, 0x8b9855e7010d350, 0x324cb41a7ee2a16, 0x23aa2282655b55f, 0x47d76117314829e, 0x710aba6f2166b88]
def page23 : List Nat := [0x39ac415d45f32d1, 0x7d0b30042ae9b88, 0xfeeca106a885795, 0x815755f434c4308, 0x428c23e2ba6d90a, 0x1962a1863f43597, 0xd0d2149440aee8f, 0x23fbb26422a21cb, 0xb1857b07d0d15c8, 0x308430ad88e90a4, 0x9263a2e613759f4, 0x74754ca314438e9, 0x208feea9b642205, 0x92c63768dd210c1, 0x55a320c797a1a84, 0xecf1aa8490e5f43, 0x35d11d32c54308f, 0x2c4356a1ac421c4, 0x1a2b1947f754d84, 0x1f434d421ada4fa, 0xed1ba432006156c, 0x9947f7558442cc2, 0x1043087eeca288a, 0xa6492c61378dd26]
def page24 : List Nat := [0x626495150c2b623, 0xdd64c8368690f6, 0x2e614f45e32d173, 0xcb458c69e9be43a, 0x871b22a1857517c, 0x3ddd942cc631eae, 0x106bd83c65a2c63, 0x831857517cc935, 0xb324c5408feea93, 0xf13acba1c819715, 0x865d67d0c354869, 0x420f362fa1c801, 0xda1a851fdd5361, 0x7d8d42ccb1dab2, 0xcde4a9362a186db, 0x8615e49f43d4131, 0x9215032fa1aca10, 0xc98a4a2065c538d, 0xed0f42141318f8e, 0xc33db386092e21c, 0x2b994f976087050, 0x2611510e6a86232, 0x8bca5288878f50d, 0xd3c7550c43486ba]
def page25 : List Nat := [0xa41cbc6b8366490, 0x2184413bdd9320c, 0x790f504c67dbb24, 0xb886b2843185792, 0x634fdd543d0b10c, 0x251071fa1ecaa14, 0x90e6b2057b078d9, 0x19743509318fcce, 0x72fbaa6c10c818f, 0xa1853d57d0f420c, 0x6d1730e6e87a122, 0x1aca21843cd4c51, 0x2d2149b45cc31fa, 0x108f8eca126b887, 0xa80435d1d5434c5, 0x90d31c87b9a1a62, 0xecfa9a42a04f767, 0x33e19d21500308f, 0x50c2bda3eac2826, 0xaa8490d79750870, 0xc926d1730e3e861, 0x9fabe8721a43cb4, 0x10c7d67d14504ca, 0xc8630a78e09b68a]
def page26 : List Nat := [0xa6c108819d4c565, 0xf4350935c432fba, 0x1a78eaa1e849071, 0x8619711a604d42, 0xb15cca6f3b0869, 0xea9b6858873743d, 0x1fdd9428d5108fe, 0x483789322c18241, 0x6649947f6711531, 0x9568c841ce88b8b, 0x71924da2e619bcc, 0x873a45d1b504c73, 0x1730aea6e2322a1, 0xda18614fdc9315, 0x43d5b424c6ed13a, 0xaf2ea216611863f, 0xe659710f6548630, 0xe50086ba9be858a, 0xa9b68418e7967d0, 0x7d4d168c9408fee, 0xa6ebb08610c619, 0x62a067926c1b535, 0x4389510cbea6936, 0x3b0a690a815ec1f]
def page27 : List Nat := [0x63f4355a430863f, 0x4308feea9b48588, 0x3a82655dd9f4345, 0x789b535029f23aa, 0xbce02326a10d5d1, 0x61cdd0d42c5732a, 0x25c436db1a42a00, 0x9b0840857b07d0d, 0x59c21cd6408feea, 0x3b921a62a80431f, 0x4a047f754da2110, 0x245732cb8a7b0a6, 0xba43a2c615ddcd4, 0xe926c1b43c86af1, 0x32a7ee29368b986, 0x82e87cd51b45c57, 0xc1b43086bcb8e4a, 0x68610c801847957, 0x11f55f464c830f3, 0x50426f1bac22106, 0xc801847f67d0d2, 0x1921cd620bb26e1, 0x1f932cba1c818fd, 0x9963e45d1b504c7]
def page28 : List Nat := [0xd0d21adee4a2ea0, 0xe8799263bac9b06, 0x9065974390eec83, 0x1c388da9a64a063, 0x8a657cc1f434c72, 0x5b535033d22ec0a, 0xec21a431855d278, 0x9d4c556c84409bc, 0x8ca9eabe87a1061, 0x6a8866f7549b43, 0xe604d421aba6fa1, 0xfa34439ac4157d1, 0x53d75d0b418c31, 0x921d3e8e9b0432, 0x6390a814fd5f43d, 0x7110b35c42ba2ba, 0xaba6e10e6b20575, 0x8819b49b25c5743, 0x7458c2afb92629a, 0xf99262a055d3708, 0xec1f4345632abea, 0xcb3c832ada1e655, 0xa2996d907d8d42c, 0x3648640af60fa1e]
def page29 : List Nat := [0xabe8c98861a7d0e, 0xc7b67d0d500863e, 0x440a7eeaa1e8418, 0xa988819d4c56508, 0x755b430873d03ec, 0xbe0f2326a10e3f4, 0x87bcc5b06d0d21a, 0x354871f8b2cba1c, 0x29e42a053c4741a, 0xdd94511532eaae2, 0xb3a98aca10c614f, 0xa2047b76540504c, 0x350920eaa6390a6, 0xa8c0992434fd5f4, 0x3e2745b45cc32f1, 0x30fa26390e61185, 0xa9a81b6c9f63500, 0xd95150c2af13a2d, 0x22c83686a167726, 0x19749916d4d40d7, 0x5cc3372124d9ae2, 0xe6b2053f724db4, 0x8e3550921abc6e9, 0xcc93e8720061971]
def page30 : List Nat := [0x21c7f6710935c43, 0x45420e5e4fa1a4b, 0xc849ae211fd9f43, 0xf07d0e354863fb3, 0x1af08e990a098d5, 0xae657c41f434c72, 0x9b45cc2ba9be848, 0xec10c801863d364, 0x97cc936115109f2, 0x432e29a2d19281, 0xa63885797510b30, 0xd3245430aeaafa1, 0xda3843200615d11, 0xf5531c8735102d, 0xc310a7c8e8346a9, 0x8c282635e55f430, 0x17d0e400c39c22e, 0xcea85b2a6218f99, 0xe214fdd921d1730, 0x7308c3ac2186092, 0x6b28431857975d0, 0xf55f4350b10cbe8, 0xc27ab3e8598c634, 0x60085b847486400]
def page31 : List Nat := [0x21cd440bb26e216, 0xbb28621c431fdd9, 0x69f438d9211025f, 0x743a7eeaa168398, 0xda1861dc8591541, 0x54db414836c9320, 0xde8f1924b1865c3, 0x818fd1d6510c21a, 0x35c425e9b88c90c, 0xa168b8867b620c1, 0xdd932cd440a7ee6, 0x2ba9b8858a86197, 0xb98d5d3710b3504, 0x2c5732af20fa1a4, 0xaa4da1a2155dcd4, 0x6e5249a5110e3e3, 0x31a7e8e3126b886, 0x9a8815ec1f43d49, 0x58453502afb9263, 0x2639824b1865d62, 0x5c7d0c3550920eb, 0x350b3c228c0a8a6, 0x8e42a06791641b5, 0x1f464d421eaea69]
def page32 : List Nat := [0xaca1e65a826357c, 0x185bb47087050c3, 0xcd710db22fb1a80, 0x687200611f5d842, 0x531085351034cbb, 0x19ec6eb08858875, 0x92839dd0b654c43, 0xb35c43362b6649, 0xce21a6390c7d679, 0x1fdd526104309ee, 0xc2afb8a4da9a81, 0xe6b1069b4349a40, 0x525417438face20, 0xcb386092e215edc, 0x971d324db45cc33, 0x4021cdeca30a641, 0x6092e215a5c8435, 0x57d0d31443ada18, 0xcf683b2a6018577, 0xe433bdd9320c841, 0xd50086f293e8698, 0xc29a42a07394310, 0x51c526d4d40cbce, 0x2e693e8719061d]
def page33 : List Nat := [0x6490f5617d4f215, 0x42c5732cb88c1aa, 0xa1e42928815ddcd, 0xc7d75119218c396, 0x30a7eafa308690, 0xda1841e6c9f4390, 0x6c1b434873c83aa, 0xfeeca166b8867b5, 0x2137d9f43484308, 0x15ccabbbaa6498e, 0xa366490d7747d95, 0xd0d6508440cbc6b, 0x23fb3c8aa82658f, 0x420d7537d09150c, 0x5c5430adeea9906, 0xba43a28615d45f2, 0x795641b43086af1, 0x32ae20fa1a2b996, 0x988819d11516cc9, 0xc8745cc32e996ca, 0xe8632a848873531, 0x15e5c843d4131c7, 0x28c32e8b2ada186, 0x14628847f755844]
def page34 : List Nat := [0x1956d0f31baee6a, 0xbcba884186219e4, 0x10e3f265974390e, 0xcc520cf2ad83686, 0xe8512a21574dc45, 0xf53d8931502b69b, 0xcbaec29e42a065, 0xa41a750d360844, 0x8935c423fb3c6aa, 0x87a162a1866c42d, 0x574dc42cd710e6e, 0x87a793ea690a81, 0x88790c7d57c1a43, 0xf410c120c7a86b2, 0xebb0859a8215ed5, 0x84fb76484304823, 0x1431e76433068b9, 0x2d992639b8c926d, 0x7d0e31c876ba36, 0xbe60fa1a6210df3, 0xc8797118604d421, 0xd211031e8b2cba1, 0x5b2a60184bc7650, 0xa49906d0d21cf08]
def page35 : List Nat := [0x872e932ada1861b, 0x80185e57210d310, 0x3608440db6c790a, 0xbb0839a841a7d1d, 0xf57438cb150c23e, 0x430af6af21ea098, 0xda1c615ddd52645, 0x7c9b45cc36c9320, 0x7e0f2188a90d3d3, 0x5cc514010010b6a, 0x98a500226084c05, 0x502c0002, 0x501801c3788708a, 0x700031f0203b00, 0x81ac97c00032240, 0x20040100582800, 0xc080c300c000020, 0x7fa060f980c04, 0x30b874000060960, 0x54068040181a807, 0x319014359c7a5b0, 0x80e02600434000, 0xe0a6c0000c4220, 0x88fe0002704a]
def page36 : List Nat := [0x7fc0030101c6c80, 0x400800019002001, 0x182740e01102706, 0xc0202a006001118, 0xd00180800100001, 0x30160197d4460, 0xb40c04200400c00, 0x40201d8034b74, 0x182308002c08000, 0x106b83002a04c0, 0xa0022b00e46600e, 0x1281652120e0000, 0x20001518181c174, 0x30a40702201b08, 0x6ba42e3b7000614, 0x100000402a4a, 0x803030000050070, 0x280000100602401, 0x40e40309702c0, 0x300b33700004437, 0x1800102000405c0, 0x51db030304000c0, 0x260022272500881, 0xa21c29000014000]
def page37 : List Nat := [0x22a2e0281088180, 0x82800d0140e80c1, 0x430202181500230, 0xc1906a0900085c1, 0x10018248121d8f7, 0x1c00090c100880, 0xf03000401816, 0x12982c0000c11c0, 0xdc0000b801004, 0x8000000000, 0x1000000, 0x20000000000180, 0x2800000000, 0x300000, 0x4000000000038, 0x500000000, 0x58000, 0x680000000006, 0x70000000, 0x800000000007800, 0xa0000000000, 0xb000000, 0xc0000000000b80, 0xc800000000]
def page38 : List Nat := [0xd00000, 0xe0000000000d8, 0xe80000000, 0x8000000000f0000, 0x100000000000f, 0x110000000, 0x4087800, 0xc0820000000c08, 0xc083000000, 0x880000000c08400, 0xc8830000000c0, 0x1088380000, 0x8000000010c820, 0x4808700000048, 0x800000480878000, 0xc4810000004c080, 0x4c4818000004, 0x78000004c482800, 0x508838000005008, 0x88080800000, 0x800000008808700, 0x8c0838000008c0, 0x8c48280000, 0x8860000008c8838]
def page39 : List Nat := [0x900878000008c, 0x90c820000, 0xc082000000cc080, 0xcc083000000c, 0x7000000d0481000, 0xd0c82000000d088, 0xd0c82800000, 0x84000000d0c8380, 0xd0c86800000d0c, 0x400c10100000, 0x1008000c0041010, 0xc0d0d000000c04c, 0x8000c0d0d020000, 0x41028000d448500, 0x114485008001144, 0x8001144c502800, 0x4c5010001404c50, 0x14c50101000140, 0x280014c5010200, 0x4d0d0000014c501, 0x414d0d0100041, 0xd02800414d0d020, 0x40cc100800414d0, 0x4540c1008004]
def page40 : List Nat := [0xc1030004540c101, 0x4540c1040004540, 0x1800454cc900800, 0x50d01800454cc90, 0x4c48c5018004c4, 0x30004c490d0180, 0x84c5018004c4cc1, 0x4c8cc1030004c, 0x5018004d4085008, 0xd4085030004d408, 0x4d4101010004, 0xc5018004d4c8100, 0x5140c90180050c4, 0x1000514cc101000, 0x10901800540d0d0, 0x54810d02000544, 0x180054c0850080, 0x850180054c085, 0x8c00c10000055, 0xd028008c0481000, 0xd4485008008c4d0, 0x800904d0d010008, 0xd010009144c901, 0x94810d02000940d]
def page41 : List Nat := [0x2000c14d0d01000, 0xd0d02800c14d0d0, 0xc400c101000c14, 0x2800c540c10080, 0x40c103000c540c1, 0xc54cc900000c5, 0x901800c54cc9008, 0x804c100800c54cc, 0xc80cc100800c, 0xc100800cc004101, 0xcc08c100800cc04, 0x3000cc0cc503000, 0xcc103000cc4cc10, 0xcd408500800cc8, 0x1800cd41010100, 0xc0c102000cd4109, 0xd140c901800d0, 0x100000d14c81000, 0x14cc101000d14cc, 0x800d14cc102000d, 0xd01800d14cc102, 0xd4850d02000d485, 0x2000d4c50101000, 0x50900000d4c5010]
def page42 : List Nat := [0xd4c50902000d4c, 0x1800d504c90180, 0xc0850300154c085, 0x2d44cc90180154, 0x458cc8cc1830, 0x10080301004000, 0x10080401c0e0603, 0xb05828120904824, 0x381a0b0582c160, 0x28140984c240e07, 0xa0d06030160b050, 0x8783c1d0d86c341, 0x40200f87c3e1f0f, 0x8130984a2311888, 0xb0562b158a8542, 0x622f168b45a2d16, 0x61a0d06633198c8, 0x8ec743a1c0dc6c3, 0x8240201007a3d1e, 0x42190c864221104, 0x1148a4422110884, 0x964924120904723, 0x2793c9c4c26130, 0x950a65329144a25]
def page43 : List Nat := [0xb2582b958ac552a, 0xd2e16cb45a2d168, 0x990c86331184bc5, 0xd0673399ccc6632, 0xd361acd469341a0, 0x9c4e270379bcdc6, 0xe673399cce47238, 0x63b1d8ea73399cc, 0x1e0f0783c1d8ec7, 0xfc7e3f1f4f6793c, 0x843a190c8541a04, 0xa3d1c8c45a25108, 0x249249249229047, 0x74b2592a954a251, 0x26d349a4ca5d2e9, 0x3e9f4f2793c9d4e, 0x451a8d46a350a81, 0x2a150a7532954aa, 0x52a8542a150a854, 0xe562b158aa552a9, 0xac160af57abd5ca, 0x66b2592c562b158, 0x95c2d96cb55a2d1, 0xafd7cbd5dae972b]
def page44 : List Nat := [0x84c160b0582bf5f, 0x8643218ec662311, 0xb2590c86432190c, 0x98cc65b2d92c964, 0x369b4da2d068339, 0x359aad56ab51a6d, 0xaed76bb5daed66b, 0x96c361b0d76bb5d, 0x371b6db6d369b4d, 0xc4e170381c0e06f, 0x571b8dc6e371b8d, 0xb99cce673399cce, 0xd2e873b9dcee773, 0xc75badd4e974ba5, 0x3bddeed76bb5d8e, 0xe4f2793c5e2f078, 0x67b3d9ecf67abcd, 0xbe5f2f87c3e1f0f, 0xf4fa7d3e9f4fa7c, 0xc7dbedf4fa7d3e9, 0xc06030080401fef, 0xd0482412050180, 0xa8542613098441e, 0x43a1d0d86c32150]
def page45 : List Nat := [0x251288442211088, 0x48a45227128944a, 0xc5e2d168b45a291, 0x3f1e8f476391a8b, 0x90482412090482, 0x48a432090482412, 0x4f2793496492391, 0xd96cb25529944a2, 0xcc25f2f97cba5d2, 0x6532994c6633198, 0x59acd6693499cce, 0x4de6f379bcde6d3, 0x71389c4e271389c, 0xc9e4f2793a9d4e6, 0xd0a833f9fcfe7d3, 0x8b45a2d168b43a1, 0xca552a9348a3516, 0x546a14fa7d3e9d4, 0xb158ac55eaf56aa, 0xbad56ab55aad566, 0x57abb5dae56eb75, 0xc360b0582bf5eaf, 0x6b3596cb63b1d8a, 0x5aad369b45a2cf6]
def page46 : List Nat := [0xdb6bb5daed76bb5, 0x2b95c2e16fb75b6, 0x5daed76bb5d6e57, 0xf57abcde2f176bb, 0xcbe5eef57abd5ea, 0x6130781c0dfefd7, 0x1187c3e1b0d85c2, 0x9c4e271388c4623, 0x633198cc5e2f158, 0x2390c7e3b1b8cc6, 0x7cae532994c9e4b, 0x66b3198cc65f2f9, 0x3d9dcee773b9dce, 0x3d1e8b43a1d067b, 0xe9f4fa7d3e9f4ba, 0x57a9d4ea351a7d3, 0xd7ebb5dacd66af, 0x6d367b2d96c763b, 0x73b9dbed769b4da, 0xbddeef75badd6e7, 0x6ff7fbfdeef377b, 0x83c1e070381c0e0, 0x2e170b85c2e1707, 0x71389c3e170b85c]
def page47 : List Nat := [0x95c9e4f238bc4e2, 0xfe773b9dcce672b, 0x1c505732340641c, 0xac4341d0626449a, 0x1c2d2c2c3026222, 0x27434002c085e10, 0x586f044034546a7, 0x674063e262a0c22, 0x584c26e4073ab22, 0x6c25b1af28f222a, 0x21f38ac18282a2, 0x612403e2f123618, 0x3482962a06ea067, 0xc31212cee92ef28, 0xccaa5a8a2c44624, 0xc00d09ea21868c2, 0x70c518dae626ce1, 0xe2a38a21816a60a, 0x60572e06f0ee5c3, 0xb0d1e825654f486, 0xc4829d1a2a40c00, 0x6a6b0561c56d026, 0x75203ee806049a0, 0x6301a06262646a0]
def page48 : List Nat := [0x88228fce12d243, 0x4f6c32c34450a89, 0x261c5e5ab441260, 0x6a6ba1cfe0ebeae, 0x82ee011c18d2282, 0x62a2a407c7b1874, 0x1b0ee07826acaa5, 0xc2a26d81e831274, 0xc6c4161c3537244, 0x8b42b242d2b249a, 0x6e0983e9538040, 0xc4482401e2acac2, 0x844e2b24066a02b, 0x6d4e444000a2a2e, 0x2c0c9cb8aeb0620, 0xe743a0a0802da74, 0x521cc20aec904c2, 0xa962602560a1e04, 0xb0662ac4061e4c1, 0x622021882d12424, 0x4a0c04261ce2de5, 0xa068234f0b42a06, 0xa4260d1a80c2441, 0x32aee02270a5a74]
def page49 : List Nat := [0xa6eec8c220c46a8, 0xc2604e01cf00082, 0xa6645a40c8289a0, 0xf1710403502832c, 0x8c7f14443524a23, 0xb344074070e443c, 0x30a83404a002440, 0x4729d14ef1aec07, 0xb62a82351d2a367, 0x524400c34824220, 0x2b2b2a4032d63, 0xc140640ee403407, 0x213ab418a2e4e8d, 0xcf92a06ee0c490f, 0x1d104482a4c46c4, 0xa6424ac62fa82c4, 0x6b10869067a8a22, 0x8510f760da1a857, 0xdf8c0a1243dfa1a, 0x3a2861aea326a10, 0x81bea1c4a886fc4, 0xa0e8b9877a4da1c, 0xb90cfeada1a219e, 0x7e86a1243bfb026]
def page50 : List Nat := [0x90c61bfb2a65987, 0x1ba20a2a187b886, 0xe6b204fa4d9ae2, 0x18ddac421843bf1, 0xaada18613eab484, 0x8241bf18e8b106f, 0x7c83686997e22c1, 0x60907be8790861, 0x5fa4da1e61fc99, 0x8b99243afa1e6b9, 0x8817f8368610ef8, 0x918c40886da4292, 0xba1dfa2d29087f, 0x6fa65a2c21bc8ae, 0x49ac837e9b68588, 0x81bfa1a4b886fec, 0x8368710ebea6192, 0xa10efaada1863fd, 0xbc2da9a819f9b68, 0xa14633fb2a65206, 0x3beab6861077e87, 0x9061887ba8d9926, 0x10ff60da1843fd1, 0xaad90861dfa1c86]
def page51 : List Nat := [0xa8613eb2e6520df, 0x7e8b484986fe4b8, 0x8821877a87a1663, 0xefec49ae213eb2, 0x2b82e877a8b6642, 0xc617e934a221efa, 0xeab686105fe8d90, 0x8518e7acba1c873, 0xdfcc021a43dea1e, 0xda9a81eea1e6498, 0x817e3028610efe4, 0x8368a996feca996, 0xb107f262a00617d, 0xfaca210613f1b22, 0x92821fdb0263204, 0x17e9b684086f88c, 0xb085985fe8c1086, 0x107da64190836e9, 0xaada16213eab687, 0x1663fba126218cf, 0x7c93480185fa6da, 0x22a184fac422a61, 0x7e88718e43fa93, 0xad908617d836649]
def page52 : List Nat := [0x61bfb126a20cfa, 0xe9b08a887f44320, 0x8798ef8c0928833, 0x6f8649ac837c836, 0x7a8263bfa1a4a08, 0x21bfab664a0ef28, 0x9b683986f0609ae, 0x1885f0c0992417e, 0xfa6c10881f88b06, 0x19681be98e8b185, 0x53e9366a085fac2, 0x1282986fa8ba826, 0x9973e87a10617fb, 0xeada1221bda84a0, 0xac816f1b242184f, 0xbba122b996fe439, 0x462187f44218441, 0x84fc6c92e81ef19, 0xa3a82657f1322b1, 0x2636e9b084986fe, 0xe9968b987a8c299, 0x8790dfec6a1665b, 0xc7e8d9ac41fab08, 0x692e61bd8b60ba1]
def page53 : List Nat := [0x613fb2a8610efa8, 0x8b060905fa2d192, 0xb207b20da1861f9, 0xf88a28263be90a6, 0x99421afa186a906, 0x3ee3026498dfe8c, 0x2a0ba1ef086a804, 0x206788aa1241be9, 0xa8718a21bf10a6a, 0x12419ea1aa421fe, 0xfba1a62886fc6ba, 0xa0b194faad99621, 0xfe88698e43bc21, 0x6da10617f1b20ba, 0x6655fb2a87a15fa, 0xd1320ba1dbec6a1, 0x4a085fa2d19281f, 0x7b88690861bd982, 0xda1c437a8b66499, 0x81fc8368618ff20, 0x8b465185ea2d996, 0x2a06f8429a8817e, 0xf88a99241be29a4, 0x98e217e9b68418e]
def page54 : List Nat := [0x17e93463207e88c, 0x108698ebe879ae2, 0x887f60da1e437eb, 0xaca10881bfa126b, 0x16217f8368510cf, 0xae21a6b8877e86a, 0x26ba05fa6c20c41, 0x6f685a82633fb1, 0xa498a81bfa126b1, 0xe81bf18e8a186fe, 0xea1e8b90efa6292, 0x6598efa8692c639, 0x4fec49a883afb2a, 0xc92821fdb026218, 0x63baa122b994fc6, 0xa34a0995f20da1a, 0x2994f0c09ac835f, 0xfaca21e435e232a, 0xa1a857fa3464186, 0x5be90a6b1067ead, 0x2a63207f20da186, 0xa06ba649ac833fb, 0xc8aa8265be2b264, 0x16213eb2885986f]
def page55 : List Nat := [0xbba162a184faca2, 0x24b186fa65a2c63, 0xefeca98881b7a1, 0x2d19081f7310871, 0x8813fab464a05fa, 0xe32a84996ba629a, 0x87186f8829ac413, 0x5f88c99443ee8b6, 0x2a00613e9b08a90, 0x61dfa1c8710ff64, 0x8368690df88c988, 0xa086f88a28a657f, 0xfac392e87bfa166, 0xa8a859eb2e87205, 0x13e936a6a04fa6d, 0x3687184faada1e4, 0x986be871aa41ec8, 0xaad90e613e9368b, 0xa81be21a4b884f, 0xea99263884fead9, 0x26b885fc2c82e87, 0x84facba0c61ae99, 0x65a2e61efa1c431, 0xe617fab08698e7c]
def page56 : List Nat := [0xfb026b216fa43a2, 0x6b216fa63a2e61b, 0x5f88c99263be30a, 0x7a16639ea1a4a20, 0x417fb2a421877e8, 0x18a2a205fec6a0a, 0x4997ea438a861bb, 0xf243828616e31a8, 0x280877eb0885987, 0x1eea1a63984fa4d, 0x94a221ff0c098e8, 0x216fe0d1aa43bf2, 0xaad18c41be3026a, 0x2e877e1b20ba0cf, 0xbfb2a64206f64b8, 0x68b18f7e8c21c43, 0x6fe43a2e613eb1, 0x8710c81bfb2a63a, 0x443be3026a10f7e, 0xe232421877e87a1, 0x8418dfe8d190217, 0x4fead98a81dfa1a, 0xd21a633eab68398, 0x857fb1287985fea]
def page57 : List Nat := [0xb2c6520ef8c29ae, 0x905f60da1a633e, 0xf60da1a41bdab06, 0xa0e61bc836a6a15, 0x5be9346a9077e84, 0xb20ba1efc87a8a6, 0x20d7e8c10c61fc0, 0x887a8a413eab464, 0x2e21fba1263886f, 0x3e9b68b904fa6c9, 0x487906ba2da9a81, 0x5f88c98c617d83, 0x87a12633e9b24b2, 0x63ae29a64a077a, 0xd996a098f7a87a1, 0x42207b08618621b, 0x7f264186217e9b6, 0xda2e43bf1b24a08, 0x619fa126ba0cfa6, 0x98e61185fe8d108, 0x185fe8d99265ec, 0xfa6da1665fc90c8, 0x9a8433fb2a85985, 0x37f3008710eba86]
def page58 : List Nat := [0x3642186be879a84, 0x985facb10c617fa, 0xea7a12837fb1286, 0xac813e9b24a20e7, 0x3a32a62884fc6c8, 0x243985fec2a9087, 0x85be6da12657f1b, 0x868a8413f328868, 0xa41be936a6a0efe, 0xe93687086f86ba0, 0x8690ef60da9a857, 0x4faca21063fc836, 0xd99265ae136a6a0, 0x65baa162b995ee2, 0x9362a184deca990, 0xb885fe8c28263fa, 0xf68498061bea126, 0x82e873f1b22a207, 0x176b108710fb46c, 0xe4b186fc429ac8, 0x986fe87a8a41f69, 0xc6b992437e93686, 0x28633fab682906b, 0xee21c6518cfa4da]
def page59 : List Nat := [0x60ba0eec658a861, 0xdf60da18433e93, 0xc099621afa1c6a9, 0xa657e8b665a05f0, 0xe90e8b984fa4da2, 0x43986ea8b8ae659, 0x6f843a2c613fb2a, 0xc19463dc83686a1, 0x87fb18e42185fe8, 0xb1087906fa4a8ae, 0x3187f2421824176, 0xda6512a217fa344, 0xa1c63fc8368790e, 0x3be22a6490dea2d, 0x1682986b8869a84, 0x10dfaad10861dea, 0xa84988637fa3665, 0x88433e9b24b20fe, 0x6e9b684997ee869, 0xa65a0efa2da9a81, 0xe7a87a2c63bfb2, 0x4d82c877e9b6851, 0x843fc83684184fa, 0xf1320ba1fea8698]
def page60 : List Nat := [0x8690efc869ae437, 0x7ea8498e217f834, 0xc99283bfa1a2b19, 0x637e9b443204fea, 0x930a0a0ff28da82, 0x490ef24b82e873e, 0xf60d19621be1ae8, 0x1aa21b69924b185, 0x13e2b264a06b887, 0x3663a06e0c08a86, 0x886fc65a2c637e9, 0xe8c10c617d83486, 0x2861ae9926a205f, 0x7fb1a83986fe43a, 0x465206788aa1a65, 0xcfa6da28437e8b, 0xcaa10637e302649, 0xe43be2324a184fe, 0xeab665a0cfaca21, 0x4b18ef8849ae213, 0x67e8b22a65bf21a, 0xd82e633e32a8488, 0x617fa34a2994fa4, 0xa88a09967a2da2e]
def page61 : List Nat := [0xb185fec299081bf, 0xfa4da1e63bfa0a4, 0x194817e9b084085, 0x19f21e8a10cfacb, 0x26ba16b8a698a8, 0x905fa6da0c41bfb, 0xc6c9288177b1286, 0x1c63dfa308610cf, 0xbfa2e2b995eec2a, 0x686185eec299463, 0x1ef2ca18621ef93, 0x6c82e85bc8aa0ba, 0x2417e9b684905fc, 0xea1683985e22c18, 0x86995f60da1e21d, 0xcfead21a6376936, 0x719281afab66498, 0x65bea146a886bea, 0x8b6859867e2da28, 0xa10ebea790a817e, 0xfca228265aa8b66, 0x992633e9b24a206, 0x37f1b243207bec0, 0x2a421dfcc02184]
def page62 : List Nat := [0x20e7a62a2e61bfb, 0xc428a8613fb2a65, 0x88437e9b442187e, 0xbe22e42987e8869, 0x283984fc6c92883, 0x87dc8b992657fb1, 0xca218436e9b0431, 0xc65be90e8b184fa, 0xe23243105f20da1, 0x4a20cfaca214617, 0x5f86c82e85b7992, 0xd992633db2a6018, 0x61bfa2a2b995fe8, 0x22a84995f88c90c, 0x2997be87190639e, 0xfa4c20c617e232a, 0x1aa21bc21ea098d, 0x1ec21860906be86, 0xb664a0fba6498e6, 0x986faada1c21fb8, 0xe8c996639f9368b, 0xa8817e9b485985f, 0x5fa3042186fe439, 0x887886fc8c9a843]
def page63 : List Nat := [0x97f085980217ab0, 0x87a1061baa2a2b9, 0x4437c302869077e, 0xfa1e8490df8c099, 0x62206ba659ae21d, 0xfe26218621ee992, 0xa282653e930a0a1, 0x619e9b68a10ef88, 0x8b687186de4292c, 0xa10cfaada1063ef, 0xee4d8a861af2326, 0x8a861be288a0997, 0x1be2326b90eea65, 0x1a63887f6839846, 0x84facb90c61faa, 0xc859ae217e23264, 0x8c61be836a6a0ef, 0xbf21c4a885fe8d1, 0x88418ede4292881, 0x1ef08ba82637ab0, 0x8492c61be92e0ba, 0xe61dea1e85986d8, 0xeb286420efa6292, 0x65985fa2da1e613]
def page64 : List Nat := [0x6f686282637fb0a, 0x49a821be9968b18, 0x41ba2322a186f88, 0xb2a2b996fe839ac, 0x98efe87a9263bb, 0xd88b992657fa36a, 0x92c63af9926b887, 0x3efa1c62186fc8c, 0x968b986f8c49a88, 0x1077e86a1241bf1, 0xe8692e63be20e6b, 0x9263fda36a098ef, 0xfa98e42a07ae2d9, 0x68b886dea599283, 0x87f0c099281bf19, 0x6da1243bfa126a0, 0x841fc30262a05fa, 0xf9926a20ef8829a, 0x6a90efc87a8a41a, 0x7ea8718e43ae21c, 0xca88853fb2a8619, 0x873eab48610cfc6, 0x21ea498ef64a82e, 0x790efc65a2861bf]
def page65 : List Nat := [0xee2da1a437f3008, 0x98e217fb1263987, 0x1be3024b18fae64, 0xb44a886fc65a282, 0xa0fba6598a813f1, 0xc4da9a81f799265, 0x28817f1322ba1eb, 0x3fb2a64086fc6c9, 0xa60187f64320661, 0x7bc8c99263fc90, 0x8aa1a63fdb02652, 0xc653a8b66b90678, 0xea88a09967a87a2, 0x2a185fe8d19063b, 0x6fea690a817f132, 0x58a861bfa9e42a0, 0x213eab48518ee88, 0x8b684984faada1e, 0xb994fecaa18637e, 0xfc8ba8265bba2e2, 0x210217c30242906, 0x1bfb2a64184faca, 0xa64196ec628ac6, 0x187f64382861f63]
def page66 : List Nat := [0xa0d1aa43bb1b22a, 0xc617fb1262986f, 0xbea1ea498cfeca9, 0xea098dfec6a1661, 0xdfec498a81bda1, 0xc4a1a65afa186a9, 0x881bc8b60ba1dde, 0xe2b262a04faad90, 0x8b187f243984413, 0x6f8c09a883bf18e, 0xda1021fc8368218, 0x43bfa0a4a184faa, 0x21a2b1977a8621e, 0xa086fc6a90a41be, 0xf887a92633e9b24, 0xa28613f1b24b20e, 0x5fd90e61186fa65, 0xa6a206fe2da9a8, 0x20dfac221061bf9, 0xea7992813eab664, 0x1c811fb2a8621eb, 0xfba166318f720da, 0x663a06ba659a881, 0xefe868ac61ee99]
def page67 : List Nat := [0x8c9ae21be3026b9, 0x8413e9b6a4a06f8, 0xea188690dfe8d18, 0x6ba16fa43a2861d, 0x6fa6422a65bfb0a, 0xda1c876e9b04220, 0x81bfa166b8877a4, 0x8b68710dfa6d90c, 0x4996bac429a81fa, 0xb88c9a843dea1e8, 0x984613bb2a6218e, 0x53eb2e43207f243, 0x1e43185feac21a6, 0x10f788c99681efa, 0xa6210c81fc83686, 0x9663769368690fe, 0xdfa1282986feca9, 0x66a20ff26218241, 0x95fa2d92861ae99, 0x6ba1241faa362b9, 0xe83be22a42906f8, 0xfa3065884fec49a, 0x87186e262a80435, 0x6ba639a8817e936]
def page68 : List Nat := [0x390c617fb0a6498, 0x65ee21843187ec6, 0xa362b996faada18, 0xba04fa6da2e217f, 0xfc439ac41bf90a6, 0x82e87be22a6498e, 0x1bfa28a0997f04c, 0x34a0994faada106, 0x98fe0c098e217fa, 0xa4da9a81beab687, 0xaa433fab664906b, 0x9ea188a886fa4d1, 0xa64885fe0d99243, 0xeba659ac833e32, 0x2d19483ae3026a1, 0xe63af9926b20dea, 0xe9b685987f20da1, 0x6498cf8caa0a417, 0x6faada1843e7b12, 0x721a63bf2326b90, 0x43b61924a20f3e8, 0x30284905f60da1c, 0x6186faca218437c, 0xee2da1263ee9368]
def page69 : List Nat := [0xa1463bea1a2b987, 0x37e9362a184facb, 0x2a2b185f88c9966, 0x18df88c99063be9, 0xa8492c637d83465, 0x96637db1280186d, 0x3e2b264a0fba869, 0xa6598efe6422a21, 0x6faca21c43efa1, 0x8721a43bfa1a2b9, 0x241bea2a2b9977e, 0xe29e42a06bc6b99, 0x4b2057e8c19463a, 0x7ea6210861be98a, 0xba8263f690a4b18, 0x41bf21a6a10efc8, 0x1aa42907f22c182, 0x690ef48682c65be, 0xfa62928813fab68, 0x9a8213eb2887906, 0x1fa98e42184f0c0, 0xb68b986fe8692c6, 0x21cfaca214639e9, 0xc8ca8a659fa1aa4]
def page70 : List Nat := [0x2863be21a6b90d7, 0xef21a6498ef88c9, 0x860905fec4a1a21, 0x1efa439ac41fda0, 0x8c9a843bc9360ba, 0x621fda1c40886f8, 0xea168b887f24c18, 0x64a06faa3a82659, 0xfb887108615e232, 0x7a8a659ea1e8a10, 0x61bd21ea098efa8, 0x92e0ba1dfac2214, 0xa9077a8621843bf, 0xfa6c22a439ea188, 0x9ac833eab464184, 0x37e9b642a04fac5, 0xaa84907ee2d9968, 0x204fa4d9ae83bf1, 0xa2da1c87fdb0262, 0x1a63efa1c421877, 0x7e93682985fec4a, 0xc801867c85a2e61, 0xf7c8c99681fd90, 0x8c99663bea346a9]
def page71 : List Nat := [0xa617c93481987b8, 0xeab464206f88a90, 0x6420dfa2da1a613, 0x4fc6c92e21f7994, 0xb82e87fc8368708, 0x657f1b242906f62, 0xa1e8498efc8ba8a, 0x2987f04382861df, 0xfe8d99463bfa928, 0x9ae21ef93687185, 0x1dfa1a42206f8c4, 0x1a8510fec6390c8, 0xa0efa4d1aa217e3, 0x88aa8a659fab684, 0x8a41fba1c62886f, 0xfa98e42986f88b9, 0xa6390f7a87a1665, 0x85fe8da8265faa1, 0x85980217e930821, 0x841dfa1e43207f6, 0xea1a2b197f20da1, 0x65884fecaa1463b, 0x5f88c992433eb28, 0x492c63afa1c6a88]
def page72 : List Nat := [0x633eb2843186da6, 0x9968b886f865a2c, 0x29977a8710881be, 0x7e8710881be21ea, 0xa2e216db1a80187, 0x1be1aa84904fa4d, 0x3687906fa4a8a86, 0x90f7a87a12417d8, 0xa4d8ac61fb30887, 0xaa213fb2a65885f, 0xbf21a6b10efa8d1, 0xa85984feca99683, 0x94fa4d9ae81dfa1, 0x64a0061bfa1ea29, 0xc415e23243207f4, 0xc99280184feca98, 0x849977e87a1441f, 0x6b86a992416fb1a, 0xa82e87be90e6ba0, 0x439ea168b98ef6c, 0xa146a887dac421c, 0x5884fecaa1e21bf, 0xfa429ae817c3028, 0xa1e437c9360a186]
def page73 : List Nat := [0x3fda30a098cfeca, 0x1e8b906f0c09ac8, 0x104faad21e419ea, 0x68720061bf10e8b, 0x2c61fda0e611073, 0x7e8b685186f88c9, 0xe6a104fa4d9a883, 0x6788aa1243be20, 0x8790861bfa166b1, 0x2833eab465887b8, 0xfa1aa2196fea799, 0x4b21efe868a861b, 0x6feada1a439fa1a, 0x328a65be98e8a18, 0x61ee99263206eea, 0x9b084185fa2da18, 0xa886faada18217e, 0x7a86108813e9346, 0x90421be32a64887, 0x1af21a6a10ff686, 0x2a65207ec4c8a86, 0x996faa4a8887bfb, 0xc09ac43dfa1a84, 0x92637c30287884f]
def page74 : List Nat := [0x6e9b043206de85a, 0x68a084feac19281, 0xf7e2da1c87be99, 0xca20c61fb21a621, 0xe43fc21661184fa, 0xfb0a64a05fe0d21, 0x6498dfec2a1e617, 0x7ea6210c61b7a92, 0x292c61fa98e4398, 0x41be8b6a6a15fec, 0xb022b996fc6aa0a, 0x7204faad21621bb, 0xfea598a81df9368, 0x19063fa8b68690e, 0x1f799264a0cfaad, 0x30a2995fac22126, 0x184fec49ac837fa, 0xe8690c617eb0e4b, 0x1a213eb2e85187b, 0x7c8368790dfac42, 0x682907f60da1a43, 0x8dfa6d216217e9b, 0x4da1a637e9b4841, 0xe41efa1a42185fa]
def page75 : List Nat := [0xf936a6a06fa868a, 0x86a15fa4d18861a, 0x4fc6c92c81de8b6, 0x6992817a8b66588, 0x21ba2322b996bea, 0x31a8490fee8518a, 0xb994faada08617e, 0xf0c0a8a65fba362, 0xa28613eb286520d, 0x17f9b62ba16f843, 0xb465a077e87a146, 0x90e7a42a2e617e8, 0xa4da9a85af1aa64, 0x8a81bba1a2b996f, 0xfc21ea098fba649, 0xa63206fe649ac83, 0x873e87a1461bfb2, 0x429a881bfa106a8, 0x881afa9e62a06fa, 0xfa30a0994fa4d9a, 0x65a06fe8692c217, 0x4fecaa1e417fb0a, 0xaa0e617a8b664a0, 0x617fb1a8510cfec]
def page76 : List Nat := [0x836a6a17f043200, 0x698efa65a2c41be, 0xfec4a88873fab08, 0x20861bfa346a885, 0x1dfa308690dfa6c, 0xe8b987b6861824, 0x185fe8d188619f9, 0xe8692861fc21260, 0xa8857f1b243a06f, 0xfd0b20ba1ef8c29, 0x263187f28c28263, 0x8df20da2a657fb1, 0x6d908613eb108a9, 0xe61f790a4b185fa, 0xfa3064a0674c1a2, 0x8710ef8ac992835, 0x6f28682c657f836, 0xa21a41fa98e4320, 0x617e8b684184fcc, 0xa1a2b987be86990, 0x790dfec6a1221bf, 0xf20da1865dfa1c8, 0x82c65afa9a42a05, 0x17e9b685086f687]
def page77 : List Nat := [0x2e2a186feca98e6, 0x90ef6ad10221ba9, 0xa6da2a63bfa346a, 0xe61bba162b994f, 0xbc228a098dfa4da, 0xa2b9977e86a1663, 0x95fa4da0c61bba2, 0x428a861bd8b60b1, 0x865be29e42a07ea, 0xf10e6a206fa86a8, 0x43186be869ae21b, 0x6da4292c617fb2a, 0xaa12637fb0a6418, 0x857e93686184f8c, 0x99262a077a4da1a, 0x10efe868ae65ef, 0xf88c99441bca1aa, 0xa124377b128710d, 0x3dfa1e8418efc6b, 0x1e84986f2642826, 0x187f68598441dea, 0xa8292e617fb1262, 0xae877d83684906f, 0x7fb128798dfa4d8]
def page78 : List Nat := [0x243106fa65a2e63, 0xdfa6d8ae857f1b, 0xc0a1e437e302851, 0xa413eb166b205f8, 0xea1e8b884f8caa1, 0x8a18ef8869a8439, 0x4faada16639ea16, 0x6194637fa346310, 0x413fb2a64187be8, 0x90e6a204faca208, 0xb904faad18881be, 0xdc8c99065bf21a2, 0x28265aea366a10f, 0x1efa1e6498ef88b, 0x2aa2995fa6d90e6, 0x186ea868ae65bf2, 0x8a7192813eb2842, 0x18213eab686196b, 0xafa9a62a07f20da, 0x26498fee438a861, 0x4facba0c41ee23, 0x6d90e81bf90a6b2, 0xa41dfa1a84985fa, 0xf21c6a90df0c098]
def page79 : List Nat := [0x432077e2da1c81b, 0xcfaada1e43dfa1a, 0x419483bfa1a4a18, 0x81ee21a6498fda6, 0x1aa82907ea62108, 0x510eba879a843be, 0xfec498e817f9b68, 0xa1221ae21c6a905, 0x3fc930609077e86, 0x348698dfec6a124, 0x2077e86a12637e9, 0xa85a2c63dfa1843, 0x8441bfa1c4a8867, 0x7a8b66520ff2421, 0xa8598efa2a82e87, 0x85dec4a18437fb1, 0x4da1c65efa18431, 0x8617e93463185da, 0xf9b68490fe84c8a, 0x8490cfaad216617, 0x77e2da1a85be1aa, 0x219281fd10e0a18, 0x217fa3465185fac, 0xa1a0b197ea6498e]
def page80 : List Nat := [0xa886ec8c8ae65bd, 0xfa6da08613e9308, 0xa1e437fb1a85885, 0x3dfa1682185da4d, 0x1a8418eda8492e6, 0x1077e87a16656fb, 0xa6da2c437e9b082, 0xa817e9b042184f, 0xbba1e2a185fc6c9, 0xa098dfe0d21c43, 0xd7a8d282653e93, 0x6b99243dea1e851, 0xa83bf98a4ba06fc, 0xe10e6b204fac429, 0x2a187ee8718e43b, 0xefc8c9ae21bb92e, 0x3a2e61fd21ea098, 0x83be3026ba167a6, 0x9968b986f86c928, 0xb107f685984619e, 0xfec292e87ae9966, 0x19621b71924b185, 0x73fb126b8857a8c, 0x1e85884fa4d82e8]
def page81 : List Nat := [0x886faada1c43dea, 0xe8c10c81be2166b, 0x1843bc1824b8857, 0xdc8368721fdac42, 0x61106faada1e65, 0xef64d82e87788b, 0x8692e21f7994652, 0x2437c8368690efa, 0xfa3262185fe0da1, 0xba1deec2a14637, 0xcfecaa1621bf8ae, 0xd21a41bf2324a18, 0x43fc21061884fea, 0x2326520fde4da1a, 0x4085fa6c210635e, 0xfe0d994433eab46, 0x9a843be21c6a90d, 0x1bea166b886be8c, 0x2a62905fa4d1888, 0xa06f8c092e873e3, 0xeada1a41aeb08a6, 0x2861fd90a60184f, 0xbf90e6ba06fa629, 0x46518dfec6a1241]
def page82 : List Nat := [0xe7e42a2e617a8b, 0xc6a0061be21a6b1, 0xc213eb2c63205f6, 0xfa366490efe859a, 0x609077a0da1a857, 0x5bec6a1463fda10, 0x7a8a417e9b68510, 0x61ae9966a086fa8, 0x90e6b207be87190, 0x4a05fec2a1261be, 0xfec2994813fab26, 0x990837e8b687185, 0x1ae9926a084feca, 0x3686887788c9928, 0x184feac21a657d8, 0xc64a2e61ba9922a, 0xac21bda10a098e7, 0x7e8b465986fe849, 0x842187ec8698e43, 0x87f68618621efa1, 0x4da1a217e9b0859, 0xc617fa346518dfa, 0xf21a4b887ea6390, 0x6ba0f7a8690881b]
def page83 : List Nat := [0x6da6492e83bfb12, 0xda1e43bfb2a6508, 0x41af3026a10df60, 0x8368690ff686182, 0x3885f88c98c417d, 0xf88c99463fb2326, 0x21a659ea168b985, 0x5be3126b20dfead, 0x8a4b187f20da1e6, 0x10ef24a82e87be9, 0xa6390e819f8368a, 0x2863fb9322a187e, 0xdfa1e85086fc65a, 0x68790cfa4da2e63, 0xcfeada1263f693, 0x86996619f2188a9, 0x8437e232a0997ba, 0xd83687196be8d9a, 0x43206fe65a2c637, 0x77e85a0c617e9b0, 0x698e213f1b22a10, 0x81bca80a0997ee8, 0x1a860906f8ac98a, 0x1886fc849ae21bd]
def page84 : List Nat := [0xfeca98881fd9306, 0xa14639ea168b994, 0x33eab48790f7e86, 0x2a43206f265a826, 0x996dc64928813fb, 0xc65a2c617c83687, 0x2861bfb026a216f, 0xbd9824b185fec29, 0xe42207ec8718e43, 0x87ea6518a21fb18, 0x8710c613eab6861, 0x241bda1aa010fb8, 0xf1aa8490dea2d99, 0x4ba1ebe869ae41b, 0xeec628ac41bfb02, 0xa8a657a8b66518, 0x61be10e6a205f6c, 0xa366498dfec2994, 0xa205fa4d98a81ef, 0xb8c6a14639fa1a4, 0xa1661beab68790d, 0x1efa1a62185fec2, 0xb22b214fead98a4, 0x186ec628a8413f1]
def page85 : List Nat := [0xe8610881aeab686, 0x8263bf10e8b1877, 0xbf9926ba0ef6ac2, 0xa2a185fa6da1221, 0x7bc8c99663fb90, 0x649ac41be10a6b2, 0x4833eab68610eba, 0xeb28421857e8c19, 0x2a1877a2da1c817, 0x5fec498c81bba12, 0xda1665b7a144a88, 0x613f1b22ba15ba6, 0x936a6a0fba4da1c, 0x98efe8d1aa413e, 0x7a8c19463bca16a, 0xa9a853e2b242a05, 0x1be8b46a904f60d, 0x1861884fead9928, 0x9867a4da2e61eda, 0xa6422a21bfa0a4b, 0xc817eb2843186f, 0x9ea126ba0cfaca1, 0xa6b906f865a2e21, 0xff20da1861ae21]
def page86 : List Nat := [0xc09ac83beab665a, 0x843bea106a886f6, 0xfb1a8418feac221, 0x2a186fe8692c637, 0x4faca20c41fa10a, 0xd992213eab46210, 0x817e93682184fea, 0xa1a85997be6498e, 0x78867a64a2e61df, 0xda64928817a8b48, 0xa18637e8b664a06, 0x37e23264184faad, 0x1aa010efec09ae8, 0x187ba6498861bd2, 0xc868ac657f1b242, 0x86217eb2e43186f, 0xbe90e8b107f6841, 0xa4b986dc8492c63, 0xdf8c0a1c43bfa1, 0xc4a1e41afa1a6a1, 0x263bf9926a20dde, 0xea188710ef48ba8, 0x87104fa4d9ac21d, 0x7ee8698e43beab6]
def page87 : List Nat := [0xd21661fa98e4220, 0x65bea1a4a18dfa2, 0x1924b18ddec4a1c, 0x610dfe0da1e43b7, 0xfaada18217f8348, 0x21621bba1a2a184, 0x1b7b2a64195fa6c, 0x368718cfaada166, 0x20efe4b8ac617d8, 0x8859a821bf1b24a, 0x1a433eb2887886f, 0x7fb0a86985f8c0a, 0xa2b9067e8692c81, 0x86fa868ae65be21, 0xda28657ab08858, 0xe833e9b68a9967a, 0xda0a60184fa6c92, 0x62886f88b28a65f, 0x6fa8d1aa41faa1a, 0x598c63ba92a2a18, 0x61baa1e2b997ea8, 0x21e43185ba6c108, 0x2206f88712a21ee, 0xfec498881dfa1e4]
def page88 : List Nat := [0xa0a61ee21842185, 0x3bfa0a6b106fea5, 0xb486886fa8692e6, 0xa0ef687280433fa, 0xc6c90c61be3026b, 0x10213eab487885b, 0xbe9968a18f7e87a, 0xea2995f88c99421, 0x86fcca21a43be22, 0xc0996633fb2a421, 0x2417f1b242207be, 0xf9968b886f88b99, 0x64906fc429ac41b, 0x6fa63a2c41af1aa, 0x28ac81ae29a42a0, 0x65be936a6a06ec6, 0x1824a086f88b992, 0xb186f88692c63bc, 0xee878ae65bf90e8, 0x99061ee99263a06, 0x13e32a64905fe8c, 0x2a86887f20da1c4, 0x1877e8c21e433e3, 0xeca908817e8b464]
def page89 : List Nat := [0x1a43ae1aa6490cf, 0x3fab66498fda4da, 0xe84996fc63a2841, 0x4fead99283dfa1, 0xc2196213fb2a642, 0xa433fb2a8598dea, 0xf2326b90cfcca21, 0x2b105ea2da1463b, 0x6eeca8a861bfa1a, 0x790881af310a6a0, 0x659e9b68a1977a8, 0x90a80184fead21a, 0x4886f88a98a41fc, 0xf60da1a65dea1e8, 0x21a21be2324b18d, 0x73fab48690dfa4d, 0x2e6498f7e4da1c8, 0x187ba2da1861be2, 0xa6d108813eab462, 0x661ae9926a20df, 0xbe1926a20ff2432, 0x462885f88c99461, 0x6fe4b8ae87faa1, 0xd190833eb10a6a]
def page90 : List Nat := [0xa43dea1e8490df6, 0xf8b686184f8caa1, 0x6a886f88c9ae41e, 0xefc6ba0a413e930, 0xc99065bc930a098, 0x500200200c7d88, 0xc01200100b0460, 0x805e00001d0000, 0xe400000003c00d0, 0x200004a5468, 0x1200301c0410310, 0x748030055c9bc58, 0x358000060110260, 0x628060062228e7d, 0x3100002c0030444, 0x6300122980e0030, 0x800011a81103d0, 0x700b0020003e28, 0x20005f080f0010, 0xb01d0160070080, 0xf00c4898081ef8, 0x2400002227680c0, 0x730010033998200, 0x3042280000001c0]
def page91 : List Nat := [0x300302e0210, 0x3c00300c0074c68, 0x301308d8380090, 0x3a0280030070070, 0xd180d0020250080, 0x1300700200a0012, 0x818d08a9020050, 0x1d0143a08690370, 0x6c00200014d0000, 0x3900002902b0150, 0x420de8bf00f0010, 0x39065812244bae8, 0xa200300101d0000, 0x40010013d98061, 0xa880000000201d0, 0x1c5a482b8150221, 0x878010010000010, 0x3101139388103d5, 0x718080240960040, 0x1301301200000f0, 0xd1088080190000, 0x1603b0000e19110, 0x9400200001d00e0, 0x3f4ff8000740180]
def page92 : List Nat := [0xb38a881b0030080, 0x1814402784c20a9, 0x3004a01224e8100, 0x40042e98040, 0x70240000030290, 0x1f11980101910f0, 0x41e480500902f0, 0xfba89bda80401a0, 0x10000000000041, 0x181a68175e18000, 0x2400002201e0260, 0x50130050010450, 0x1601300125880c0, 0x50000010ce0, 0x6a82f00601805b8, 0x620021dc80a01a3, 0x1e00400104a21b8, 0x1801204505a0180, 0xe00004844d8810, 0x98a7780000229b8, 0xb90120000420255, 0x44718000010000, 0x1607f8490010060, 0xf5038360000]
def page93 : List Nat := [0x1701d2fe0, 0x20250020020010, 0x1707a0040010110, 0xdad4284125c8040, 0x1e00801600214e9, 0x1d01302f0500060, 0x500100f2fa84e0, 0x5100100b0240030, 0x95a98020110010, 0xc4658000000000, 0x348220002df8020, 0x7915187e0000052, 0x40040100000010, 0xc01138f8110000, 0x10021150588070, 0x1e01100000000a0, 0x60080a90000, 0x404d01a00300a0, 0x75558600025f38, 0x101281108d0, 0x1800200702d0060, 0x808600032c8040, 0x1d0011200aa0010, 0x494b18070300120]
def page94 : List Nat := [0x28000060bf8570, 0x3e380d00000b0, 0x2700a0192330000, 0x30060030000950, 0x520bf0020151118, 0x30050000090340, 0xc00005c00a0, 0x401000e05300b0, 0x300f901e3968, 0x9d0074b98000050, 0x2d78155e98460, 0x225e28020480, 0x4000000, 0x3000000004, 0x1400000002000, 0x700000000c00000, 0x400000000, 0x140000000240, 0x600000000b0000, 0x34000000, 0xf00000001c, 0x4400000008000, 0x300000002400000, 0xa00000001]
def page95 : List Nat := [0x2c0000000540, 0xc0000000170000, 0x64000000, 0x1b000000034, 0x740000000e000, 0xf00000003c00000, 0x1000000001, 0x440000000840, 0x810000081010000, 0x20414000040, 0x810f00001020c, 0x40400008080000, 0x600002020800004, 0x848080001010, 0x2120c00004240c0, 0x808000181000000, 0x604080000c0, 0x18105000030208, 0x4200000c083000, 0x100003022000006, 0xc48100001890, 0x3120a00006240c0, 0x800000189060000, 0x644040000c8]
def page96 : List Nat := [0x19104000032206, 0x4000000c883000, 0x400004020400008, 0x1008280002010, 0x412060000824080, 0x800000209050000, 0x8440c000108, 0x21107000042208, 0x640800010c80000, 0x400004320600008, 0x10c8280002190, 0x102020000864340, 0x830000881020001, 0x220420000440, 0x90101000120200, 0x41800048082000, 0xe00012020e00024, 0x4808780009010, 0x212060002424040, 0x850000909060001, 0x242430000484, 0x98101000130200, 0x4140004c081000, 0x100013020c00026]
def page97 : List Nat := [0x4c48100009890, 0x3120a00026240c0, 0x800000989060001, 0x2644040004c8, 0x99104000132206, 0x441c0004c883000, 0xe00013221800026, 0x5008000009910, 0x402080002804080, 0x878000a01050001, 0x282408000500, 0xa0905000141206, 0x440c00050880000, 0x700014220800028, 0x508870000a110, 0x432040002864000, 0x820000a19030001, 0x28641400050c, 0x10810100014321a, 0x41400084081000, 0x21021000042, 0x8808080011010, 0x2020c0004404100, 0x8780011010e0002]
def page98 : List Nat := [0x442404000880, 0x110906000221206, 0x4040008c080000, 0x400023020400046, 0x8c08280011810, 0x302200004604180, 0x810001189010002, 0x46240c0008c4, 0x11890600023120a, 0x44040008c880000, 0x400023220600046, 0x8c88300011910, 0x3221800046441c0, 0x810001201000002, 0x480410000900, 0x12010f00024020a, 0x240c00090481000, 0x24120a00048, 0x9088180012110, 0x432000004844100, 0x818001219020002, 0x48641000090c, 0x18810100024320a, 0x414000c4081000]
def page99 : List Nat := [0xf00031020c00062, 0xc808000018810, 0x2020c0006404040, 0x818001909010003, 0x642418000c84, 0x198100000321218, 0x408000cc080800, 0x500033020800066, 0xcc08300019810, 0x312020006604200, 0x818001989020003, 0x662414000cc4, 0x19910000033120c, 0x440c000cc880800, 0x600033220800066, 0xcc88700019910, 0x402040006804000, 0x810001a01040003, 0x68240c000d04, 0x1a110000034120a, 0x4410000d0881800, 0xe00034220e00068, 0xd0c800001a110, 0x432060006864080]
def page100 : List Nat := [0x828001a19040003, 0x68641c000d0c, 0x1820200034321a, 0x48100c004101008, 0x403034340006046, 0xd4441028181a1a0, 0x3040006a2408100, 0x28218182040430, 0x8a22081410c8c5, 0x890a01045120408, 0x480c1144c502822, 0x104513240808a26, 0x404c502828098a0, 0x324000a02628181, 0x30280992040501, 0xa02848001404c9, 0xa1a04050142408, 0x81014c50101028, 0x505314040a0a628, 0x4c509020298a0a0, 0x3240c20a4648101, 0x10829a1a001052, 0x20a686810414d0d, 0x81020610534340a]
def page101 : List Nat := [0x8144540c10108a, 0x611503040c22a06, 0x5490d0188a91920, 0x3240622a4868144, 0x108a9992061153, 0x24a020818454d0d, 0x81820012501041e, 0x8004940c103092, 0x12504140624a08, 0x948c50189291820, 0x4040024a4628184, 0x1092998a061252, 0x262462814494d0d, 0x99920313133040c, 0x8004c84c501898, 0x613233040c26446, 0xd40850089a80820, 0x2140c26a04280c4, 0x189a8202021350, 0x26a08480c4d4105, 0x819203143131406, 0x8145140c9020a2, 0x414533040428a46, 0x14cc1028a299820]
def page102 : List Nat := [0x324062a00428185, 0x18a88212031510, 0x2a208681454410d, 0x21a02152041406, 0x681054810d018a9, 0x31523304082a408, 0x4c109018a9810a0, 0x4340a2a804280c5, 0x211a8882052313, 0x46a2428048d4481, 0x9a1a0223514140a, 0x48049144c502920, 0x624513240648a26, 0x4810d01128010a0, 0x324084a40868109, 0x1829192063052, 0x60a486814c1490d, 0x9a1a02305343400, 0x6814c14d0d02182, 0x231003040460a68, 0x540c10118819820, 0x3040c62a060814c, 0x318a9992033150, 0x62a686808c54cc9]
def page103 : List Nat := [0x9a1a0232503040c, 0x2818cc004101192, 0x633033240c66066, 0xd40850319a80820, 0x4140666a080808c, 0x19a1918a053350, 0x68a06480cd14085, 0x918205345032408, 0x808d148c5019a2, 0x534533040868a66, 0x404c5009a299820, 0x3140c6a0262814d, 0x21a80992013501, 0x6a0264818d404c9, 0xa1a02352140408, 0x6810d4850d019a9, 0x43531404046a428, 0x4c501029a98a020, 0x424086a6282814d, 0x32828992063531, 0xaa6040819548cc5, 0x810a06553021406, 0x2809c144c9032a9, 0x9252314070a048]
def page104 : List Nat := [0xd006002000800, 0x4402000e0060026, 0x806c03201800a40, 0x12c09004101e80e, 0xf81680b00550278, 0x3b01c00d806702, 0x8a04302040fc07b, 0x9d04c025811c0, 0x15e0ad055029014, 0x417c0bc05c02cc, 0x83341960c506103, 0x6e83741b40d6068, 0x507883b01cc0e10, 0x10508103f81f00f, 0x2c1150888430212, 0xc25c12708e84682, 0x51027a13809a84c, 0x8053c29c14b0a28, 0xad05682ae1530a, 0x700b405982c615e, 0x21830be85e42e41, 0x3321930c7862c31, 0xc43541a80d10678, 0x86f83701b60d906]
def page105 : List Nat := [0xea874c39a1ca0e0, 0xb0f307883c01d90, 0x1fc0fd07d83e01e, 0x2420f1050818402, 0x844a22010e885c4, 0x8e846822f11608a, 0x4091048424111f8, 0x12b895849e24a12, 0x6a13389884bc25b, 0xc27b13b89c44d82, 0x51828714209fc4f, 0x585222911488a38, 0xa9854629f14d0a, 0x5f0ae85682b1157, 0xa16b8b405982c51, 0x2eb1748b905bc2d, 0x1030217e0bd85e4, 0x862a3141878c306, 0xca464832118e8c6, 0xe8cdc6623301970, 0x1a50d1c68834019, 0x611ad0d5c6a234c, 0x63711b48d986c83, 0x70437d1bd8dd46e]
def page106 : List Nat := [0x7472c38d1c48e18, 0xebc7543a51d10e, 0xe30f0c7823ba1db, 0xa1ec0f4c7a43cb1, 0x3ed1f58f947c43d, 0xf63f81fa8fd07e4, 0xc81c40b20290007, 0x8483c41c20c904, 0xf10dc8684292131, 0x226912088444121, 0x5d22b91588a2450, 0x846a23391848be4, 0x8fe47923991c48d, 0x5092248f2451208, 0x129093a49924b12, 0x5e12d895e4a8253, 0x426693249844bf2, 0x4e527093749a84d, 0xf84f827a13b09d0, 0x4a0e50528113fc9, 0x480a34515289143, 0xa94b4a4e5242909, 0x2a194fca7853929, 0x582aa9548a9c548]
def page107 : List Nat := [0x256c2b31580ab85, 0xb0257e2bd15dcae, 0x6cb2a58e2c41618, 0x9698b465a12cf96, 0xde96dcb6a5ae2d4, 0xb2eb974cb985c42, 0x5f02f49794bc25d, 0xc6002fe97e4be8, 0xcc2e6113079828c, 0x8a4c5262230f986, 0xc18d8c6062f3161, 0x3249908c7e63c31, 0x583299944c9e64c, 0xc6663309978cb26, 0xd0667b33a99c0cd, 0x70d2868e3459a1c, 0x1ab0d4e6a234f1a, 0x601ae8d6e6b4357, 0x63699b2cd8e6c23, 0x6ed3741b88dba6d, 0xc70037e9bd4de2, 0x8e267113869c28e, 0xcace4e72138d9c5, 0xf9cece6e7313969]
def page108 : List Nat := [0x3a89d34e9074439, 0x653b19d7ceb4757, 0x27733b89db0ed27, 0xf147863c01df0ef, 0x74f327963c81e34, 0x9ec4f527a43d09e, 0xe19ef0f747b73d9, 0x83ea9f3cf907c73, 0x7f03f51f94fc07d, 0x88003fd9fe0fe8, 0xd028810406a02d0, 0xb5052826410206, 0xfa0ed06e8354182, 0x427a13508e84441, 0x64430a1710aa853, 0x887843821b10d08, 0x11688344122010f, 0x8914089b44b2245, 0x22b51548a645222, 0x5d22e116c8b2458, 0x466a3251888c04, 0x8e5470a36d1ac8d, 0xf28f7479a3c11d8, 0xd21890a482a3f51]
def page109 : List Nat := [0x49123e91b48b244, 0xba4d126092d4942, 0x4a3250d27c93949, 0x584a9a54529a94a, 0xe9684b225892b49, 0x30297c4bca5d12d, 0x5532498d4c42611, 0x268d34299f4cc26, 0xdc26d93629ac4d5, 0x84e226f93789ba4, 0x9d74e9274139a9c, 0xe89ef4f4a7893b8, 0x1408a014fe27dd3, 0x851428a10507282, 0x42881438a1a50b2, 0x51da8e1464a2e51, 0x525252919486a3f, 0x8a5f52ea9694aca, 0x4e8a6f53529a54c, 0x1d50ca8353ea9e9, 0xaa65524a8d545aa, 0x582aa5550aa3550, 0x255daae1568ab05, 0xacd565ab19588ac]
def page110 : List Nat := [0xbaadb56c2b5559e, 0x15daae7572ab7d5, 0xbed5f0af6578abc, 0x6ac2d60cb0357ea, 0x58c2c51620b0d58, 0x2d5952c9163eb1b, 0xab3b59c2ccd660b, 0x698b465a1ad0567, 0x6d6b2b565a92d39, 0x2da16ccb635b0ad, 0xc2ae096f4b765b7, 0x95cb2e49718b895, 0xba75d2ae81738b9, 0x7ebb75d82eb9758, 0x579cbcb5e3af117, 0xf957c2bdc5ebaf4, 0xc2fd97e6bee5f4a, 0x602b011802bfc5f, 0x16609302d810c07, 0x4c27612b085836c, 0x872c33617b0b185, 0x4d89ec4b6233101, 0x31a18ccc6062d31, 0x3ab1c98e2c6f637]
def page111 : List Nat := [0x5641b2018fac786, 0xc91646322590cc8, 0x56ca464f326d928, 0xd97acb765832b99, 0x35d9a4cd0665b30, 0x8b3a99cece56703, 0x67eb3ed9f2cf367, 0xd683b411a02cff, 0x2d1b68cb449a20d, 0xa62d2d694b499a4, 0xfda76d3869ab4cd, 0xb531a92d456a0b4, 0xac3555aa8d516a7, 0x86b2b58dabcd5a6, 0xd7b6bab5bdad8d6, 0x20d8e6c4360dafe, 0xdb2ed966ca3651b, 0x6c9b5ada76d1366, 0x1b705b76db76dab, 0x6eb373db9adc76e, 0xe36f03771bb4dd8, 0xadf26f7b7a9bcad, 0xc0ae006fe37e9be, 0x5dc26e0f7063825]
def page112 : List Nat := [0x389dc48e2070db8, 0x1cb8c9c5ee2c715, 0xc723390dc7ee3b7, 0xe6072eb951ca2e4, 0xe4e6d735399dcc4, 0x9d08e8173cb9d9c, 0xa4dd24e8e7443a1, 0x23a7dd38e9974bb, 0x758babdd5aea875, 0xbe75e3ae9d6eeb3, 0xcecc7653b1dd86e, 0xdbced976abb41d9, 0xb5dd6ee6771bb85, 0xbc01dfaef5778bb, 0x8bbc4de1af0a781, 0xb793bc8de44f1e7, 0xf3b79cbcd1e5cf2, 0xb0f567a73d19e84, 0x5ed6f677b23d75e, 0xe09efcf7a7bb3dc, 0xa3e49f1af8b7c43, 0x7cf3e71f32f957c, 0xb37d83eb1f4afa2, 0x8fc57e03eedf70f]
def page113 : List Nat := [0xfb0fd67ea3f41f9, 0xa5fccfe37f03f75, 0x3fd9fe8ff07f63f, 0x3c012002fff7fe, 0xe80e405e02100b8, 0x2c814409a04301, 0x8503e81d40d6067, 0xe0a304b825411e0, 0x19a0c705f82ec15, 0x141f20ef06d8354, 0x849423e11708884, 0xa68514282137096, 0x50b5858c2b21550, 0x1930c4860c2fe17, 0x7a1bb0d8869433a, 0x43ba1cf0e4871c3, 0x7fc3f21f50f6879, 0x8889c43e2151058, 0x12b893449223d11, 0x8f13f89cc4da265, 0xa2ad1568aa453a2, 0x5962c71608ae456, 0xe45e22e916f8b54, 0x8c6462230f1828b]
def page114 : List Nat := [0x9e8cdc652325190, 0x51aa8d3468a33f1, 0x36b1b18d7c6b235, 0x1a3891c38de46e6, 0xc7563a51cf8e547, 0xf8c7ae3cf1e08ed, 0x590047fa3f31f58, 0x21790a483a41320, 0x4522090e4866431, 0x647b23891848aa4, 0x93a495246921c90, 0xf496e4af2529284, 0x93849b64d126492, 0x89940c9de4eb271, 0x929694a4a425192, 0x5552a99514a7a53, 0x65732b5959cabe, 0x4b325912c7962cb, 0x6dcb665af2d3967, 0xe9734b8a5c52dd9, 0x2ff97e4bda5e52e, 0x2330e9864c1e60b, 0x264531f98ccc5a6, 0xcf266f3309954c9]
def page115 : List Nat := [0x9cd3269534399f4, 0x9b1cd7e6b33559a, 0x749b84dba6d5366, 0x93829bfcdea6ed3, 0x72d3929c6ce2270, 0xb674d3a09ce4e6a, 0xcef27733b39d84e, 0xe7cf3a7953c79e0, 0x59f0cf7a7b53d49, 0x3f19f74fae7cf3e, 0x134059ffcfde7ed, 0x2831415a0a50428, 0xbe853426a11508, 0xfd0ea871437a1ad, 0xa28d12e893440a1, 0x66a30516e8b1456, 0x1476a38d1ba8d34, 0x913484a3fd1f28f, 0x7e933495a48d22e, 0xd2d695d4aba53d2, 0x63531a9854bea5c, 0x7a69534a9974c8a, 0x4e9a73d3869b74d, 0x7501a7cd3ce9dd]
def page116 : List Nat := [0x2a1d509a83d412a, 0x492a3d51aa8a544, 0xc54cea6352da955, 0xaa15506a7b53aa9, 0x59aab5546a97547, 0xf564ab05576ab55, 0xaff57caba55c6ac, 0x66b2d593ac5d61e, 0x56b2b515a1acfd6, 0xde56eab715b3ad8, 0xfae6571eb895c1a, 0x5e3aef575eba75c, 0xf15f7af957babcf, 0x6c15607b00d7eeb, 0x882c35616b09583, 0x8d8b6c59628b125, 0xb22d906c77635b1, 0x57b2bd94aca164c, 0x9668b335992cc16, 0xcf5678b39d9bacd, 0x52d2368cb42d9fe, 0xda8ed4169db4bda, 0x59dac6d5d6aab52, 0xbb615af6d736b5b]
def page117 : List Nat := [0x6d8b6b5b52da56c, 0xe36eab72db8adb9, 0xedf36f5b79dbc6d, 0xc32e11705b80dbf, 0x25c86e39715b88d, 0xb99dcc2e59728b9, 0x4aba45d12e7b73c, 0x775dbabdd52e9d7, 0xee776dbb55d9eec, 0x1af0177dbbe5dda, 0x5e52f1f78dbc45e, 0xd55ea2f477a0bce, 0x2bdededef637acb, 0x7d7be8df2ef937c, 0xdb7e7bf15f86fb9, 0xaff77f6bfa5fbef, 0x47015809c015ff, 0x4609b04181bc0a6, 0xc1be0cf06382cc1, 0x4cc24e10b08383c, 0x185fc2e615f09f8, 0xe069ecf50b8630c, 0x2aaab0806e7a0c9, 0x853e818005d0407]
def page118 : List Nat := [0x801252840c21655, 0xce41c0b819221b0, 0xd9079e840c80307, 0x28110e810fdbd5a, 0x200519861c0170, 0x9a078200a6ea3a0, 0xb83c0c1c0c94532, 0xd780c030081e6e0, 0x3c0803c40910e05, 0xd334fc0d018e963, 0x4d21b0d84106180, 0xc8081b8310d2e06, 0xa301c52685425a2, 0xc66a20e0606ce61, 0x1f64b4c20e40b80, 0x62702ee40187034, 0x80c0b8d03e1a0, 0x104f2353a1a5f82, 0x5840301f1d8389a, 0xc3610a9a1c47555, 0xd20c29030100680, 0xf5f020060b87996, 0x82154bd9e1a0401, 0x685b04042060d24]
def page119 : List Nat := [0x806af86b0d86033, 0x5c41a530701c043, 0x1a0fba54a6e10e0, 0x686035531a0b430, 0xd96d3100bc40050, 0xe18834ad590680, 0xc05c0a190d98834, 0x958d26586808d10, 0x230738a24d80d01, 0x1002e4d0838d0e, 0xc1c047206934221, 0x1c0e858301ac080, 0x22641e0d0f88820, 0x9a0060d061a8d24, 0x2001a0d78060d0f, 0x70c0e818c203034, 0xc4cf618400d430, 0x18a00d86698199b, 0xa07c1a0e4a83809, 0x8061806abc2f724, 0xc7968c03819108d, 0xf0624c330e06020, 0x83e1b07010061a0, 0x321a06840046e88]
def page120 : List Nat := [0x1a436040103034, 0x66202d83da21b1, 0x3265b4830100300, 0xb81408030806122, 0x598788d05d94300, 0x66942a12690858, 0xf03c301b0b8f834, 0x58c0e41862e4252, 0x3001aec30170e5c, 0xd820dc9f0803406, 0x176690dbf1f6182, 0x109401820184a07, 0xa86d32b5272501a, 0x4480c03249100f6, 0x1f3d8680617ba8b, 0xadd0dcd10d06036, 0xc060e0c0703e22b, 0xea2b15d2361885, 0x6069be6a0bafc40, 0x53a310e0c839125, 0xc40b8100aa20c3a, 0x7a2034030e05d96, 0xc301c084b4ca183, 0x1a64042486a691b]
def page121 : List Nat := [0x2b442e1a3705c0a, 0xed2e607840080f4, 0x6ad554a5540d5b, 0x680d0a213931c2e, 0x436196581cc4e10, 0x19710d837592e1a, 0x4834ba1a0c3ac3c, 0xc060f0f9ac200e3, 0x73198810e197685, 0xd00ca0b3278703e, 0x4205969b902e100, 0x1a3106830f2402f, 0x486948172007ce0, 0x8b86e08019a21a3, 0x4d83414a0e20e13, 0xf83406410c13c42, 0x36176f818e4220, 0xe0f068217e2035, 0x7c5830c60d978e8, 0x82e36288d09c5d0, 0x374884213130d1a, 0x7a58d40e1006a24, 0xccc830806034051, 0x1f03164da0c8003]
def page122 : List Nat := [0x18801e1f4f2a42e, 0x4206837868a0170, 0x430b8883e346055, 0x12fe6b410c03c58, 0x834100d94d10562, 0xd272d030200306, 0x1215a2170c8603c, 0x30df0faf430040, 0x52029ae2bb631f, 0xd8601e190b87942, 0x3c1b4d8d020680, 0xe722541ec13401, 0x1c90838064756c, 0x685023602e1a1, 0x184e9a45e940c02, 0x2c4d9610030e434, 0x8301989200d41a2, 0xc0d08214320848, 0xf8e030341906836, 0x6a41b014e6170, 0x54581836101807, 0xd07d903d080fd44, 0x5a41b0c05c0a000, 0x300f52a046d3781]
def page123 : List Nat := [0x7ae492dc0701408, 0x1e1b1037094180, 0x181006d3eb64e04, 0x80382e0f0701034, 0x154a10f28c0c050, 0x1708060346d0701, 0xc0a408030103ca0, 0xf2174d3388e1a0, 0xe0281006100c36, 0xb0601e321834060, 0xc344f18038066b1, 0xf38140201c0207, 0xfa7dc20e1106c20, 0xc1a04071e188060, 0x205b214709c3130, 0xf8f030040134da2, 0x9341b070112ae40, 0x20a205c02180fb8, 0x100d8ee41e9f420, 0xc0c109f0cc20060, 0x8b0c03ceec00f05, 0x3832200e5d954, 0x4361f029bda2187, 0x9127ad4c4940b81]
def page124 : List Nat := [0x206adc10515bc34, 0xc0a04641781c100, 0x1a0801866180d05, 0xfb34300e021a590, 0xcb21a381416a6a0, 0x1b0c00c060d1883, 0x70354e100790c38, 0xc1a0bd605e0f0, 0x374583c31043994, 0x115c345f080381b, 0x65c1f0d2f578560, 0xe0c1340b4d0d9a, 0x40725a18518c586, 0xcc4c3c30400cd13, 0xf358847c9c1422, 0xa341181f0c042aa, 0xc20212b03c0a6da, 0x10105bca0681480, 0xc248641b34b2180, 0x6c1c1887008c50, 0x220817c940e018c, 0xa05c0aca0d3381e, 0x301a0087c437b4, 0xcb0c0340c850bde]
def page125 : List Nat := [0xc1ecde0d01ab946, 0xc37551a040001a0, 0x182d8157ae21900, 0xcb203618aa2ad18, 0x81a980b984443e0, 0x980cbac21093783, 0x783406475188534, 0x1bc690c83a1eda3, 0x6e0b80818060006, 0xa8c01c04018410a, 0xaf57cbdb3830cc4, 0x185a25134bea886, 0x11402e040180802, 0x81e700f1c836df1, 0xe68aee0073809b, 0xddcae2d43607d8c, 0xa010c0d1c4ef5, 0xd1e05ce2a20c08, 0xa8c0080308214bc, 0x13e056f84196684, 0x220c06460031087, 0x22acba340b831a7, 0xdb80e021f436177, 0xd94a103085955b]
def page126 : List Nat := [0xcb8c42e40d15838, 0x9ba300700c44360, 0xdf0d889a008bc15, 0xfad810036900830, 0x1389518014080e4, 0x20071a41e0e0d8e, 0x80301e0d018c49a, 0x9c0170293034732, 0x18151781e0d0c03, 0xc884140f7183afa, 0x2aac40d86114880, 0x31d12a105d0c86, 0xe06d441866b741a, 0xde1a4f05ef6a4b, 0x5cad8693c7e0bd7, 0x7880320d0e05435, 0x8307d0319c3e1b0, 0x40d06034030806, 0xcb11909a1c1300a, 0xc18020b8d1c41e0, 0x910d060093c9d83, 0x9820c60e0c85c30, 0x1ed90e01596176, 0x2901830fc172306]
def page127 : List Nat := [0x683eb24d0d39196, 0xa2a170d569469d0, 0x100d5523cbc2400, 0x862a6bf0f86068, 0xc34e62685c1c067, 0xd50db481cfc0bbe, 0xc8a40803013902e, 0x82e1a10840356d0, 0x31140400cc52f12, 0x40409c1a0806d24, 0x88010b5428f01b6, 0x10718393c9d1003, 0xe842781a673902e, 0x420e72e16c060d9, 0xa00f83c06730b88, 0x806038c85fc2820, 0x30212f9bc18620, 0x1c194a252512794, 0x105c08d83c810d2, 0xc1e192828c10030, 0xcc1b8610a730605, 0xa8800c216c03c0a, 0x1966849db0e4e34, 0xf350c06c590d08]
def page128 : List Nat := [0x69414ce20305c3c, 0xc34695a0180a170, 0x181da8c0ae1071f, 0x99402e080200c70, 0x37720f8383e0d3, 0x195eabc48170d25, 0x4a32a8ab080603f, 0x834a607a902f531, 0x1a1006830b90dd3, 0x11ba86b20c0380c, 0x1c850680380c048, 0x106686c06170d07, 0xa540349f0c8300a, 0x40a1810a6aa2202, 0xbf0d840e6d00803, 0xa85c20700680c68, 0x420210f819ecf54, 0x6e01000343001a1, 0xe8e196e40680cfc, 0xa7a50198182e856, 0x1c10b916c0d0180, 0x312430050681006, 0x4209e0b81834100, 0x1b0e528e018102d]
def page129 : List Nat := [0x3008b803068601e, 0x56c0c0bc6d7a570, 0xdb6b22de0f0806, 0x3341c203794cdc, 0x1ae410261b0211, 0xa407011541a0186, 0xcda030b65a8405c, 0x310010408d61a0, 0x1bbc0781aa41804, 0x58100a1a0c5e430, 0x38bc0f860344e6, 0x100787008620321, 0xf0d8d038311bda6, 0xc06320db9868e20, 0x88500c3418082e, 0xc830340369a6845, 0x425c0d9a438a42, 0xc10554a5540d18, 0xe38c2e052786830, 0xd497c0da88301a0, 0x1a0e5a834060c5e, 0xb0c200d1003ad2, 0x8281a0c306f8196, 0x20d061f46e039a]
def page130 : List Nat := [0xfb1c31240301006, 0x41e0d0f8601a060, 0x6b0d06678290ba6, 0x61401a0337cca68, 0xd8c1c19391a4795, 0x5352d41e2f0e00, 0xb8340a035186040, 0x16c1c0b86c064d0, 0x2a4d0c406984b86, 0x83841a03951409f, 0x8200951428341b0, 0xb024a2e1278641b, 0x701408030dbccbe, 0xa343f0c031a4170, 0x190883dba1c1b08, 0xc841a4d30d07c36, 0xcbe474aa69a6d83, 0xf67a86018802805, 0xc05d6c17060ec34, 0x9c00e272ec8e0f0, 0xe018683f72b8b1, 0x794468e227171d8, 0x13c790bc918e1a7, 0x10585bdc4190d57]
def page131 : List Nat := [0x300c66cc655b81e, 0xc32c0078801c0d0, 0xb32686038211b0c, 0x1ce4c4105d83a70, 0xc1ed83c88034276, 0x5b0c014b2830686, 0x2be8dc5344159fe, 0x3e6f0f03dbea60, 0x324a2ecd4423988, 0xe1580c02018204e, 0x4e01037034daa15, 0x3b4c082d0850808, 0xf0e196e40680dba, 0x49a185b2d654853, 0x40e564401906ca, 0x683c40333703438, 0x9900d5b062b49d0, 0x100801930200d4b, 0xa0615e0f029c000, 0x38174fad12a9a1, 0x14080e81c4a2208, 0xbb8964180e07e6e, 0x2e980db9118290, 0xc70c85ce4220d06]
def page132 : List Nat := [0x680c7e1c379a034, 0x9861006b8c1cd20, 0x180d30c1a6f0733, 0x7041f0c81906c1c, 0xc381b0d06132b63, 0x1c1008420320786, 0x93841c400bc4c34, 0x4206707298d4e36, 0x502068a0174210, 0x52c42e3e6887c30, 0x830eb1b274681a2, 0xa20d042de6b0834, 0x803c36100286990, 0x834cd0b8f81a060, 0x210e06928180f83, 0x5861a81b0b9d41c, 0xc30210186c20056, 0x20d0603610a480, 0xc3dce81a0c0fd46, 0xa5818080fc401a0, 0x4d0b8380c180c83, 0x28693c20a2acca2, 0x4080e4f0601c044, 0xd01ad8424d6183]
def page133 : List Nat := [0xbc25a218080789a, 0x9420d1a041666a0, 0x19070603e0d02b8, 0xd3258a6a0b80eba, 0xa3817921a87f230, 0x6e3985db2100d8a, 0x79cc4038500300c, 0xce0d00d9b830410, 0x3d0685c3817be5e, 0x801806020d1f542, 0xd6c180d061901f0, 0x950f83820180685, 0xe2901e0e351a5e8, 0xdc000dad9c8950, 0x351880c401c5204, 0x5f0bc050d05c30, 0x495590d0601c191, 0xb14f5693adb0783, 0xab8c3e6a3f03406, 0x34620d0382e054, 0x1c0b868761702a1, 0xf0680c1aa559c08, 0x300f1286c501b2, 0x2f0725c1e185c12]
def page134 : List Nat := [0x703c3819140353c, 0x8c8cf0400c62188, 0x8b310400c5602a5, 0x91a9040c0b81862, 0x301f620601a343, 0x750e05ee2c60731, 0x321440060b83834, 0xc8820aa8683f780, 0x2f0b8180a190c03, 0xbd81860327b8cce, 0x258184ca741410a, 0xf0180836300701, 0x78cdb0210d85c30, 0x2e4d08019460e0, 0x3010607e5e0d06, 0x2134d4170b8300c, 0x200d0200c0a175, 0x7e65864300d368d, 0x50bc1e0e0686831, 0x1a0401c4d96202, 0x186a34c32050d36, 0xa3203e160d3447a, 0x4200d078383c191, 0xcc0d382ca73029b]
def page135 : List Nat := [0x7060dec30706076, 0xc0c040181430302, 0x1b0786042106585, 0x801030e22e83c20, 0x950182210e500c3, 0xdb1107c2c100335, 0x81b81e040807c1a, 0xc300f02c0205013, 0x130d4a2532a2813, 0x8601e200f83438, 0x82e9a4cafc0a0f6, 0x86438858180801, 0xc0300817349a035, 0x6456348601ee40, 0xe068c6cc100788, 0x20683e9eae05c72, 0x1620c0197436035, 0x1f42820064a0b87, 0x806008690e2e434, 0xaca6710040343e6, 0x9a28a7840cd0398, 0x904042060d2649c, 0x460170280c20216, 0x10499a078171001]
def page136 : List Nat := [0x4322141035ad8de, 0x360e0200c446e0, 0x1a0d868381b0639, 0xd066f81869b440c, 0x5780d030093017b, 0x54518f1381768af, 0x89c96eb2700381e, 0xc6e0e03c50177, 0x18198640c1a1004, 0x38615d0f9407254, 0xec278650fc36202, 0xf0d87148100680, 0x1018341a0c1e830, 0xc301a2706306e20, 0x1a51b4830101f91, 0x58d0ba180687ea9, 0x5fc5b149f435555, 0xe61a3886c109513, 0x12058c0e3405c20, 0x41a5006810069c1, 0x70080387c170c8c, 0x22602e970733408, 0x13c1aa7038e0100, 0x1c0c474fc17a786]
def page137 : List Nat := [0x80719a200c06437, 0x860e0803c1a033, 0xe0c810401a6715, 0xa0642ed83c88020, 0x433022e0f9a21f6, 0x2208070356a07b0, 0x7b70d0040d0882e, 0xae4050c1a4d0bc0, 0x5a0c8c89a186a86, 0xa2d8b8a30180834, 0xc0a0470c1439065, 0x434081044d0680, 0x7011c41a221f41a, 0x450270c0c8364e0, 0xd17106c2e6a348c, 0x920c1ec85310130, 0x41a0325072df6e3, 0x1b1c060201a8eb7, 0x9ac42eb6399c02e, 0x8b63201de044175, 0x1a0f97d468b040f, 0x1878344d59862a8, 0x434070f94820210, 0x4e48bd83017083d]
def page138 : List Nat := [0xa83d0a84080b9dc, 0x968bb428299b684, 0x50c03ae2c6075c, 0x4a303e5f250401e, 0x42ee207964301a1, 0xd20f84030f25a25, 0x7018086e0d0c19a, 0x4100401ab01e100, 0xd0306006e4281e, 0x81f40c1a1087020, 0x4940801a701e180, 0x1806838e6b642b7, 0x5249c4ce0c5c128, 0x5a4680d8fc30177, 0x7d07ac2de1a01a1, 0xc0402e345fdb990, 0x18cc80d1ccde4d0, 0xe0211034660104, 0x78619c073128406, 0xc2e10032880a180, 0x870c07ea8190d30, 0xc060481a01d5594, 0x1be0f0f819b0202, 0x1e0baf0300f0db9]
def page139 : List Nat := [0x886132404d34c20, 0x8405e71040343e6, 0x3c0c32cd0050ba7, 0x587c0c611125c1c, 0x8b21007a7434700, 0x17352090ae40786, 0xe05c320d42840da, 0x1801f03321860f0, 0xcb0543e14c81484, 0xf374d00d019f93e, 0x818bb1f8400cb91, 0x430c0383e705880, 0x28663b1c4f1bc2f, 0x13e103734420060, 0x92378382e051084, 0x184042180c8d024, 0x1e06148602e0f0, 0x17068c81c330b84, 0xa2ac3057aa8ccd2, 0x82e0e078180a1aa, 0x10031b8de325125, 0xa068304c0c344d0, 0x56c0d0200c384f5, 0x28c1b81ec81a21]
def page140 : List Nat := [0xc1b99a205e95c08, 0x20060d070be1f0, 0x1b0c07836345106, 0x987c1e17bf1cc2e, 0x8361f0180834ed3, 0xf0701434ce0806, 0x22e8441a0f8600a, 0x42efe0d3882e054, 0x322e06c34020c0a, 0xf838360d01a1440, 0xd7c2f0c86c30690, 0x45f06968e20e03, 0x40d9cc79242481c, 0x840980305d921e6, 0x4019163e0f3d83, 0x811c2e0407b6010, 0x97e08532907c020, 0x6e08019441c2893, 0x738c2e0e0290146, 0x40c0f19038343f0, 0x60d394d2180803, 0x38346810033842c, 0xcdea8340e0dee23, 0xc71a0bdc60e069c]
def page141 : List Nat := [0xbb88341b0e03406, 0x300c03351a29c0, 0x190787106060d0f, 0x493430b65aca8b4, 0xc1c1a100c8380d9, 0x1b0d03c0a500b93, 0xfb602eba7f86864, 0x830aa0cca830066, 0x1b081dc1c041e86, 0x2864364f07b3830, 0x841516403c30170, 0xc306819080e1003, 0x483c3205399a02e, 0xafc1810038d20f3, 0x120d1e834100c01, 0xc8601eb00dc4c49, 0x301e100780c1f5, 0x3a08019461a8a01, 0x8128c41a0729c2e, 0x9a6d20b85c0a210, 0x96070f030080180, 0x200c369a731753a, 0x2781798ad8a00e0, 0x7864060210a0c94]
def page142 : List Nat := [0x286007532f06830, 0xc30034205c1c0d0, 0x3f3434830cd0e06, 0xc8380c362f389cc, 0x6f6d00c1007d7c0, 0xe4080c41a170e06, 0x58c02e0402a9030, 0xcdc1889892241a6, 0xebd9cce0d00286, 0x91155913893d034, 0xc0c050103d3c626, 0x8417b0c2e050da8, 0xc068301c07885c6, 0x8800d018fd5c1b1, 0x22710b01e100db4, 0x3390360f6e83dc8, 0xcbd3251b54360e5, 0x24f05d22bf0797, 0x99a81c200d3902e, 0x434181f89cea188, 0x1f4d06c3e0e0d34, 0xc868312b0d83c44, 0x2f4780c5f040ce0, 0x6d0d84056490788]
def page143 : List Nat := [0xd839241c0b83420, 0x9c40e022f90ad50, 0xc83d1a81c200d44, 0x45fadc342085c0a, 0xd56341603524cb3, 0x55a868360c0186, 0x60609a1c0ba102e, 0xc1e180680d8cb22, 0xfb7865d61f0da2, 0xd00c609f0c8d820, 0xdce21985c36100, 0x100cb34301b0186, 0x8a59281a7c86034, 0x2fe6e0c030403e6, 0x50518a420030b87, 0x28358e6f0703406, 0xc381ab4864201a0, 0x1c710360679b51d, 0xe388388342c18ac, 0x808e20d1a951052, 0x1a178801c0d2703, 0xd00d8c0e1b1b868, 0x8f0060686006e00, 0x5ebd42614c8080f]
def page144 : List Nat := [0x206034915f860be, 0xd21903d39901c7, 0x1a0786c40320786, 0xf93566184786c06, 0x460626181508104, 0x9e0d3742e384e25, 0x4a4c201c0b80eb6, 0x1f2f73489c301c6, 0xd83c88034ce1db9, 0xdae69c1a0e05c1a, 0x81f0c34a2c1e0d0, 0xf1f83a04200c83, 0x60061f4907008, 0x30080205c06961, 0x6b0e0bcde0e06a6, 0xa00dc8200203406, 0x9a87607a99c8351, 0x859a86820066903, 0x82c1180c70a1106, 0xef1770c01804173, 0x1a1d29946405605, 0x11f434f91903830, 0x8620e019a82ec81, 0x1a308782e061ab4]
def page145 : List Nat := [0xca91c2172daf5b8, 0x2e6f670410a200, 0xe4110d544b81f09, 0xe94c52566e06da6, 0xc4083100141afd3, 0x471164a13c1483, 0x3dc4214720c1c, 0x80a3b59860e4951, 0xd0200c38b16e86, 0xfa303c10c0215c8, 0x808a20d27c34404, 0x180791c54100701, 0x7836cb0b9d14916, 0x4861a6417968100, 0x1a0706536030b81, 0x9068e00c42216c8, 0x836330680da8e36, 0x1935038401a8982, 0x206a04940801866, 0x1c040606a02035, 0x1b0c065d5071184, 0x78801c0dbe1ac40, 0x4300f0d878a1591, 0x1a0d8417e1a0c01]
def page146 : List Nat := [0x90bc30050d9a532, 0x82019080189a271, 0x170680dc8202f06, 0x406834500c86874, 0x10b640d0181e693, 0x1b01b2cd0050221, 0x72d0301703069ac, 0x83017510d40d442, 0x68378696c171f97, 0x80b43e1a4006cd6, 0xc3f6c0c014089f0, 0x5018d438170300, 0xd1162756742411e, 0x9c60e0806807120, 0xc1bcb3034181db3, 0xcb88589a735e030, 0x92e3e4b05c20184, 0x2201a41f0d0da7, 0x701190b0518300a, 0x99c10078198e330, 0x9502a68e80f070c, 0xb91c4189206968, 0x88b13834149c1c0, 0x450805e91120706]
def page147 : List Nat := [0x680d00290c03c06, 0x8301b01a103e0e0, 0x1f6e8c5bee4105f, 0x705c377e0ba0035, 0xc201c028610a0f6, 0x1c0231430951800, 0x6dc61a0686006, 0x968560e0353b591, 0x1a1045c481b0b86, 0xba702e0565870e0, 0xcfc0801a701e1e0, 0x200f9cdc85058c0, 0xb01e0e068180a, 0xac0fac86c329e1, 0x1913860604e5a06, 0x1862dac8b784034, 0x8201a518408e170, 0xf06db5906eb7db, 0x80801c73638202e, 0x9732f0d26034e40, 0xc03009a4d10bae, 0x12f0041a0f8f030, 0xc90050203c08721, 0x71a0603c321087]
def page148 : List Nat := [0xd060353b078143e, 0xae1aaa86838060, 0x83905c3c06af55, 0xc32124c00c040bd, 0x5e0e06008002b3, 0x620786cfc0e718c, 0x79f8fb524387c70, 0x344a0bb7174180, 0x18258c8b20e022d, 0xa8602e107b57c2e, 0xc250d03808cd7, 0x1829a20aca00184, 0x538c9a197206166, 0x4f817080141e069, 0x100300c861c0b83, 0x185d3a10031a438, 0x3f00811ac34190, 0x34a8380803aaa3, 0x403c1a6f1985c34, 0x361a018801c6e3, 0xf1d0fcd4625186, 0xa938340f6086669, 0x53e1a1900cf0185, 0x4a0785c44100b81]
def page149 : List Nat := [0xf87044340d06d62, 0x86b670bdf836180, 0xf06880320e508f, 0x78d944e21a06ac6, 0x8340e2e87c0c020, 0x60c1c0dc203f18, 0xb0819c10178603e, 0x4de186c03408035, 0x60c49cd8cf0681, 0x1a901f550d07ee6, 0x21c1a0e0381a040, 0xdf0dccc06a40d4d, 0xd06018f8138c830, 0x9ccb361835460e0, 0x185da0c682d710d, 0x80cc201875b9468, 0x1404081542e033, 0x1e0b8400c963529, 0xb8380a214320c0c, 0xeaa8807830e6680, 0x54558d0ba180687, 0x1caa52314c25c31, 0x3e1aa98d0305c4, 0x8c0f04068915f86]
def page150 : List Nat := [0xeb20a00a7b06cd6, 0xedcb06e03d00053, 0x780f019a4180283, 0x89a01ad20c589a0, 0x212030d060203f6, 0x534835ac210fc2, 0x31121a0c8ec20, 0x5c8d214a30063f4, 0x40187044050821, 0xc05c1c102f9401a, 0x34b60605e4cc70, 0x80d060336471b9, 0x50113e10aa0d020, 0x92c200c8601a1f9, 0x1a080193c1a0c36, 0x91a5f8fb0d060d2, 0x864300197031011, 0x1c0186820b00c01, 0x9905aa1702dc834, 0x1e060e200340c6, 0xb601034065060b9, 0x8b199e1f399b830, 0x34180797c3f72b, 0x10b1065a2780811]
def page151 : List Nat := [0xc034184eb5c28dc, 0x8660d969c060100, 0x20643181a5c1003, 0x232035254f1893c, 0x1c61f4185c1c050, 0x131206a248201b9, 0xc1f88a10560600d, 0x42e4e0e019c8e20, 0x1a1c0a01e0e468a, 0xf8e03113908e1a4, 0x81a0f021ccdc170, 0xcd103205ab40803, 0xd040340f0e05c1e, 0x81ee47805c0d040, 0x691a06986200d83, 0x8018341c1b38dc4, 0x8c4c3068393e9e0, 0x1f85a2c1e9e070a, 0x80b5c4100d32036, 0x1f21f0c870341b0, 0x2806a1400184207, 0xc0183e1a10434d2, 0xdc87304194302c0, 0x1ab51341a03c1b8]
def page152 : List Nat := [0x84fc1a32b49ed5c, 0xd501c0b83c361c0, 0xd41105dbe170107, 0xe1898746068101c, 0xd32d34d141c8384, 0x180400da8e44e05, 0x1f6e4302706162, 0xa61715db19b6184, 0x18079d4bc9e4f86, 0xa8d034a82ea4450, 0x808d00d3307218a, 0x7d0807c377c3683, 0xf05edac8b7db81e, 0x8a80f0c04184060, 0xf170643e0dc125, 0x306842100e08430, 0x106343c2d0301c0, 0x1e6406430d21087, 0x78103e100786c5e, 0x4397e670e4354c0, 0x1b5338c2e407086, 0x786c330c34af01e, 0x91610030a93c180, 0x1c08018381a8e1a]
def page153 : List Nat := [0x203dae7e0680c2e, 0xa6933381b81e857, 0x11312517626884c, 0xd03c400e0608035, 0xce0366705c0ae30, 0x354f8c020181800, 0x70c56c4d5a0716b, 0x946c507060e66f3, 0x1f0181420a30701, 0xeac5160824b7868, 0xc2f1c4f12830b18, 0x1c06a98340601b1, 0x681832e40c20cac, 0x2f21815de1cce32, 0xd526062e41c1f86, 0x422c180601a701e, 0x9c41e0d868e6381, 0xd07084846a709a, 0xc1c080851d05d86, 0x63a6f1f8653d79b, 0xb45e03c0c0d0f83, 0xd00c341702b8c36, 0x5ca3234c341c1b0, 0x1a0c034081c0c4b]
def page154 : List Nat := [0x806aa8010f88838, 0xd2c5602d5468180, 0xe20d0141e191f85, 0x1a2c1c0d2705c0a, 0x41c1a0fb280e624, 0xb99b841a40e8986, 0x51dc381ab48401c, 0x4600c0200d4885b, 0x3021cc2ecb3425, 0x53d834035b1a010, 0xd683027061280f0, 0xf86c3064690786, 0xf05d081aae27830, 0x392a1b06066194, 0x170e300c61c0bca, 0x88d09c2c07b4884, 0x83418050782e362, 0x52a06a3ecd0bb6, 0xc06696e3720682e, 0x806960c211860e0, 0x55d06934310b83, 0xd8404a1b082d02e, 0xe0870c8402e051, 0x1003134de793804]
def page155 : List Nat := [0x595820066181462, 0x1c06a286ab2964, 0xc0c86d3ca30c04, 0x5a800a9208085a0, 0xe88730f815a2186, 0xf2f97a00490806, 0x83c0ca9072457e, 0x2e19688f4309e2, 0x17080c8361a061c, 0xd842d64f268193c, 0x8335c0bd09c61a0, 0x21985c602001b5, 0x186c3c1a5eaf00c, 0x81a2807b802e054, 0xf21174622f5183, 0xd05d50bf2b35430, 0x83520028600a020, 0x50d8407e100327, 0xd0101a03698701e, 0x66c6d0701808030, 0xce0e094c4945dae, 0x1814084d0203406, 0x41c500c2cdc20d0, 0x6080e0c41007b7]
def page156 : List Nat := [0x486436c0100381a, 0x406a40d40a1a203, 0x6a0e214801a4ac0, 0x80381a04019c01f, 0x81e030d86020781, 0x541a04034183908, 0xa8882e03252c42f, 0x40a040680d665f2, 0x1707014d6100313, 0x48686ce67113da4, 0x1a320b8400c053, 0x56906038040186, 0x9061901f961bc20, 0xa0b44aa68d6106, 0xe10801408620d1c, 0xdd38a0063703c40, 0xd045f0324030470, 0xe20cb840a040680, 0xe1b81e4e18061d4, 0x420731c3b018064, 0x1b0e069b21a0c08, 0xf21a437a5008430, 0x7fe8510dfc1410f, 0x10fd102217c3548]
def page157 : List Nat := [0x10caf6a098ffd08, 0x50b31be1aa217d5, 0xff42487fa8610ff, 0x5d45430bc82e87, 0x2657950087fa432, 0x6b21ff94843fea8, 0xf28083ff434c6fe, 0x3fa2b187ec1743b, 0x20fc82e87ff150c, 0x50c3fa86907fd06, 0x4c440f799465771, 0xf7318c7fa87997f, 0x5f45740bf28065, 0x8617f53503fc65a, 0xa0995f11531be8a, 0xea0e617c454c3fc, 0x6fa6b905fd4520f, 0x10be8ac65fb504c, 0x50c6fc6b105f494, 0x49631fd200617f4, 0xfe32107fa2ba1df, 0x157d4d40fe99621, 0xe43fe32903fa0ba, 0x60087e0c120bf82]
def page158 : List Nat := [0xb8a861f531443f6, 0x7fa64907fc5630f, 0x20fe988617d2590, 0x24c2fca0215fc14, 0x4d710fe8ae65fd4, 0xfd214c2fc6b085f, 0xdfcd440bf9a841, 0xe41fc420c7fa0ba, 0x85987f8c640be8a, 0xc82c657d35843f8, 0x7fa86987fd0b31b, 0x32ee21c61f8504c, 0x5883f661185d457, 0x8d510fe21261fd1, 0xff430cafea4a1df, 0x7d4c431fea8887, 0xe41f9400c3fa62a, 0x64997f4ca21ffa1, 0xf1aa417f35907de, 0xefa4b885fd1532b, 0x31bf82c637c5050, 0x1c87ea2a185f117, 0x50910fea1243f63, 0x7f35d07fa86997f]
def page159 : List Nat := [0x7fc8440ffa1c63, 0x83ff31483fa849, 0x8a217f90d20fe19, 0xfa1a217d25102fe, 0x2fa6b207f4c941f, 0x32be29a85fe32cc, 0x2902fe6a10ff517, 0x45732ff18881fd3, 0x7f35c42fe6b90fd, 0x87fd0e32ff10861, 0xe657715ccbfc621, 0x6390ffd0c10be8a, 0xe22a217f35c83ea, 0x6fe6a18dfcd432b, 0x31be92e63fc428c, 0x2106fa4a20ff10e, 0xd4542be9ae43fd3, 0x7f45887fe6ba15f, 0xffd0c21bf82e65, 0xa41fd430cbf8879, 0x6b087fd0e21fe90, 0xea2e63fd424cafe, 0xbf843207fd1532f, 0x31ff19063ff514c]
def page160 : List Nat := [0x1903fe85997fd08, 0x50a31ffa1e61fd3, 0xfc43086fa4b987f, 0x5f0d620ffa1c61, 0xc617f35107fa64a, 0x2ba15f45420ff90, 0xf99221f7314c7fe, 0xbfe4a187fd0530f, 0x20fea1c657d358c, 0x5d0efe0a187f10f, 0xd4540bfa28657f0, 0xfe43c87fea098df, 0x7fd0f31ff10c81, 0xe85fd43442fe8a1, 0x6a10efd0e43dea1, 0xe92861ff32886ba, 0x3fa62985fc1641b, 0x10bfa9263fe4344, 0x2d03fa8618dfd14, 0xd0a20fe98c41ff3, 0xfd32443fa85997f, 0x17fd0d329fa2843, 0x617f458cafe6ba, 0x2b995f4d620ff19]
def page161 : List Nat := [0xe92c21fd328c7ee, 0x3fa8710f7d0c30b, 0x20fe99021ff4148, 0x58c3fc8718dfcd6, 0x11532be8ae617f4, 0xfd320c7fe6ba0df, 0x97f10d32fea2a65, 0xe41fd43cc2f60b1, 0xa021ff41743fea1, 0xe9a821ff328c6fc, 0x3f864a07fd0932b, 0x41fe92c617f058c, 0x50cbfe86185f497, 0x8ca41bfa92813f4, 0xf830883fa4ba1ff, 0x7f4ca10be9a885, 0xa63fd438c7f6611, 0x65987f4d741fe22, 0xe90a817d35103fa, 0x7f86518df49643f, 0x32ff992413d4508, 0x50afe0b197fd41, 0x10e32ff8ae657c5, 0xff32486fe6a087f]
def page162 : List Nat := [0x8df14121bf82e83, 0xe837f45c87fc841, 0x4b207fc8730be9a, 0xe8ae877f45ccafa, 0x6fc6a90ff8c620b, 0x20fe19483fe428c, 0x14cafa6a20df0d5, 0xd0d21ff21843fd5, 0xfd5210efe8b98ff, 0x8774cb31ff21e41, 0x861fe5110efe8b0, 0x65887fc9630bfa2, 0xfa28437c504cbfe, 0x6fe0ba16f50c43b, 0x41ff992837f454c, 0x3103f88690ff4cb, 0x8c930bd82e87bf4, 0x7d35887fe42987f, 0x7fc8640fe21e21, 0xe81fd43c42fa2b1, 0x2ba17f10d20fe98, 0xe90881ff424c7fa, 0x2fca018ff88620f, 0x20bea88857d35d0]
def page163 : List Nat := [0x4c7f883107f486, 0xcc932ffa1e437c5, 0xdf324c7fa65107f, 0x87fd0910fb18a21, 0xe43fc428c3f8841, 0x86105f89510fea1, 0xea1a437f4510ffe, 0x3ba6498ff8ca30f, 0x40ff21a65f83004, 0x5903fa6ba17f4cb, 0x45430ff8ae877d1, 0xfd328c3fe6520ff, 0xcfd1730be8ac85, 0xe637c45ccb7e84a, 0x869877ccb31fea1, 0xfa8a65ff324c7fe, 0x3fa8498ffc8540b, 0x30bf82c85fc42c4, 0x5c42fe8b987f4c7, 0x4d631fe990617f4, 0xff25d0ffe42185f, 0x85fd49309ea2e61, 0xc63fe32103f8421, 0x63887f10810bfa2]
def page164 : List Nat := [0xfa8a87ff430c7ea, 0x6fe6ba05fcd642b, 0x30ffa2e657c5050, 0x18c3f842207710c, 0x11532ffa1261fd3, 0xfe454c6fa2a207f, 0x87fcc841bfa9283, 0xe85ff428c7fa4a1, 0x8a21fe88210be8a, 0xf8ac41fd434c77e, 0xbfa85987fcc740f, 0x20ff99281fc514c, 0x20cbf260185f4d4, 0x10d31bea9087ed3, 0xbf4350bfc64a07f, 0x8dfd1720fe99663, 0xa417f45882f0a09, 0xa0995f94021fe98, 0xfa28837f05887f8, 0x77a86207e48210b, 0x42be92e87fd3248, 0x5d0bf843185fcd4, 0xd0e209ea28657d3, 0xf531086be6a10ff]
def page165 : List Nat := [0x5714d40bfa8a61, 0x4437c53503f8821, 0x42207fd0f32fea1, 0xe99263fd21d03fc, 0x2fe6b207f8ca31f, 0x41ff90e81ff4384, 0x5842fa6b20ffc17, 0x49740ffa1e217c3, 0xfd32907fe84185f, 0x87f0cb40ffa1661, 0xc877d1590ff4819, 0x6b215f45630bf82, 0xf18c617d5110efa, 0x37e87a15f11521f, 0x31bf82e63fe42cc, 0x3507fe85887f90d, 0xd0b41ff188417c5, 0xfe514cbfa8418ef, 0x97fd0a10fd82861, 0x863fc32c43fc871, 0x42185fd4d41be92, 0xe990817d35087fa, 0x7fa43985f11520f, 0x30ff82e87ff45cc]
def page166 : List Nat := [0x2d07fc64087f4c9, 0xd4d42ffa0e61bd4, 0xfc43443fa82985f, 0x7e0c310ff21e21, 0xc437d258c3fe62a, 0x8710ff14131bf9a, 0xf10c61fe454cbf8, 0x7fa43187f8cb10f, 0x42fe20861ff32d0, 0x18c3fa82907fc17, 0xd0e40ffa1461fc4, 0xff410c3be87186f, 0x87f90930ffa1a41, 0x621fe43887fa858, 0x83187fd0920ff21, 0x1eb80045e003fe, 0x8000000000100, 0x42e20013d800, 0xf304081c0, 0x300000805800000, 0x1c800000b8c0130, 0xe00072a000, 0x303680f00, 0x4c4802000574010]
def page167 : List Nat := [0xcdc00000000f2, 0x60001e4fa8210, 0xc0000000000000, 0x4956480004cf, 0xba6d00cead22800, 0x107f8027caf6cd, 0x200800000095000, 0x298000000cce880, 0x1, 0xcf004010000f900, 0x2, 0xca98c001b300000, 0x8000000096b8003, 0x10000004460015e, 0x709530000, 0x26a00002000, 0xce9ef0002bc0, 0x9abfc001ed004, 0x6ca150000080000, 0x6000ec9d5000021, 0x40040083b9b913, 0x1a5a1f000074000, 0x4000013d300801, 0x9cd0000007b8000]
def page168 : List Nat := [0x20c010000106b, 0x5a20280040b67a0, 0x8001fb, 0x0, 0xf00000202800000, 0x105f00c28c0508, 0xeed528800000334, 0x80000027f27, 0xdd099f000001a68, 0x2ad02821, 0x4d20005e9910, 0x440000a00000000, 0x100100a000f, 0x175, 0x6f4e38220000000, 0xf77e0084c857000, 0x18f0040100db4, 0x1d180000c000, 0xc00, 0x7004000000000, 0x180000000002400, 0x4000000030430, 0x40f00803000, 0x0]
def page169 : List Nat := [0x58000000014c9b1, 0x1f1004000c, 0x30ea840025f004, 0x26bad0200000100, 0x34ca3800000001, 0x2010354bc80400, 0x3000566000000, 0x20000000600000, 0xb8d00c010001ad0, 0x9d83afb51e00176, 0x112bf9000e, 0x91c00000, 0xc70100000, 0x7de00001000616, 0x338060040012780, 0x600000000000775, 0x9682c0b, 0x469c000, 0x661a02, 0x859c000000, 0x188380200000000, 0x5be6a4010004220, 0xb80074a214ab800, 0x31f]
def page170 : List Nat := [0x4, 0x8000001ab80, 0x2001ef8002b2000, 0x2aa0ec002316f, 0x1a380201880c000, 0xec59080000000, 0x80020a534000000, 0x6a2000ed, 0x4120009e8000000, 0x4712b1400000, 0x60000000, 0x600000050800000, 0x498000000008880, 0x6fdcb800432000, 0x8000000018d00, 0x100000600002000, 0xe00006000028000, 0x50000200000, 0x380001a0000c, 0x2200010000078, 0x180000b8000500, 0xd8000680003200, 0x7c0003c0001c000, 0x400021000100000]
def page171 : List Nat := [0x40828204080004, 0x404182020808106, 0x120c10903084808, 0x1050c0820604082, 0x810604403020c18, 0x183120a189030c4, 0xc191040c8818624, 0x100820804083220, 0x8240c4120420105, 0x220821103104828, 0x90410c818864084, 0x832204144320a21, 0x392020c90104440, 0x69090148087a404, 0x4c0812424192120, 0x604193020a98104, 0x120c989054c481a, 0x1044c881a644053, 0x812644393220c99, 0x3d4020aa0104500, 0x6a090550481a804, 0x508872844114220, 0x8640d43204a1900, 0x20aa190550c822]
def page172 : List Nat := [0x1068808242041a1, 0x81c424062021d10, 0x123020510906884, 0x3181068c082c604, 0x8c481c6240a3120, 0x644063120d18905, 0x220d191048c881c, 0x1059008248040a3, 0x82c8240e4120520, 0xa4220921103904, 0xb2190490c81c864, 0xc4082e2040a4320, 0x404131021f88106, 0x120790901c80836, 0x104cc08164241b2, 0x81e6041b3020b98, 0xf3120d98905cc4, 0xd99106cc8826644, 0xd008268040b3221, 0x8241741207a0105, 0x221da1104d0881e, 0x903d0c816864034, 0x68641743209a1, 0xe00a8088070020]
def page173 : List Nat := [0x1a8178140128100, 0x2c02982782301e8, 0x3a8378350320308, 0x4c0488458428408, 0x5905785585084f0, 0x6906706486285e8, 0x7c07987587206e8, 0x8a08788388287e8, 0x9a89889589188e0, 0xae8ad0a90a389f0, 0xbd8bb8b80b50b18, 0xce0ca8c48c10bf8, 0xe08de8d98d68d38, 0xf58f10ed8e68e40, 0x69010fd8fc0f78, 0x1591290f90a9089, 0x2491f11b1189169, 0x3513393092c9281, 0x4494314093b9399, 0x5515294f14a9469, 0x6295e15b9599571, 0x7797296d16a1641, 0x8c18818497f17c1, 0xa119c9999961901]
def page174 : List Nat := [0xb39af1aa9a81a39, 0xc71c19bc1b91b59, 0xd71d41d01cd1cb1, 0xe89e39e19dd9db1, 0xfc9f89f39ef9eb9, 0xd207a052029ff1, 0x24221a1b2162132, 0x33a3222fa2c22a2, 0x4a245240a3b236a, 0x6225f25a254a502, 0x76a7327026a267a, 0x86a82a7fa7b2782, 0x9a29629329028c2, 0xacaa8aa52a029ba, 0xb9ab82b6ab3aaf2, 0xc8ac52c22c0abc2, 0xd9ad6ad1aceacca, 0xf02e9ae7ae3adea, 0x2b002fc2f82f42, 0x15311b0c30a3083, 0x22b20b1f31c317b, 0x3432f32bb293273, 0x4634333e339b363, 0x59b55b52b4cb4a3]
def page175 : List Nat := [0x68b6536335fb5cb, 0x7cb79b75b7236d3, 0x90b8b388b84b7fb, 0xa1b9f39cb98b93b, 0xb43b03ad3aaba63, 0xc63c33c03bb3b83, 0xd93d5bd13cdbc9b, 0xecbe8be43e0bdd3, 0xffbfbbf7bf43f0b, 0x12c1140dc0ac073, 0x20c1cc1a4184154, 0x2dc2ac274264234, 0x4043ec3d436c31c, 0x52c4ec4ac474434, 0x65c6345e459c554, 0x79476474c72c6bc, 0x8c485c83c80c7cc, 0x9b498c96494c904, 0xb04abca94a449f4, 0xc34c1cc04bbcb64, 0xd84d34d14cd4c74, 0xe8ce6ce3cdecdb4, 0xf5cf2cf14edceac, 0x6d034fecfbcf84]
def page176 : List Nat := [0x19513d1150dd095, 0x2e52ad28d23d1d5, 0x3ed3c53a5375325, 0x4d54b547d45542d, 0x5fd5ad56551d505, 0x72d6dd6b566d645, 0x83581d7ed7bd765, 0x9959458f58c588d, 0xa85a3da25a059d5, 0xb9db6db4db1dacd, 0xc75c3dc25be5bc5, 0xd3dce5cd5cb5c8d, 0xe65e45dfddbdd8d, 0xf2df0def5ed5eb5, 0x6600dfc5f9df6d, 0x1de19615e1160ce, 0x2de28e27623e216, 0x44e40e3b637630e, 0x5164de4b648e466, 0x64660e5d658e546, 0x72e7066e66a666e, 0x8368067e679e74e, 0x9769068d6896866, 0xab6a9ea3ea069ae]
def page177 : List Nat := [0xba6b56b3eb0eade, 0xcceca6c76c2ebe6, 0xde6d86d5ed3ecf6, 0xf86f3eed6e8ee3e, 0xa703f006fe6fbe, 0x1d719713f0e70c7, 0x3372d728725f20f, 0xa3e220a8a02827, 0x9a1be9c08863fbf, 0xa3282088b0a8a0, 0xa0b070302159706, 0x8a03070a8c818a8, 0x2000a0286450b01, 0x301928b0a07030, 0xbc68a828a478b07, 0x8a890a2e91af2c2, 0x50302bb88912e4e, 0xc60701a1cc8acd8, 0xa2203a4868b0a89, 0x2108863b3aa18a3, 0xc0a26890c828182, 0xa1d0b1d870a278, 0x20a091c061d9d03, 0x254fcf248703060]
def page178 : List Nat := [0xa0730070a09a5d0, 0xb40a8a018a8c090, 0x61286898ab38b34, 0x980cf0907130c8, 0xa02ae0a8a0a8b46, 0x822e9f4f0b09088, 0x60a0b028a36868a, 0x980201990725988, 0x8ae888b490a2524, 0xa370b020a27af4, 0x70b0981800a8b, 0x8b09070a8a4b38b, 0x9098301b9b94aa6, 0x3868a8b06028a0, 0x8c1d0b07248702, 0x8a818a0c8302018, 0xa8a860289870a27, 0x9ab45cb86450a2, 0x703090982818b0b, 0x86450809248b0a0, 0x207058302010002, 0x8a01870e888a8a0, 0x70301008034888a, 0x938a030289820a0]
def page179 : List Nat := [0x301370988821280, 0x4f8a09070287058, 0x9b91ac7ce8b504f, 0xcc273889070a8a0, 0x7b88c090a268cb9, 0x870d898301c12, 0xb01b9bb0a4d4c8b, 0xb086028a393a8, 0x28b2089930a8183, 0x248a0b460ac50a1, 0x6340a8a12868a82, 0x28b2688b4928c8, 0x79fa71f0c090684, 0x68a898d8883022, 0x20201939306098a, 0xa828a25a5129, 0x18031070b0a0181, 0x4c89088b0a2b8a8, 0x1820a0b0ca3a32c, 0xa8703028a09020, 0x20a22a182810a06, 0xc3b38c090886028, 0x80b0a8286a22432, 0xbe8587460687024]
def page180 : List Nat := [0xb808b0d06028201, 0x1b15070a8a1b8b4, 0x7898a060289964d, 0xa459b373b0c81b, 0x3451bcc8b030746, 0x982818b0a8a099, 0xa8346c78a070b0b, 0xa301890a4d4c8d8, 0x28a80090a0b2423, 0x878125060a0a8a1, 0x888a8a460a8986, 0xa1b23c381b19e3, 0x4a31bcc8b090724, 0x703340a09018b3, 0x28201810a8d8c83, 0x170b0717d00a050, 0xc0b1d9d070a4f83, 0x860a25898b080a1, 0xa098aa5288a8929, 0x32e0a07500c12a, 0x282088b424f8b09, 0x83020a028c8a333, 0x603348a09890182, 0x1808c090c87070]
def page181 : List Nat := [0x30b888201820150, 0x860280030a07068, 0x107060a000a8a09, 0x82370b00068a828, 0x21982a208a50689, 0xa0a8b2ca1ab8a8, 0xe0b0885028a2789, 0x7060a2f272ea6a, 0x7030a4f8902963f, 0x1937b7504f0c898, 0x107060318c38a43, 0xab828b088abb2, 0xf8c0a098b1f2c0a, 0x8a8a0703171ac79, 0xfbe8a17cc489a16, 0x8a8b073f1f088b1, 0x70c8a068302cd4c, 0x18c2b82011f990, 0xe2d09060302070a, 0x8a8a09278b501e4, 0x6028200830a26aa, 0x39450c0b38c58a0, 0xa06021d830a39c6, 0xaf488d070b08c90]
def page182 : List Nat := [0x78a070302820a27, 0x273a0b01ba88bb2, 0x936b58c8703188a, 0x28a020c8b0a371, 0x182068703014886, 0x8858b098703028, 0x9139312320681b3, 0x38cf0b07030a500, 0x30c928a09b9cfb9, 0x37098a023793b71, 0xf8a870302000a0b, 0x2550018e8c870a4, 0x18286a486820106, 0x8b07070302098b0, 0x148828b0a069881, 0x7030a0b0703020, 0xb3689070a8a1b8b, 0x302818a0b37cd1, 0xdcf8c87379d0a05, 0x9a88a2098702371, 0x90b0a03070c8685, 0x90602a79a268a8, 0x30a8b07058301a7, 0x8b0a83070d86800]
def page183 : List Nat := [0xa068089870b4d4c, 0x11cfd00600348a8, 0xf1c1089030a0987, 0x74386020a441dc, 0xf178a501d1c9c43, 0x28e2188972e8b2, 0xb4fa0221f8c0a00, 0xb2090a088709b30, 0xb0a8a09d01d4f4e, 0x50a028b2788870, 0xa0b272c26ab8a89, 0xa2785090c87478, 0xc818a3b1189a68c, 0x3989b9158a020b0, 0x50a8b030a070c96, 0x3028a0b08964c9, 0x58a48cd484c8a85, 0x253a0201bb3a862, 0x54f8703018a8a0c, 0x828a3737ac5045c, 0x9a5cd36ab8a8908, 0x302810188868b8, 0x31107118a1d9d07, 0x8a890a1cce908b0]
def page184 : List Nat := [0xad034cfb4070301, 0x27a693088100068, 0x88b0a892908a98a, 0xb482c787020a272, 0x30906c4063405c3, 0xa0a8286351333c, 0xc8a8301070d8700, 0x20a0b000a0b4d4, 0x30a8a060c491e8c, 0x6930aa3cc0901a, 0x7a7268a0b12818b, 0xa8a39af0908872, 0xa27d0392eb8ae0b, 0x9d424f0b07429d8, 0x70a338634b40a0a, 0xa0287060280138, 0x30b098c0302018b, 0x8c09068582098b0, 0xe0a06023fc425a4, 0x8b33099dbf43beb, 0x647cf8a3b3a0a08, 0x870b0ad00907470, 0x906020a2e0a8a02, 0x83070a8daf1e4e0]
def page185 : List Nat := [0x9828203070a0b06, 0x8c8ab33282088b0, 0x982870201269306, 0x238c09890a030a0, 0xf9e06021ebe8a24, 0x403028201810b3, 0xe960a0a07020a85, 0x98ac80a15af0ca, 0xa0b4b48a688870b, 0x8b088aa5b102018, 0x8cd308a05030281, 0x482b8a828a0b490, 0x29e890c0a0b48ac, 0x90987028227a68, 0x6cf0b088703028a, 0x97870a27d04fa72, 0x28b07060302823f, 0x130a030201808c0, 0xa8a13b992b9018b, 0xa0706028201a38, 0xa0b2709014888b7, 0xb7a7b726b688828, 0x681940a8a8a0b09, 0x2d89088a0b2eb30]
def page186 : List Nat := [0x20acb8b2f4fb2ae, 0x27818a0c9a0a070, 0x30201c5968a868f, 0x3f8cb7bf0a07060, 0x6898b0a070ab7, 0x28201808c1d870, 0xa0ccb8a8b0d0603, 0x509278c96278b0, 0xd07279d8a268a8a, 0x8a02a71c0b09089, 0xf452eae460a0b0a, 0xb094f0a42af45a, 0xa830a4f07422eae, 0x70a504f8b89890, 0x88b488a06028035, 0x8a820a4937b7270, 0xa0285030b088702, 0x8a274d26cc8a890, 0x2868aa9170b2997, 0x8a0a92060180131, 0x1b3070b338cb434, 0x8193128a8a06840, 0x3098b070a02d04f, 0xb93c868101888b8]
def page187 : List Nat := [0x72738890a8a09b9, 0x8c834fcf500a090, 0xb0281930a8a494e, 0x189278b0702928, 0x788b0098a0b0582, 0xaec60b0ac5898a2, 0x72f4fb6ae0c8a37, 0x824a58a090b25b, 0xa4b8a868b0d1d0c, 0x8b08c6450c45a68, 0x28224070a27a744, 0x8602822228a1860, 0xd8c8a0343320a08, 0xb7170a028201810, 0xa0a898302823797, 0x1fc88c028b09888, 0xc0989458c8a26c9, 0xb0a828a278b0, 0x88a06008019030a, 0x8a4937270d088b4, 0x6d01d390b07399d, 0x2888702c6820a8, 0x24921c802498a36, 0x8a028f3a87060a2]
def page188 : List Nat := [0x63d8b060280010a, 0x60287153d0a8a1, 0x9070b0681808c4d, 0xa45898581aeb78, 0x30a4644130c0602, 0xa070d82014c8c8, 0x70b060302018c50, 0xa0985830200478, 0x9090637b10881b7, 0x8b0207058301b73, 0xcb6bd0a890a37bd, 0xc896bc0a8a1717b, 0x987060313018986, 0x88582822589070, 0xf27a6948a09020b, 0x913e9c0b3f8a11b, 0xa0887060282224e, 0x504fcf1c2109218, 0xa0c0301cf8b0a07, 0xbf8a1c0c9d1d870, 0xc8a0b3f420b01c2, 0x70a4a8a070b0a8, 0x86870a9d8c861d, 0xc88a340b348a0a8]
def page189 : List Nat := [0xa8a4941268c08c0, 0x898282070600130, 0xb10070a030a0680, 0x80070b0603003, 0x22a8a8a490b0c09, 0x8a09070a8b48028, 0x20a1c27a72682cb, 0x3218887061d9d2, 0x70a01870a1ccea1, 0xa4230c23b88a138, 0x424348c090a2389, 0x705830189098b4, 0x9dcf0c87411d0a, 0x43063ac38a3b444, 0xe8a87000a8a0b3a, 0xaf40ae0c894f0a2, 0x54a4b09070a0a89, 0x8871f829c8a25a, 0xb0c870d9d1f4f0b, 0x248925870a0b020, 0x8214d4c8d8a8282, 0x8706030282018a1, 0x9888b4a3a433208, 0x9098a8a8a09b30]
def page190 : List Nat := [0x2207028606028a, 0x818a02c00886858, 0x882818a89a23131, 0x4450038b0a8a0a0, 0x30903438a064f87, 0x8b02888a1dcf4ec, 0x18b088a4927a748, 0xa0b3127b0a7028, 0xb0c370b0a023682, 0x818b130a8a05028, 0x683348a9b929b06, 0x2f1bb41b0b09070, 0x3ae2d89062e8a44, 0xa068503018b504, 0xf83018f8b100750, 0xd04f8a894f0a074, 0xa2da24e86030180, 0x21ce8908862f2e8, 0x4b934018b0a092e, 0x8a8a02890b3539b, 0xe0b08bf3fa78a12, 0x88874b0a8a26a73, 0x70da7a74a0b094a, 0xb4d4c8b0a86830]
def page191 : List Nat := [0xa09894f87000a03, 0x868ad02ecf0c860, 0x70a490c920b1312, 0x82818a09483c0a9, 0x2863527a7340b08, 0x87068186800a830, 0x1070a0d870a8b09, 0x62ec78a1d88820, 0xa0c010a0b25af47, 0x820b0a23a30a818, 0x5830282000b4925, 0xa0602442989870, 0xba489020a8a258b, 0x8a07411b9b0b2c2, 0x98a0180030b0a4c, 0x25a524c4c6458c0, 0x706030289868187, 0x92930a068282018, 0x7a7120b09088193, 0x3020009248a0b2, 0x1c4060592c39307, 0x713b4924306820, 0xfcf0b8b090a0350, 0x898a09868301af4]
def page192 : List Nat := [0xa93098703012388, 0x990a108b0191868, 0x918b8b80b070301, 0x8a8302808209873, 0x3820a0b248a1b8e, 0x987158c964f8a0, 0xb0a02000a830b50, 0x938701868282030, 0xa00030b0a060289, 0x8a8a5048c90b088, 0x70301990a109880, 0x60201890a4a3a0, 0xb2b8a0c3525b4a5, 0x8ca3a34d0a89088, 0x5268b0c0a09279d, 0x258b001e870a0b0, 0xb3f2488070a8a09, 0x970a0c8681830a8, 0xac91a480b07028a, 0xc920c819293068, 0xc8b0a890a031b87, 0x858044070b37b6c, 0xa318281b08a8a06, 0x86020a258900070]
def page193 : List Nat := [0x98a2f252eae248a, 0x898a088281018a8, 0x68b2b8acb47070a, 0xcc645c52c4c888, 0x6948d0a0909828b, 0xa6088b09c90a27a, 0x702028a8b0a29c8, 0x90b0a01898a8a0, 0x20181279d870c8a, 0x61d87259d0a028, 0x90a39a9b8a51c09, 0xa832939260b0a8, 0x7c78b0a0b0a0750, 0xa068982818b072, 0xb0a070a83928a8b, 0x9f8c090682098b4, 0xaa68c8a028a09a5, 0xb0a8a09a78b130, 0xa8a0b0986cb8a83, 0xa02029488830a0, 0x70ca227a6a18928, 0x28582018150490, 0x9828249070b0a03, 0x908901918a8a348]
def page194 : List Nat := [0x58282018309070d, 0xa8a0b0a0302860, 0x4fcf01b088870b, 0x86898b098a02825, 0x9868301898b0a24, 0x3087101a0a1a8f8, 0xb060289830186cc, 0xc90b0a333282088, 0x218d04f89074888, 0xa1088703328a0b3, 0x602820aca21993a, 0x2232c3a10a08870, 0x7a6a4828a02090b, 0x38810a09890b25a, 0x21c858306b9b7b9, 0x2f860a098a86028, 0x70acb09d04fce07, 0x80048c0d44430a0, 0x182890983020a8a, 0xa074f8c068a8b0, 0x98ad0408c89032e, 0x93070a86814b088, 0x20d8b0883019286, 0xa890a278ccd4c9]
def page195 : List Nat := [0xb0a870a0c3926bc, 0x8a45c54d0883018, 0xa174a8b070acb16, 0x2000a030b09c60, 0xa8a0b060280030a, 0x89030b0a8287000, 0x20025870a0b0201, 0xb7348c8901b40a0, 0x8c1a9b86073537, 0x30c50070682018, 0xb0a45bd0a8b028a, 0x2b4060a8a3dc50, 0xc253e063fbf258a, 0x2b8a088340874d0, 0x7b70f8a02030b0a, 0x2c16010c070b103, 0x7cd152b8a88958a, 0x268d0a09098b08c, 0xa8b1280068aa7a7, 0x39bf8a0d898a050, 0x78c40970a3f390b, 0x31589888a02411, 0x1894f830b0a8287, 0x8693060592a1920]
def page196 : List Nat := [0x213b3a10201a208, 0xa0705830909828, 0x80b029888872799, 0x9901898727269, 0x6028a4544a18686, 0xb462243920c088, 0xa07018a0a8c478a, 0xe8a24230c01890, 0xc0a830b0f3981b9, 0x8703018a86450a0, 0x201d003090acc45, 0x6230a2a8a85060, 0x6021c8a23ab4b89, 0x3f0a1d9e4e071e8, 0x1c18a92c0bf8cc1, 0x8a4729c7898a038, 0x1b4870201480a8c, 0xa48a0b07030a0b0, 0x2888a330b1d258a, 0xa79dcf9c9c32073, 0xb070d0a8a093f8c, 0xb309088b09c9268, 0xa388b3534b3b206, 0x33b9c139268c090]
def page197 : List Nat := [0x92208863402a18a, 0xa8a0b353492210, 0x98ac948c8024b87, 0xc0d9a930c86818, 0xa8a0aaa8b0a8185, 0x8a9ab48c8906898, 0xb0882b409068534, 0x1870a4d4cb38d8, 0x2860a8a03090a83, 0x4b920d020193069, 0x8830b070a2e0c4c, 0x23bd0ad04f9f090, 0xbac0abda30b090a, 0xa333f4c8a08c0a, 0xabf9d32bebe088b, 0xab8b0c3d0a0b3d8, 0xa9f4d0a08850302, 0x703348906b4060, 0xe997f20cc4bb38d, 0xa1fe107e98fe187, 0x87ea0fe207e18fe, 0xff197e10ff90fe8, 0xe907f217e987f10, 0xa17e90ff98ff887]
def page198 : List Nat := [0xfe217f21fe21ff, 0xfe20ff207f987fa, 0xea17f997f107f18, 0x187fa07e087f907, 0x87ea07e197fa1ff, 0x360070a04c21ff0, 0x95a280370c0a580, 0x520c410084a0801, 0x18039bd660f71cc, 0xcc4a8907c60482c, 0x796149311d08f0d, 0x61e09edd1b99d8d, 0xead2b29e866e563, 0xb977f674b2f16fe, 0x4990d54f6d93d3a, 0xf14994d3859524f, 0x94ef1150f5993b4, 0x8d4f5399528db05, 0x58ed518ca115953, 0x532cd8cad5190f9, 0x50d92d4d0fb5959, 0x98e1508994d3b19, 0x18550e9b0850d5a, 0x4e99390fa99550f]
def page199 : List Nat := [0x1504f19952e4c85, 0x354f194ed14ee99, 0xd0f558990d70859, 0xe98d974f1193ad4, 0x50da859530f5506, 0xaf152d8d90fb145, 0x9ffc875d943]
def storagePage (p : Nat) : List Nat := (if p < 100 then (if p < 50 then (if p < 25 then (if p < 12 then (if p < 6 then (if p < 3 then (if p < 1 then page0 else (if p < 2 then page1 else page2)) else (if p < 4 then page3 else (if p < 5 then page4 else page5))) else (if p < 9 then (if p < 7 then page6 else (if p < 8 then page7 else page8)) else (if p < 10 then page9 else (if p < 11 then page10 else page11)))) else (if p < 18 then (if p < 15 then (if p < 13 then page12 else (if p < 14 then page13 else page14)) else (if p < 16 then page15 else (if p < 17 then page16 else page17))) else (if p < 21 then (if p < 19 then page18 else (if p < 20 then page19 else page20)) else (if p < 23 then (if p < 22 then page21 else page22) else (if p < 24 then page23 else page24))))) else (if p < 37 then (if p < 31 then (if p < 28 then (if p < 26 then page25 else (if p < 27 then page26 else page27)) else (if p < 29 then page28 else (if p < 30 then page29 else page30))) else (if p < 34 then (if p < 32 then page31 else (if p < 33 then page32 else page33)) else (if p < 35 then page34 else (if p < 36 then page35 else page36)))) else (if p < 43 then (if p < 40 then (if p < 38 then page37 else (if p < 39 then page38 else page39)) else (if p < 41 then page40 else (if p < 42 then page41 else page42))) else (if p < 46 then (if p < 44 then page43 else (if p < 45 then page44 else page45)) else (if p < 48 then (if p < 47 then page46 else page47) else (if p < 49 then page48 else page49)))))) else (if p < 75 then (if p < 62 then (if p < 56 then (if p < 53 then (if p < 51 then page50 else (if p < 52 then page51 else page52)) else (if p < 54 then page53 else (if p < 55 then page54 else page55))) else (if p < 59 then (if p < 57 then page56 else (if p < 58 then page57 else page58)) else (if p < 60 then page59 else (if p < 61 then page60 else page61)))) else (if p < 68 then (if p < 65 then (if p < 63 then page62 else (if p < 64 then page63 else page64)) else (if p < 66 then page65 else (if p < 67 then page66 else page67))) else (if p < 71 then (if p < 69 then page68 else (if p < 70 then page69 else page70)) else (if p < 73 then (if p < 72 then page71 else page72) else (if p < 74 then page73 else page74))))) else (if p < 87 then (if p < 81 then (if p < 78 then (if p < 76 then page75 else (if p < 77 then page76 else page77)) else (if p < 79 then page78 else (if p < 80 then page79 else page80))) else (if p < 84 then (if p < 82 then page81 else (if p < 83 then page82 else page83)) else (if p < 85 then page84 else (if p < 86 then page85 else page86)))) else (if p < 93 then (if p < 90 then (if p < 88 then page87 else (if p < 89 then page88 else page89)) else (if p < 91 then page90 else (if p < 92 then page91 else page92))) else (if p < 96 then (if p < 94 then page93 else (if p < 95 then page94 else page95)) else (if p < 98 then (if p < 97 then page96 else page97) else (if p < 99 then page98 else page99))))))) else (if p < 150 then (if p < 125 then (if p < 112 then (if p < 106 then (if p < 103 then (if p < 101 then page100 else (if p < 102 then page101 else page102)) else (if p < 104 then page103 else (if p < 105 then page104 else page105))) else (if p < 109 then (if p < 107 then page106 else (if p < 108 then page107 else page108)) else (if p < 110 then page109 else (if p < 111 then page110 else page111)))) else (if p < 118 then (if p < 115 then (if p < 113 then page112 else (if p < 114 then page113 else page114)) else (if p < 116 then page115 else (if p < 117 then page116 else page117))) else (if p < 121 then (if p < 119 then page118 else (if p < 120 then page119 else page120)) else (if p < 123 then (if p < 122 then page121 else page122) else (if p < 124 then page123 else page124))))) else (if p < 137 then (if p < 131 then (if p < 128 then (if p < 126 then page125 else (if p < 127 then page126 else page127)) else (if p < 129 then page128 else (if p < 130 then page129 else page130))) else (if p < 134 then (if p < 132 then page131 else (if p < 133 then page132 else page133)) else (if p < 135 then page134 else (if p < 136 then page135 else page136)))) else (if p < 143 then (if p < 140 then (if p < 138 then page137 else (if p < 139 then page138 else page139)) else (if p < 141 then page140 else (if p < 142 then page141 else page142))) else (if p < 146 then (if p < 144 then page143 else (if p < 145 then page144 else page145)) else (if p < 148 then (if p < 147 then page146 else page147) else (if p < 149 then page148 else page149)))))) else (if p < 175 then (if p < 162 then (if p < 156 then (if p < 153 then (if p < 151 then page150 else (if p < 152 then page151 else page152)) else (if p < 154 then page153 else (if p < 155 then page154 else page155))) else (if p < 159 then (if p < 157 then page156 else (if p < 158 then page157 else page158)) else (if p < 160 then page159 else (if p < 161 then page160 else page161)))) else (if p < 168 then (if p < 165 then (if p < 163 then page162 else (if p < 164 then page163 else page164)) else (if p < 166 then page165 else (if p < 167 then page166 else page167))) else (if p < 171 then (if p < 169 then page168 else (if p < 170 then page169 else page170)) else (if p < 173 then (if p < 172 then page171 else page172) else (if p < 174 then page173 else page174))))) else (if p < 187 then (if p < 181 then (if p < 178 then (if p < 176 then page175 else (if p < 177 then page176 else page177)) else (if p < 179 then page178 else (if p < 180 then page179 else page180))) else (if p < 184 then (if p < 182 then page181 else (if p < 183 then page182 else page183)) else (if p < 185 then page184 else (if p < 186 then page185 else page186)))) else (if p < 193 then (if p < 190 then (if p < 188 then page187 else (if p < 189 then page188 else page189)) else (if p < 191 then page190 else (if p < 192 then page191 else page192))) else (if p < 196 then (if p < 194 then page193 else (if p < 195 then page194 else page195)) else (if p < 198 then (if p < 197 then page196 else page197) else (if p < 199 then page198 else page199))))))))
def storageWord (i : Nat) := (storagePage (i / 24)).getD (i % 24) 0
def a0Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x7d7e7d7e7d7e7d7, 0xd7e7d7e7d7e7d7e, 0xd7e7d7e7])
  | 4 => BitVec.ofNat 152 (big [0x112411241124112, 0x124112411241124, 0x12411241])
  | 5 => BitVec.ofNat 152 (big [0xf7adf7adf7adf7a, 0x7adf7adf7adf7ad, 0x7adf7adf])
  | _ => 0

def a0Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x206120612061206, 0x61206120612061, 0x6120612])
  | 4 => BitVec.ofNat 152 (big [0xbf6bbf6bbf6bbf6, 0xf6bbf6bbf6bbf6b, 0xf6bbf6bb])
  | 5 => BitVec.ofNat 152 (big [0x70207020702070, 0x702070207020702, 0x70207020])
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
def a0 : Atlas := ⟨3,rawDecor 49 a0Pos a0Neg,repeatWord 12297923203170347690,a0Count,a0Rec,(fun _ _ => 0),a0Loc⟩
def a0Domains : Catalog := []
def a1Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x653653653653653, 0x653653653653653, 0x53653653])
  | 4 => BitVec.ofNat 152 (big [0x9ac9ac9ac9ac9ac, 0x9ac9ac9ac9ac9ac, 0xac9ac9ac])
  | 5 => BitVec.ofNat 152 (big [0x0])
  | _ => 0

def a1Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xb16b16b16b16b16, 0xb16b16b16b16b16, 0x16b16b16])
  | 4 => BitVec.ofNat 152 (big [0x734734734734734, 0x734734734734734, 0x34734734])
  | 5 => BitVec.ofNat 152 (big [0xfe2fe2fe2fe2fe2, 0xfe2fe2fe2fe2fe2, 0xe2fe2fe2])
  | _ => 0

def a1Count (k : Nat) : Nat :=
  match k with
  | 1 => 2
  | 2 => 4
  | 3 => 1
  | _ => 0

def a1Rec (k i : Nat) : Nat :=
  match k with
  | 1 => field storageWord (3+i*25) 25
  | 2 => field storageWord (55+i*14) 14
  | 3 => field storageWord (123+i*3) 3
  | _ => 0

def a1Loc (k tag : Nat) : Nat :=
  match k with
  | 1 => hashRow 2 2 (field storageWord (53+(tag % 2)*1) 1) tag
  | 2 => hashRow 4 4 (field storageWord (111+(tag % 4)*3) 3) tag
  | 3 => 0
  | _ => 0

def a1Hints : Hints := fun _ _ => []
def a1 : Atlas := ⟨3,rawDecor 52 a1Pos a1Neg,repeatWord 252702960,a1Count,a1Rec,(fun _ _ => 0),a1Loc⟩
def a1Domains : Catalog := []
def a2Pos : Nat → Bits
  | 4 => BitVec.ofNat 152 (big [0x333333333333333, 0x333333333333333, 0x33333333])
  | 5 => BitVec.ofNat 152 (big [0xccccccccccccccc, 0xccccccccccccccc, 0xcccccccc])
  | _ => 0

def a2Neg : Nat → Bits
  | 4 => BitVec.ofNat 152 (big [0x666666666666666, 0x666666666666666, 0x66666666])
  | 5 => BitVec.ofNat 152 (big [0x666666666666666, 0x666666666666666, 0x66666666])
  | _ => 0

def a2Count (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def a2Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (126+i*2) 2
  | _ => 0

def a2Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => 0
  | _ => 0

def a2Hints : Hints := fun _ _ => []
def a2 : Atlas := ⟨2,rawDecor 48 a2Pos a2Neg,repeatWord 281474976645120,a2Count,a2Rec,(fun _ _ => 0),a2Loc⟩
def a2Domains : Catalog := []
def a3Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x7f8dc0c78f68d56, 0xfc6e063c7b46ab5, 0x3da355ab])
  | 2 => BitVec.ofNat 152 (big [0xfedfbbffa7f6fa4, 0xf6fddffd3fb7d27, 0x9fdbe93f])
  | 4 => BitVec.ofNat 152 (big [0x6a752e7a7537c89, 0x53a973d3a9be44e, 0xd4df2273])
  | 5 => BitVec.ofNat 152 (big [0x8f2f7d755adda7b, 0x797bebaad6ed3df, 0x6b769efc])
  | _ => 0

def a3Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x8463b24b930cd58, 0x231d925c9866ac2, 0x4c335614])
  | 2 => BitVec.ofNat 152 (big [0x10404200062024, 0x82021000310120, 0x1880900])
  | 4 => BitVec.ofNat 152 (big [0x86c2e148971dcc8, 0x36170a44b8ee641, 0x5c77320c])
  | 5 => BitVec.ofNat 152 (big [0x585280140304a4b, 0xc29400a01825258, 0xc1292c2])
  | _ => 0

def a3Count (k : Nat) : Nat :=
  match k with
  | 3 => 2
  | 4 => 13
  | 5 => 5
  | 6 => 1
  | _ => 0

def a3Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (128+i*37) 37
  | 4 => field storageWord (211+i*26) 26
  | 5 => field storageWord (694+i*15) 15
  | 6 => field storageWord (870+i*4) 4
  | _ => 0

def a3Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 2 2 (field storageWord (202+(tag % 2)*2) 2) tag
  | 4 => hashRow 13 13 (field storageWord (549+(tag % 13)*5) 5) tag
  | 5 => hashRow 5 2 (field storageWord (769+(tag % 2)*4) 4) tag
  | 6 => 0
  | _ => 0

def a3Hints (k i : Nat) : List Nat :=
  match k with
  | 3 => hintsAt storageWord 207 1 210 1 206 1 i
  | 4 => hintsAt storageWord 622 4 678 2 614 2 i
  | 5 => hintsAt storageWord 792 5 822 3 777 3 i
  | 6 => hintsAt storageWord 883 2 887 2 874 3 i
  | _ => []

def a3 : Atlas := ⟨6,rawDecor 54 a3Pos a3Neg,repeatWord 17578671933861445824,a3Count,a3Rec,(fun _ _ => 0),a3Loc⟩
def a3Domains : Catalog := [(repeatWord 3689348814741910323, 4), (repeatWord 1085102592571150095, 4), (repeatWord 281470681808895, 4), (repeatWord 18446744069414584320, 4), (repeatWord 1085102592318504960, 3)]
def a4Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf6edf6edf6edf6e, 0x6edf6edf6edf6ed, 0x6edf6edf])
  | 1 => BitVec.ofNat 152 (big [0x3f5f3f5f3f5f3f5, 0xf5f3f5f3f5f3f5f, 0xf5f3f5f3])
  | 4 => BitVec.ofNat 152 (big [0xe4e4e4e4e4e4e4e, 0x4e4e4e4e4e4e4e4, 0x4e4e4e4e])
  | _ => 0

def a4Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xe200e200e200e2, 0xe200e200e200e20, 0xe200e200])
  | 1 => BitVec.ofNat 152 (big [0x514051405140514, 0x140514051405140, 0x14051405])
  | 4 => BitVec.ofNat 152 (big [0x71ca71ca71ca71c, 0x1ca71ca71ca71ca, 0x1ca71ca7])
  | _ => 0

def a4Count (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def a4Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (893+i*3) 3
  | _ => 0

def a4Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => 0
  | _ => 0

def a4Hints : Hints := fun _ _ => []
def a4 : Atlas := ⟨2,rawDecor 19 a4Pos a4Neg,repeatWord 12297866911897275596,a4Count,a4Rec,(fun _ _ => 0),a4Loc⟩
def a4Domains : Catalog := []
def a5Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf7bf6efedb39bf9, 0x7bf6efedb39bf9d, 0xb39bf9df])
  | 2 => BitVec.ofNat 152 (big [0x2c264de8f0b54b3, 0xc264de8f0b54b3b, 0xb54b3b2])
  | 4 => BitVec.ofNat 152 (big [0x94b242e092318b8, 0x4b242e092318b88, 0x2318b889])
  | 5 => BitVec.ofNat 152 (big [0xfdfd9fef6fd6c8f, 0xdfd9fef6fd6c8fb, 0xfd6c8fbf])
  | _ => 0

def a5Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x1095460010339, 0x10954600103392, 0x1033920])
  | 2 => BitVec.ofNat 152 (big [0xc5d1abcc54e95a3, 0x5d1abcc54e95a34, 0x4e95a34c])
  | 4 => BitVec.ofNat 152 (big [0x4aed7ebb8eb7a9a, 0xaed7ebb8eb7a9a7, 0xeb7a9a74])
  | 5 => BitVec.ofNat 152 (big [0x20542280c26882, 0x20542280c268824, 0xc2688240])
  | _ => 0

def a5Count (k : Nat) : Nat :=
  match k with
  | 3 => 8
  | 4 => 18
  | 5 => 12
  | 6 => 1
  | _ => 0

def a5Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (896+i*37) 37
  | 4 => field storageWord (1288+i*26) 26
  | 5 => field storageWord (2242+i*15) 15
  | 6 => field storageWord (2653+i*4) 4
  | _ => 0

def a5Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 8 3 (field storageWord (1192+(tag % 3)*4) 4) tag
  | 4 => hashRow 18 18 (field storageWord (1756+(tag % 18)*5) 5) tag
  | 5 => hashRow 12 6 (field storageWord (2422+(tag % 6)*5) 5) tag
  | 6 => 0
  | _ => 0

def a5Hints (k i : Nat) : List Nat :=
  match k with
  | 3 => hintsAt storageWord 1268 2 1286 1 1204 32 i
  | 4 => hintsAt storageWord 2014 6 2128 3 1846 21 i
  | 5 => hintsAt storageWord 2467 6 2545 3 2452 3 i
  | 6 => hintsAt storageWord 2663 2 2667 1 2657 3 i
  | _ => []

def a5 : Atlas := ⟨6,rawDecor 53 a5Pos a5Neg,repeatWord 12297923205865146890,a5Count,a5Rec,(fun _ _ => 0),a5Loc⟩
def a5Domains : Catalog := [(repeatWord 12297829382473034410, 4), (repeatWord 1085102592571150095, 4), (repeatWord 4294967295, 4), (repeatWord 17361641481138401520, 3), (repeatWord 2863311530, 3)]
def a6Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xebf3fbffddf96fd, 0xbf5f9fdffeefcb7, 0xefff77e5])
  | 1 => BitVec.ofNat 152 (big [0x36feffbdf767fe6, 0xf9b7f7fdefbb3ff, 0xfef7dd9f])
  | 4 => BitVec.ofNat 152 (big [0xc9a15842d899619, 0x864d0ac216c4cb0, 0x610b6265])
  | 5 => BitVec.ofNat 152 (big [0xddedff53ffdff5b, 0xd6ef6ffa9ffeffa, 0xfd4fff7f])
  | _ => 0

def a6Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xac086427c8424d5, 0x356043213e42126, 0x909f2109])
  | 1 => BitVec.ofNat 152 (big [0x31108c431728e26, 0x8988846218b9471, 0x310c5ca3])
  | 4 => BitVec.ofNat 152 (big [0xe674a5c776a9e1c, 0x8733a52e3bb54f0, 0x971ddaa7])
  | 5 => BitVec.ofNat 152 (big [0x4a121130a41bb49, 0xd25090898520dda, 0x44c2906e])
  | _ => 0

def a6Count (k : Nat) : Nat :=
  match k with
  | 2 => 2
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 0

def a6Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (2669+i*37) 37
  | 3 => field storageWord (2747+i*26) 26
  | 4 => field storageWord (2927+i*15) 15
  | 5 => field storageWord (3090+i*4) 4
  | _ => 0

def a6Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => hashRow 2 4 (field storageWord (2743+(tag % 4)*1) 1) tag
  | 3 => hashRow 6 6 (field storageWord (2903+(tag % 6)*4) 4) tag
  | 4 => hashRow 6 3 (field storageWord (3017+(tag % 3)*2) 2) tag
  | 5 => 0
  | _ => 0

def a6Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3038 4 3066 3 3023 3 i
  | 5 => hintsAt storageWord 3103 2 3107 2 3094 3 i
  | _ => []

def a6 : Atlas := ⟨5,rawDecor 51 a6Pos a6Neg,repeatWord 12297866909033990280,a6Count,a6Rec,(fun _ _ => 0),a6Loc⟩
def a6Domains : Catalog := [(repeatWord 14757395258967641292, 4), (repeatWord 7378697629483820646, 4), (repeatWord 3689517697150995660, 4), (repeatWord 12297829382473034410, 3), (repeatWord 18446744069414584320, 3)]
def a7Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xdffffedfdfef7f3, 0xffffedfdfef7f3f, 0xfef7f3fd])
  | 2 => BitVec.ofNat 152 (big [0xeaef17ef35b197c, 0xaef17ef35b197ca, 0x5b197cae])
  | 4 => BitVec.ofNat 152 (big [0xad220d60905471, 0xad220d60905471b, 0x905471b0])
  | 5 => BitVec.ofNat 152 (big [0x65f667fc78d6c1f, 0x5f667fc78d6c1fd, 0x8d6c1fd6])
  | _ => 0

def a7Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x2000048100024a0, 0x48100024a00, 0x24a002])
  | 2 => BitVec.ofNat 152 (big [0x15a0380e0f90954, 0x5a0380e0f909545, 0xf9095451])
  | 4 => BitVec.ofNat 152 (big [0xf623ffed0d5f4f5, 0x623ffed0d5f4f54, 0xd5f4f54f])
  | 5 => BitVec.ofNat 152 (big [0x96489278994001f, 0x6489278994001f2, 0x94001f29])
  | _ => 0

def a7Count (k : Nat) : Nat :=
  match k with
  | 4 => 12
  | 5 => 1
  | _ => 0

def a7Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (3113+i*15) 15
  | 5 => field storageWord (3473+i*4) 4
  | _ => 0

def a7Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 12 24 (field storageWord (3293+(tag % 24)*5) 5) tag
  | 5 => 0
  | _ => 0

def a7Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3422 3 3461 2 3413 3 i
  | 5 => hintsAt storageWord 3495 3 3501 3 3477 3 i
  | _ => []

def a7 : Atlas := ⟨5,rawDecor 54 a7Pos a7Neg,repeatWord 14757448241482091724,a7Count,a7Rec,(fun _ _ => 0),a7Loc⟩
def a7Domains : Catalog := [(repeatWord 4340410370284600380, 4), (repeatWord 14757226376558555955, 4), (repeatWord 3689348817318890700, 4), (repeatWord 1085350949055099120, 4), (repeatWord 17361641477348724495, 4), (repeatWord 281474976645120, 4)]
def a8Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xdafae3a7fee0e2d, 0xafae3a7fee0e2d9, 0xee0e2d9d])
  | 2 => BitVec.ofNat 152 (big [0xffffbd7bff7f5fe, 0xfffbd7bff7f5fef, 0xf7f5feff])
  | 4 => BitVec.ofNat 152 (big [0x65f3847aa17c4ca, 0x5f3847aa17c4caa, 0x17c4caa6])
  | 5 => BitVec.ofNat 152 (big [0xaa57fa976d97f91, 0xa57fa976d97f91e, 0xd97f91ea])
  | _ => 0

def a8Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xd11190de22460d, 0xd11190de22460d6, 0x22460d60])
  | 2 => BitVec.ofNat 152 (big [0x202200900160, 0x2022009001600, 0x90016000])
  | 4 => BitVec.ofNat 152 (big [0x9b65499ee24d68a, 0xb65499ee24d68a5, 0x24d68a59])
  | 5 => BitVec.ofNat 152 (big [0x43288d82c41de90, 0x3288d82c41de901, 0x41de9014])
  | _ => 0

def a8Count (k : Nat) : Nat :=
  match k with
  | 3 => 15
  | 4 => 12
  | 5 => 1
  | _ => 0

def a8Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (3519+i*26) 26
  | 4 => field storageWord (3984+i*15) 15
  | 5 => field storageWord (4330+i*4) 4
  | _ => 0

def a8Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 15 15 (field storageWord (3909+(tag % 15)*5) 5) tag
  | 4 => hashRow 12 24 (field storageWord (4164+(tag % 24)*5) 5) tag
  | 5 => 0
  | _ => 0

def a8Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 4285 3 4324 1 4284 1 i
  | 5 => hintsAt storageWord 4335 1 4337 1 4334 1 i
  | _ => []

def a8 : Atlas := ⟨5,rawDecor 54 a8Pos a8Neg,repeatWord 17361654726817530048,a8Count,a8Rec,(fun _ _ => 0),a8Loc⟩
def a8Domains : Catalog := [(repeatWord 281470681808895, 4)]
def a9Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x31826304c6098c1, 0x31826304c6098c1, 0x4c6098c1])
  | 4 => BitVec.ofNat 152 (big [0x778eef1dde3bbc7, 0x778eef1dde3bbc7, 0xdde3bbc7])
  | 5 => BitVec.ofNat 152 (big [0xb9f373e6e7cdcf9, 0xb9f373e6e7cdcf9, 0x6e7cdcf9])
  | _ => 0

def a9Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xdf43be877d0efa1, 0xdf43be877d0efa1, 0x77d0efa1])
  | 4 => BitVec.ofNat 152 (big [0x8297052e0a5c14b, 0x8297052e0a5c14b, 0xe0a5c14b])
  | 5 => BitVec.ofNat 152 (big [0x41d483a907520ea, 0x41d483a907520ea, 0x907520ea])
  | _ => 0

def a9Count (k : Nat) : Nat :=
  match k with
  | 1 => 9
  | 2 => 62
  | 3 => 95
  | 4 => 12
  | 5 => 1
  | _ => 0

def a9Rec (k i : Nat) : Nat :=
  match k with
  | 1 => field storageWord (4338+i*47) 47
  | 2 => field storageWord (4786+i*36) 36
  | 3 => field storageWord (7452+i*25) 25
  | 4 => field storageWord (10083+i*14) 14
  | 5 => field storageWord (10311+i*3) 3
  | _ => 0

def a9Loc (k tag : Nat) : Nat :=
  match k with
  | 1 => hashRow 9 5 (field storageWord (4761+(tag % 5)*5) 5) tag
  | 2 => hashRow 62 62 (field storageWord (7018+(tag % 62)*7) 7) tag
  | 3 => hashRow 95 32 (field storageWord (9827+(tag % 32)*8) 8) tag
  | 4 => hashRow 12 12 (field storageWord (10251+(tag % 12)*5) 5) tag
  | 5 => 0
  | _ => 0

def a9Hints : Hints := fun _ _ => []
def a9 : Atlas := ⟨5,rawDecor 52 a9Pos a9Neg,repeatWord 17361393120864829440,a9Count,a9Rec,(fun _ _ => 0),a9Loc⟩
def a9Domains : Catalog := []
def a10Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xe4f77edad3e9bcd, 0x27bbf6d69f4de6b, 0x4fa6f35f])
  | 2 => BitVec.ofNat 152 (big [0xdbefffef3cfecf2, 0xdf7fff79e7f6797, 0xf3fb3cbe])
  | 4 => BitVec.ofNat 152 (big [0x9444e5d2f4203e6, 0xa2272e97a101f32, 0xd080f994])
  | 5 => BitVec.ofNat 152 (big [0x4c431473c06cf54, 0x6218a39e0367aa6, 0x1b3d532])
  | _ => 0

def a10Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x1109426004a1985, 0x884a1300250cc2c, 0x12866160])
  | 2 => BitVec.ofNat 152 (big [0x200008804018442, 0x440200c2210, 0x611081])
  | 4 => BitVec.ofNat 152 (big [0x6a7d18d27d9c6e7, 0x53e8c693ece373d, 0xf671b9eb])
  | 5 => BitVec.ofNat 152 (big [0xb394dea6e27df52, 0x9ca6f53713efa91, 0x89f7d48d])
  | _ => 0

def a10Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a10Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (10314+i*4) 4
  | _ => 0

def a10Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a10Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 10319 1 10321 1 10318 1 i
  | _ => []

def a10 : Atlas := ⟨5,rawDecor 53 a10Pos a10Neg,repeatWord 12297906650113702650,a10Count,a10Rec,(fun _ _ => 0),a10Loc⟩
def a10Domains : Catalog := [(repeatWord 6510615555426900570, 6)]
def a11Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdf1ffd9f2bbd9ab, 0xdf1ffd9f2bbd9ab, 0xf2bbd9ab])
  | 2 => BitVec.ofNat 152 (big [0x3dfdd42afa2facc, 0x3dfdd42afa2facc, 0xafa2facc])
  | 4 => BitVec.ofNat 152 (big [0x10114903292498a, 0x10114903292498a, 0x3292498a])
  | 5 => BitVec.ofNat 152 (big [0x774e4f65edf8792, 0x774e4f65edf8792, 0x5edf8792])
  | _ => 0

def a11Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x2088004c080000b, 0x2088004c080000b, 0xc080000b])
  | 2 => BitVec.ofNat 152 (big [0xc0068382872aac0, 0xc0068382872aac0, 0x2872aac0])
  | 4 => BitVec.ofNat 152 (big [0xefeff3dfff7efcb, 0xefeff3dfff7efcb, 0xfff7efcb])
  | 5 => BitVec.ofNat 152 (big [0x8923a002651a780, 0x8923a002651a780, 0x2651a780])
  | _ => 0

def a11Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a11Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (10322+i*4) 4
  | _ => 0

def a11Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a11Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 10327 1 10329 1 10326 1 i
  | _ => []

def a11 : Atlas := ⟨4,rawDecor 53 a11Pos a11Neg,repeatWord 12297923205865208570,a11Count,a11Rec,(fun _ _ => 0),a11Loc⟩
def a11Domains : Catalog := [(repeatWord 1085102592571150095, 4)]
def a12Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x30bd87db4fba30b, 0xfba30bd87db4fba, 0xbd87db4])
  | 2 => BitVec.ofNat 152 (big [0xe70fdfb5f479e70, 0x479e70fdfb5f479, 0x70fdfb5f])
  | 4 => BitVec.ofNat 152 (big [0xb624d3409531b62, 0x531b624d3409531, 0x624d3409])
  | 5 => BitVec.ofNat 152 (big [0x5a67f4c727a75a6, 0x7a75a67f4c727a7, 0xa67f4c72])
  | _ => 0

def a12Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x30126801c220301, 0x22030126801c220, 0x126801c])
  | 2 => BitVec.ofNat 152 (big [0x0])
  | 4 => BitVec.ofNat 152 (big [0xbe3bee3fef77be3, 0xf77be3bee3fef77, 0xe3bee3fe])
  | 5 => BitVec.ofNat 152 (big [0x8a28062824028a2, 0x4028a2806282402, 0xa2806282])
  | _ => 0

def a12Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a12Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (10330+i*4) 4
  | _ => 0

def a12Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a12Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 10335 1 10337 1 10334 1 i
  | _ => []

def a12 : Atlas := ⟨4,rawDecor 53 a12Pos a12Neg,repeatWord 18085048728383716090,a12Count,a12Rec,(fun _ _ => 0),a12Loc⟩
def a12Domains : Catalog := [(repeatWord 1085102592571150095, 4)]
def a13Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xffffedffd6ffedb, 0xffff6ffeb7ff6de, 0x5bffb6f7])
  | 2 => BitVec.ofNat 152 (big [0xbff4f6adfd67d37, 0xffa7b56feb3e9bb, 0xf59f4ddd])
  | 4 => BitVec.ofNat 152 (big [0x28542021d440813, 0x42a1010ea20409a, 0x510204d1])
  | 5 => BitVec.ofNat 152 (big [0x7d589f6ea96cb66, 0xeac4fb754b65b31, 0xa5b2d98b])
  | _ => 0

def a13Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x30010e00620283, 0x180087003101419, 0x1880a0c8])
  | 2 => BitVec.ofNat 152 (big [0x4809450d3051d14, 0x404a2869828e8a4, 0xc1474522])
  | 4 => BitVec.ofNat 152 (big [0xd79f5ef5ee69a97, 0xbcfaf7af734d4bd, 0xb9a6a5ee])
  | 5 => BitVec.ofNat 152 (big [0x866e50058eaca66, 0x3372802c7565336, 0x3ab299b4])
  | _ => 0

def a13Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a13Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (10338+i*4) 4
  | _ => 0

def a13Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a13Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 10343 1 10345 1 10342 1 i
  | _ => []

def a13 : Atlas := ⟨4,rawDecor 54 a13Pos a13Neg,repeatWord 13889379413306428620,a13Count,a13Rec,(fun _ _ => 0),a13Loc⟩
def a13Domains : Catalog := [(repeatWord 18446744069414584320, 4)]
def a14Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xe5f1bb4dbfecdb9, 0xe5f1bb4dbfecdb9, 0xdbfecdb9])
  | 1 => BitVec.ofNat 152 (big [0xbfbffefbedf776f, 0xbfbffefbedf776f, 0xbedf776f])
  | 2 => BitVec.ofNat 152 (big [0xfbeffdbfde7fafe, 0xfbeffdbfde7fafe, 0xfde7fafe])
  | 4 => BitVec.ofNat 152 (big [0xcac51d8cd25dab2, 0xcac51d8cd25dab2, 0xcd25dab2])
  | _ => 0

def a14Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x182c54e51164c39, 0x182c54e51164c39, 0x51164c39])
  | 1 => BitVec.ofNat 152 (big [0x40016190d8a0724, 0x40016190d8a0724, 0xd8a0724])
  | 2 => BitVec.ofNat 152 (big [0x514082a07148ca, 0x514082a07148ca, 0xa07148ca])
  | 4 => BitVec.ofNat 152 (big [0x35a267da90e96b2, 0x35a267da90e96b2, 0xa90e96b2])
  | _ => 0

def a14Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a14Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (10346+i*4) 4
  | _ => 0

def a14Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a14Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 10351 1 10353 1 10350 1 i
  | _ => []

def a14 : Atlas := ⟨4,rawDecor 23 a14Pos a14Neg,repeatWord 16204172224370886856,a14Count,a14Rec,(fun _ _ => 0),a14Loc⟩
def a14Domains : Catalog := [(repeatWord 12297829382473034410, 3)]
def a15Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xcf4b3fc693d2cf4, 0x3d2cf4b3fc693d2, 0xf4b3fc69])
  | 1 => BitVec.ofNat 152 (big [0xa43ffbbf656ba43, 0x56ba43ffbbf656b, 0x43ffbbf6])
  | 4 => BitVec.ofNat 152 (big [0xea554b4e9139ea5, 0x139ea554b4e9139, 0xa554b4e9])
  | 5 => BitVec.ofNat 152 (big [0x53971cfc3f8e539, 0xf8e53971cfc3f8e, 0x3971cfc3])
  | _ => 0

def a15Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x454448224802454, 0x802454448224802, 0x54448224])
  | 1 => BitVec.ofNat 152 (big [0x0])
  | 4 => BitVec.ofNat 152 (big [0xba1aa69595acba1, 0x5acba1aa69595ac, 0xa1aa6959])
  | 5 => BitVec.ofNat 152 (big [0x1218828085a0121, 0x5a01218828085a0, 0x21882808])
  | _ => 0

def a15Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a15Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (10354+i*4) 4
  | _ => 0

def a15Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a15Hints : Hints := fun _ _ => []
def a15 : Atlas := ⟨3,rawDecor 51 a15Pos a15Neg,repeatWord 17216979900174355660,a15Count,a15Rec,(fun _ _ => 0),a15Loc⟩
def a15Domains : Catalog := []
def a16Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfb77fbfb7ed2af6, 0xb77fbfb7ed2af6b, 0xed2af6bf])
  | 1 => BitVec.ofNat 152 (big [0x9fdfce7cf57fdad, 0xfdfce7cf57fdadf, 0x57fdadf9])
  | 2 => BitVec.ofNat 152 (big [0xeef94ccc9dfd769, 0xef94ccc9dfd7695, 0xdfd7695e])
  | 5 => BitVec.ofNat 152 (big [0x69e3f5ab6af535e, 0x9e3f5ab6af535ed, 0xaf535ed6])
  | _ => 0

def a16Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x40306012d402a2, 0x40306012d402a24, 0xd402a240])
  | 1 => BitVec.ofNat 152 (big [0x4a2011640013d04, 0xa2011640013d040, 0x13d0404])
  | 2 => BitVec.ofNat 152 (big [0x1112660b91c4269, 0x112660b91c4269a, 0x1c4269a1])
  | 5 => BitVec.ofNat 152 (big [0x837c018ec03215c, 0x37c018ec03215c2, 0x3215c28])
  | _ => 0

def a16Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a16Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (10358+i*4) 4
  | _ => 0

def a16Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a16Hints : Hints := fun _ _ => []
def a16 : Atlas := ⟨3,rawDecor 39 a16Pos a16Neg,repeatWord 16927600443537279176,a16Count,a16Rec,(fun _ _ => 0),a16Loc⟩
def a16Domains : Catalog := []
def a17Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfb7c9f36bd4599f, 0x3f96ac78dacfc5e, 0x467fb937])
  | 1 => BitVec.ofNat 152 (big [0x77d5bbcd8ede7a8, 0xfffdf75e2db73c7, 0xbefef7ef])
  | 2 => BitVec.ofNat 152 (big [0xf06bfadf652be6d, 0xbcfb53b7eb7c779, 0xdfa19fff])
  | 4 => BitVec.ofNat 152 (big [0x586836381803ebf, 0x8fca8f4cd16ce5b, 0x403053a])
  | 5 => BitVec.ofNat 152 (big [0xbde646727bf24d3, 0x63c4feeb9ea1db3, 0xf7f65a3a])
  | _ => 0

def a17Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x627e2806b54198a, 0x80b08401bc0dc06, 0xa7440d0c])
  | 1 => BitVec.ofNat 152 (big [0x9c533450a145a8, 0x146063541008000, 0x30381068])
  | 2 => BitVec.ofNat 152 (big [0xb202c028052b245, 0x2a0010222074658, 0xcc04e600])
  | 4 => BitVec.ofNat 152 (big [0xd9e573341a02ffd, 0xda305fc851382dd, 0x78dbdaea])
  | 5 => BitVec.ofNat 152 (big [0x991006306ac2453, 0xb8151898e8038b, 0x8895056])
  | _ => 0

def a17Count (k : Nat) : Nat :=
  match k with
  | 4 => 35
  | 5 => 781
  | 6 => 1537
  | 7 => 520
  | 8 => 40
  | 9 => 1
  | _ => 0

def a17Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (10362+i*60) 60
  | 5 => field storageWord (12675+i*49) 49
  | 6 => field storageWord (71509+i*38) 38
  | 7 => field storageWord (225910+i*27) 27
  | 8 => field storageWord (284791+i*16) 16
  | 9 => field storageWord (286950+i*5) 5
  | _ => 0

def a17Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 35 12 (field storageWord (12462+(tag % 12)*6) 6) tag
  | 5 => hashRow 781 261 (field storageWord (50944+(tag % 261)*11) 11) tag
  | 6 => hashRow 1537 513 (field storageWord (129915+(tag % 513)*12) 12) tag
  | 7 => hashRow 520 520 (field storageWord (239950+(tag % 520)*11) 11) tag
  | 8 => hashRow 40 20 (field storageWord (285431+(tag % 20)*7) 7) tag
  | 9 => 0
  | _ => 0

def a17Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 12600 2 12672 1 12534 33 i
  | 5 => hintsAt storageWord 60767 9 67805 8 53815 44 i
  | 6 => hintsAt storageWord 149756 13 169750 9 136071 35 i
  | 7 => hintsAt storageWord 249051 12 255303 8 245670 21 i
  | 8 => hintsAt storageWord 285646 8 285974 4 285571 5 i
  | _ => []

def a17 : Atlas := ⟨9,rawDecor 55 a17Pos a17Neg,repeatWord 16927620312460216520,a17Count,a17Rec,(fun _ _ => 0),a17Loc⟩
def a17Domains : Catalog := [(repeatWord 7378697629483820646, 7), (repeatWord 6148914692668172970, 7), (repeatWord 4340410370284600380, 7), (repeatWord 12297829382473034410, 6), (repeatWord 3689348814741910323, 6), (repeatWord 1085102592571150095, 6), (repeatWord 18446744069414584320, 6), (repeatWord 11068046444225730969, 6), (repeatWord 11936128518282651045, 6), (repeatWord 6510615555426900570, 6), (repeatWord 14757395256390660915, 6), (repeatWord 3689348817318890700, 6), (repeatWord 17361641477348724495, 6), (repeatWord 6148914691236517205, 5), (repeatWord 14757395258967641292, 5), (repeatWord 281470681808895, 5), (repeatWord 4294967295, 5), (repeatWord 12297735558912431445, 5), (repeatWord 6149008514797120170, 5), (repeatWord 14757226376558555955, 5), (repeatWord 3689517697150995660, 5), (repeatWord 17361393124654452495, 5), (repeatWord 281474976645120, 5), (repeatWord 17361641481138401520, 4), (repeatWord 18446462603027742720, 4), (repeatWord 2459565876494606882, 4), (repeatWord 93823560602965, 4), (repeatWord 6148914689804861440, 4), (repeatWord 868082074056920076, 4), (repeatWord 18446462598732906495, 4), (repeatWord 723401728380766730, 3), (repeatWord 2863311530, 3), (repeatWord 3472328296227680304, 3), (repeatWord 3689348813882916864, 3), (repeatWord 1085102592318504960, 3)]
def a18Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x8119ea99c7d3beb, 0x377d3cae69d3bdd, 0xbdbeb30a])
  | 1 => BitVec.ofNat 152 (big [0xcf27874e283bcff, 0xfe81d3c7aefed3c, 0x751ee9e7])
  | 2 => BitVec.ofNat 152 (big [0xf7e075ba3586735, 0xd6dacad9fb75862, 0xcf571777])
  | 3 => BitVec.ofNat 152 (big [0xbcdf51e5dc3c2aa, 0x2d3fcf7116aa5db, 0x93c1edd2])
  | 4 => BitVec.ofNat 152 (big [0xa9abc7df7e5580, 0x697c6ced47116d3, 0xedfbbebb])
  | 5 => BitVec.ofNat 152 (big [0x39ffea802acde44, 0x9832733f58e9686, 0x36e868ac])
  | _ => 0

def a18Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x81116a9985432eb, 0x252418a8695680c, 0xff18904a])
  | 1 => BitVec.ofNat 152 (big [0x602800e0839cc7, 0xa8413062880120, 0x7412110f])
  | 2 => BitVec.ofNat 152 (big [0xe1e065203582330, 0xd0002051c335040, 0x89450260])
  | 3 => BitVec.ofNat 152 (big [0x1c5d11c15c34228, 0x49bcc6004804dc, 0xb80e5c0])
  | 4 => BitVec.ofNat 152 (big [0xa8a947ce2c5580, 0xa85c7595a601413, 0x44e2381b])
  | 5 => BitVec.ofNat 152 (big [0x79bfea80228cc04, 0x9030671915682ae, 0x20828a1])
  | _ => 0

def a18Count (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | _ => 0

def a18Rec (k i : Nat) : Nat :=
  match k with
  | 9 => field storageWord (286955+i*6) 6
  | _ => 0

def a18Loc (k tag : Nat) : Nat :=
  match k with
  | 9 => 0
  | _ => 0

def a18Hints (k i : Nat) : List Nat :=
  match k with
  | 9 => hintsAt storageWord 286962 1 286964 1 286961 1 i
  | _ => []

def a18 : Atlas := ⟨9,rawDecor 63 a18Pos a18Neg,repeatWord 18368771970383792320,a18Count,a18Rec,(fun _ _ => 0),a18Loc⟩
def a18Domains : Catalog := [(repeatWord 72056494543077120, 10)]
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
theorem a1S1P0 : segment (checkRow a1 a1Domains a1Hints 1) 0 2 = true := by decide +kernel
theorem a1S1 (j : Nat) (hj : j < 2) : (checkRow a1 a1Domains a1Hints 1) j = true := by
  exact segmentRange a1S1P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S2P0 : segment (checkRow a1 a1Domains a1Hints 2) 0 4 = true := by decide +kernel
theorem a1S2 (j : Nat) (hj : j < 4) : (checkRow a1 a1Domains a1Hints 2) j = true := by
  exact segmentRange a1S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S3P0 : segment (checkRow a1 a1Domains a1Hints 3) 0 1 = true := by decide +kernel
theorem a1S3 (j : Nat) (hj : j < 1) : (checkRow a1 a1Domains a1Hints 3) j = true := by
  exact segmentRange a1S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Complete : Complete a1 a1Domains a1Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a1S1 j hj
  · exact a1S2 j hj
  · exact a1S3 j hj
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
theorem a3S3P0 : segment (checkRow a3 a3Domains a3Hints 3) 0 2 = true := by decide +kernel
theorem a3S3 (j : Nat) (hj : j < 2) : (checkRow a3 a3Domains a3Hints 3) j = true := by
  exact segmentRange a3S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S4P0 : segment (checkRow a3 a3Domains a3Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S4P1 : segment (checkRow a3 a3Domains a3Hints 4) 10 3 = true := by decide +kernel
theorem a3S4 (j : Nat) (hj : j < 13) : (checkRow a3 a3Domains a3Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a3S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a3S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S5P0 : segment (checkRow a3 a3Domains a3Hints 5) 0 5 = true := by decide +kernel
theorem a3S5 (j : Nat) (hj : j < 5) : (checkRow a3 a3Domains a3Hints 5) j = true := by
  exact segmentRange a3S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S6P0 : segment (checkRow a3 a3Domains a3Hints 6) 0 1 = true := by decide +kernel
theorem a3S6 (j : Nat) (hj : j < 1) : (checkRow a3 a3Domains a3Hints 6) j = true := by
  exact segmentRange a3S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Complete : Complete a3 a3Domains a3Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a3S3 j hj
  · exact a3S4 j hj
  · exact a3S5 j hj
  · exact a3S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S2P0 : segment (checkRow a4 a4Domains a4Hints 2) 0 1 = true := by decide +kernel
theorem a4S2 (j : Nat) (hj : j < 1) : (checkRow a4 a4Domains a4Hints 2) j = true := by
  exact segmentRange a4S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Complete : Complete a4 a4Domains a4Hints := by
  intro k hk j hj
  change k ≤ 2 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a4S2 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S3P0 : segment (checkRow a5 a5Domains a5Hints 3) 0 8 = true := by decide +kernel
theorem a5S3 (j : Nat) (hj : j < 8) : (checkRow a5 a5Domains a5Hints 3) j = true := by
  exact segmentRange a5S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S4P0 : segment (checkRow a5 a5Domains a5Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S4P1 : segment (checkRow a5 a5Domains a5Hints 4) 10 8 = true := by decide +kernel
theorem a5S4 (j : Nat) (hj : j < 18) : (checkRow a5 a5Domains a5Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a5S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a5S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S5P0 : segment (checkRow a5 a5Domains a5Hints 5) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S5P1 : segment (checkRow a5 a5Domains a5Hints 5) 10 2 = true := by decide +kernel
theorem a5S5 (j : Nat) (hj : j < 12) : (checkRow a5 a5Domains a5Hints 5) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a5S5P0 j (by omega) (by omega)
  ·
    exact segmentRange a5S5P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S6P0 : segment (checkRow a5 a5Domains a5Hints 6) 0 1 = true := by decide +kernel
theorem a5S6 (j : Nat) (hj : j < 1) : (checkRow a5 a5Domains a5Hints 6) j = true := by
  exact segmentRange a5S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Complete : Complete a5 a5Domains a5Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a5S3 j hj
  · exact a5S4 j hj
  · exact a5S5 j hj
  · exact a5S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S2P0 : segment (checkRow a6 a6Domains a6Hints 2) 0 2 = true := by decide +kernel
theorem a6S2 (j : Nat) (hj : j < 2) : (checkRow a6 a6Domains a6Hints 2) j = true := by
  exact segmentRange a6S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S3P0 : segment (checkRow a6 a6Domains a6Hints 3) 0 6 = true := by decide +kernel
theorem a6S3 (j : Nat) (hj : j < 6) : (checkRow a6 a6Domains a6Hints 3) j = true := by
  exact segmentRange a6S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S4P0 : segment (checkRow a6 a6Domains a6Hints 4) 0 6 = true := by decide +kernel
theorem a6S4 (j : Nat) (hj : j < 6) : (checkRow a6 a6Domains a6Hints 4) j = true := by
  exact segmentRange a6S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P0 : segment (checkRow a6 a6Domains a6Hints 5) 0 1 = true := by decide +kernel
theorem a6S5 (j : Nat) (hj : j < 1) : (checkRow a6 a6Domains a6Hints 5) j = true := by
  exact segmentRange a6S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Complete : Complete a6 a6Domains a6Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a6S2 j hj
  · exact a6S3 j hj
  · exact a6S4 j hj
  · exact a6S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7S4P0 : segment (checkRow a7 a7Domains a7Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7S4P1 : segment (checkRow a7 a7Domains a7Hints 4) 10 2 = true := by decide +kernel
theorem a7S4 (j : Nat) (hj : j < 12) : (checkRow a7 a7Domains a7Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a7S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a7S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7S5P0 : segment (checkRow a7 a7Domains a7Hints 5) 0 1 = true := by decide +kernel
theorem a7S5 (j : Nat) (hj : j < 1) : (checkRow a7 a7Domains a7Hints 5) j = true := by
  exact segmentRange a7S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Complete : Complete a7 a7Domains a7Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a7S4 j hj
  · exact a7S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S3P0 : segment (checkRow a8 a8Domains a8Hints 3) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S3P1 : segment (checkRow a8 a8Domains a8Hints 3) 10 5 = true := by decide +kernel
theorem a8S3 (j : Nat) (hj : j < 15) : (checkRow a8 a8Domains a8Hints 3) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a8S3P0 j (by omega) (by omega)
  ·
    exact segmentRange a8S3P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S4P0 : segment (checkRow a8 a8Domains a8Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S4P1 : segment (checkRow a8 a8Domains a8Hints 4) 10 2 = true := by decide +kernel
theorem a8S4 (j : Nat) (hj : j < 12) : (checkRow a8 a8Domains a8Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a8S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a8S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P0 : segment (checkRow a8 a8Domains a8Hints 5) 0 1 = true := by decide +kernel
theorem a8S5 (j : Nat) (hj : j < 1) : (checkRow a8 a8Domains a8Hints 5) j = true := by
  exact segmentRange a8S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Complete : Complete a8 a8Domains a8Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a8S3 j hj
  · exact a8S4 j hj
  · exact a8S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S1P0 : segment (checkRow a9 a9Domains a9Hints 1) 0 9 = true := by decide +kernel
theorem a9S1 (j : Nat) (hj : j < 9) : (checkRow a9 a9Domains a9Hints 1) j = true := by
  exact segmentRange a9S1P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P0 : segment (checkRow a9 a9Domains a9Hints 2) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P1 : segment (checkRow a9 a9Domains a9Hints 2) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P2 : segment (checkRow a9 a9Domains a9Hints 2) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P3 : segment (checkRow a9 a9Domains a9Hints 2) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P4 : segment (checkRow a9 a9Domains a9Hints 2) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P5 : segment (checkRow a9 a9Domains a9Hints 2) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S2P6 : segment (checkRow a9 a9Domains a9Hints 2) 60 2 = true := by decide +kernel
theorem a9S2 (j : Nat) (hj : j < 62) : (checkRow a9 a9Domains a9Hints 2) j = true := by
  by_cases bound : j < 30
  ·
    by_cases bound : j < 10
    ·
      exact segmentRange a9S2P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 20
      ·
        exact segmentRange a9S2P1 j (by omega) (by omega)
      ·
        exact segmentRange a9S2P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 50
    ·
      by_cases bound : j < 40
      ·
        exact segmentRange a9S2P3 j (by omega) (by omega)
      ·
        exact segmentRange a9S2P4 j (by omega) (by omega)
    ·
      by_cases bound : j < 60
      ·
        exact segmentRange a9S2P5 j (by omega) (by omega)
      ·
        exact segmentRange a9S2P6 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P0 : segment (checkRow a9 a9Domains a9Hints 3) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P1 : segment (checkRow a9 a9Domains a9Hints 3) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P2 : segment (checkRow a9 a9Domains a9Hints 3) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P3 : segment (checkRow a9 a9Domains a9Hints 3) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P4 : segment (checkRow a9 a9Domains a9Hints 3) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P5 : segment (checkRow a9 a9Domains a9Hints 3) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P6 : segment (checkRow a9 a9Domains a9Hints 3) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P7 : segment (checkRow a9 a9Domains a9Hints 3) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P8 : segment (checkRow a9 a9Domains a9Hints 3) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P9 : segment (checkRow a9 a9Domains a9Hints 3) 90 5 = true := by decide +kernel
theorem a9S3 (j : Nat) (hj : j < 95) : (checkRow a9 a9Domains a9Hints 3) j = true := by
  by_cases bound : j < 50
  ·
    by_cases bound : j < 20
    ·
      by_cases bound : j < 10
      ·
        exact segmentRange a9S3P0 j (by omega) (by omega)
      ·
        exact segmentRange a9S3P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 30
      ·
        exact segmentRange a9S3P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 40
        ·
          exact segmentRange a9S3P3 j (by omega) (by omega)
        ·
          exact segmentRange a9S3P4 j (by omega) (by omega)
  ·
    by_cases bound : j < 70
    ·
      by_cases bound : j < 60
      ·
        exact segmentRange a9S3P5 j (by omega) (by omega)
      ·
        exact segmentRange a9S3P6 j (by omega) (by omega)
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a9S3P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 90
        ·
          exact segmentRange a9S3P8 j (by omega) (by omega)
        ·
          exact segmentRange a9S3P9 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S4P0 : segment (checkRow a9 a9Domains a9Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S4P1 : segment (checkRow a9 a9Domains a9Hints 4) 10 2 = true := by decide +kernel
theorem a9S4 (j : Nat) (hj : j < 12) : (checkRow a9 a9Domains a9Hints 4) j = true := by
  by_cases bound : j < 10
  ·
    exact segmentRange a9S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a9S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S5P0 : segment (checkRow a9 a9Domains a9Hints 5) 0 1 = true := by decide +kernel
theorem a9S5 (j : Nat) (hj : j < 1) : (checkRow a9 a9Domains a9Hints 5) j = true := by
  exact segmentRange a9S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Complete : Complete a9 a9Domains a9Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a9S1 j hj
  · exact a9S2 j hj
  · exact a9S3 j hj
  · exact a9S4 j hj
  · exact a9S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S5P0 : segment (checkRow a10 a10Domains a10Hints 5) 0 1 = true := by decide +kernel
theorem a10S5 (j : Nat) (hj : j < 1) : (checkRow a10 a10Domains a10Hints 5) j = true := by
  exact segmentRange a10S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Complete : Complete a10 a10Domains a10Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a10S5 j hj
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
theorem a12S4P0 : segment (checkRow a12 a12Domains a12Hints 4) 0 1 = true := by decide +kernel
theorem a12S4 (j : Nat) (hj : j < 1) : (checkRow a12 a12Domains a12Hints 4) j = true := by
  exact segmentRange a12S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Complete : Complete a12 a12Domains a12Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a12S4 j hj
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
theorem a14S4P0 : segment (checkRow a14 a14Domains a14Hints 4) 0 1 = true := by decide +kernel
theorem a14S4 (j : Nat) (hj : j < 1) : (checkRow a14 a14Domains a14Hints 4) j = true := by
  exact segmentRange a14S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Complete : Complete a14 a14Domains a14Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a14S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S3P0 : segment (checkRow a15 a15Domains a15Hints 3) 0 1 = true := by decide +kernel
theorem a15S3 (j : Nat) (hj : j < 1) : (checkRow a15 a15Domains a15Hints 3) j = true := by
  exact segmentRange a15S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Complete : Complete a15 a15Domains a15Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a15S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S3P0 : segment (checkRow a16 a16Domains a16Hints 3) 0 1 = true := by decide +kernel
theorem a16S3 (j : Nat) (hj : j < 1) : (checkRow a16 a16Domains a16Hints 3) j = true := by
  exact segmentRange a16S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Complete : Complete a16 a16Domains a16Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a16S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S4P0 : segment (checkRow a17 a17Domains a17Hints 4) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S4P1 : segment (checkRow a17 a17Domains a17Hints 4) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S4P2 : segment (checkRow a17 a17Domains a17Hints 4) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S4P3 : segment (checkRow a17 a17Domains a17Hints 4) 30 5 = true := by decide +kernel
theorem a17S4 (j : Nat) (hj : j < 35) : (checkRow a17 a17Domains a17Hints 4) j = true := by
  by_cases bound : j < 20
  ·
    by_cases bound : j < 10
    ·
      exact segmentRange a17S4P0 j (by omega) (by omega)
    ·
      exact segmentRange a17S4P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 30
    ·
      exact segmentRange a17S4P2 j (by omega) (by omega)
    ·
      exact segmentRange a17S4P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P0 : segment (checkRow a17 a17Domains a17Hints 5) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P1 : segment (checkRow a17 a17Domains a17Hints 5) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P2 : segment (checkRow a17 a17Domains a17Hints 5) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P3 : segment (checkRow a17 a17Domains a17Hints 5) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P4 : segment (checkRow a17 a17Domains a17Hints 5) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P5 : segment (checkRow a17 a17Domains a17Hints 5) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P6 : segment (checkRow a17 a17Domains a17Hints 5) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P7 : segment (checkRow a17 a17Domains a17Hints 5) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P8 : segment (checkRow a17 a17Domains a17Hints 5) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P9 : segment (checkRow a17 a17Domains a17Hints 5) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P10 : segment (checkRow a17 a17Domains a17Hints 5) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P11 : segment (checkRow a17 a17Domains a17Hints 5) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P12 : segment (checkRow a17 a17Domains a17Hints 5) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P13 : segment (checkRow a17 a17Domains a17Hints 5) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P14 : segment (checkRow a17 a17Domains a17Hints 5) 140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P15 : segment (checkRow a17 a17Domains a17Hints 5) 150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P16 : segment (checkRow a17 a17Domains a17Hints 5) 160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P17 : segment (checkRow a17 a17Domains a17Hints 5) 170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P18 : segment (checkRow a17 a17Domains a17Hints 5) 180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P19 : segment (checkRow a17 a17Domains a17Hints 5) 190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P20 : segment (checkRow a17 a17Domains a17Hints 5) 200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P21 : segment (checkRow a17 a17Domains a17Hints 5) 210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P22 : segment (checkRow a17 a17Domains a17Hints 5) 220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P23 : segment (checkRow a17 a17Domains a17Hints 5) 230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P24 : segment (checkRow a17 a17Domains a17Hints 5) 240 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P25 : segment (checkRow a17 a17Domains a17Hints 5) 250 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P26 : segment (checkRow a17 a17Domains a17Hints 5) 260 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P27 : segment (checkRow a17 a17Domains a17Hints 5) 270 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P28 : segment (checkRow a17 a17Domains a17Hints 5) 280 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P29 : segment (checkRow a17 a17Domains a17Hints 5) 290 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P30 : segment (checkRow a17 a17Domains a17Hints 5) 300 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P31 : segment (checkRow a17 a17Domains a17Hints 5) 310 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P32 : segment (checkRow a17 a17Domains a17Hints 5) 320 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P33 : segment (checkRow a17 a17Domains a17Hints 5) 330 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P34 : segment (checkRow a17 a17Domains a17Hints 5) 340 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P35 : segment (checkRow a17 a17Domains a17Hints 5) 350 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P36 : segment (checkRow a17 a17Domains a17Hints 5) 360 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P37 : segment (checkRow a17 a17Domains a17Hints 5) 370 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P38 : segment (checkRow a17 a17Domains a17Hints 5) 380 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P39 : segment (checkRow a17 a17Domains a17Hints 5) 390 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P40 : segment (checkRow a17 a17Domains a17Hints 5) 400 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P41 : segment (checkRow a17 a17Domains a17Hints 5) 410 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P42 : segment (checkRow a17 a17Domains a17Hints 5) 420 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P43 : segment (checkRow a17 a17Domains a17Hints 5) 430 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P44 : segment (checkRow a17 a17Domains a17Hints 5) 440 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P45 : segment (checkRow a17 a17Domains a17Hints 5) 450 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P46 : segment (checkRow a17 a17Domains a17Hints 5) 460 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P47 : segment (checkRow a17 a17Domains a17Hints 5) 470 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P48 : segment (checkRow a17 a17Domains a17Hints 5) 480 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P49 : segment (checkRow a17 a17Domains a17Hints 5) 490 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P50 : segment (checkRow a17 a17Domains a17Hints 5) 500 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P51 : segment (checkRow a17 a17Domains a17Hints 5) 510 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P52 : segment (checkRow a17 a17Domains a17Hints 5) 520 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P53 : segment (checkRow a17 a17Domains a17Hints 5) 530 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P54 : segment (checkRow a17 a17Domains a17Hints 5) 540 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P55 : segment (checkRow a17 a17Domains a17Hints 5) 550 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P56 : segment (checkRow a17 a17Domains a17Hints 5) 560 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P57 : segment (checkRow a17 a17Domains a17Hints 5) 570 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P58 : segment (checkRow a17 a17Domains a17Hints 5) 580 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P59 : segment (checkRow a17 a17Domains a17Hints 5) 590 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P60 : segment (checkRow a17 a17Domains a17Hints 5) 600 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P61 : segment (checkRow a17 a17Domains a17Hints 5) 610 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P62 : segment (checkRow a17 a17Domains a17Hints 5) 620 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P63 : segment (checkRow a17 a17Domains a17Hints 5) 630 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P64 : segment (checkRow a17 a17Domains a17Hints 5) 640 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P65 : segment (checkRow a17 a17Domains a17Hints 5) 650 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P66 : segment (checkRow a17 a17Domains a17Hints 5) 660 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P67 : segment (checkRow a17 a17Domains a17Hints 5) 670 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P68 : segment (checkRow a17 a17Domains a17Hints 5) 680 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P69 : segment (checkRow a17 a17Domains a17Hints 5) 690 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P70 : segment (checkRow a17 a17Domains a17Hints 5) 700 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P71 : segment (checkRow a17 a17Domains a17Hints 5) 710 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P72 : segment (checkRow a17 a17Domains a17Hints 5) 720 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P73 : segment (checkRow a17 a17Domains a17Hints 5) 730 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P74 : segment (checkRow a17 a17Domains a17Hints 5) 740 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P75 : segment (checkRow a17 a17Domains a17Hints 5) 750 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P76 : segment (checkRow a17 a17Domains a17Hints 5) 760 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P77 : segment (checkRow a17 a17Domains a17Hints 5) 770 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P78 : segment (checkRow a17 a17Domains a17Hints 5) 780 1 = true := by decide +kernel
theorem a17S5 (j : Nat) (hj : j < 781) : (checkRow a17 a17Domains a17Hints 5) j = true := by
  by_cases bound : j < 390
  ·
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
              exact segmentRange a17S5P0 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P1 j (by omega) (by omega)
          ·
            by_cases bound : j < 30
            ·
              exact segmentRange a17S5P2 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P3 j (by omega) (by omega)
        ·
          by_cases bound : j < 60
          ·
            by_cases bound : j < 50
            ·
              exact segmentRange a17S5P4 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P5 j (by omega) (by omega)
          ·
            by_cases bound : j < 70
            ·
              exact segmentRange a17S5P6 j (by omega) (by omega)
            ·
              by_cases bound : j < 80
              ·
                exact segmentRange a17S5P7 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P8 j (by omega) (by omega)
      ·
        by_cases bound : j < 140
        ·
          by_cases bound : j < 110
          ·
            by_cases bound : j < 100
            ·
              exact segmentRange a17S5P9 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P10 j (by omega) (by omega)
          ·
            by_cases bound : j < 120
            ·
              exact segmentRange a17S5P11 j (by omega) (by omega)
            ·
              by_cases bound : j < 130
              ·
                exact segmentRange a17S5P12 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P13 j (by omega) (by omega)
        ·
          by_cases bound : j < 160
          ·
            by_cases bound : j < 150
            ·
              exact segmentRange a17S5P14 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P15 j (by omega) (by omega)
          ·
            by_cases bound : j < 170
            ·
              exact segmentRange a17S5P16 j (by omega) (by omega)
            ·
              by_cases bound : j < 180
              ·
                exact segmentRange a17S5P17 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P18 j (by omega) (by omega)
    ·
      by_cases bound : j < 290
      ·
        by_cases bound : j < 240
        ·
          by_cases bound : j < 210
          ·
            by_cases bound : j < 200
            ·
              exact segmentRange a17S5P19 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P20 j (by omega) (by omega)
          ·
            by_cases bound : j < 220
            ·
              exact segmentRange a17S5P21 j (by omega) (by omega)
            ·
              by_cases bound : j < 230
              ·
                exact segmentRange a17S5P22 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P23 j (by omega) (by omega)
        ·
          by_cases bound : j < 260
          ·
            by_cases bound : j < 250
            ·
              exact segmentRange a17S5P24 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P25 j (by omega) (by omega)
          ·
            by_cases bound : j < 270
            ·
              exact segmentRange a17S5P26 j (by omega) (by omega)
            ·
              by_cases bound : j < 280
              ·
                exact segmentRange a17S5P27 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P28 j (by omega) (by omega)
      ·
        by_cases bound : j < 340
        ·
          by_cases bound : j < 310
          ·
            by_cases bound : j < 300
            ·
              exact segmentRange a17S5P29 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P30 j (by omega) (by omega)
          ·
            by_cases bound : j < 320
            ·
              exact segmentRange a17S5P31 j (by omega) (by omega)
            ·
              by_cases bound : j < 330
              ·
                exact segmentRange a17S5P32 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P33 j (by omega) (by omega)
        ·
          by_cases bound : j < 360
          ·
            by_cases bound : j < 350
            ·
              exact segmentRange a17S5P34 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P35 j (by omega) (by omega)
          ·
            by_cases bound : j < 370
            ·
              exact segmentRange a17S5P36 j (by omega) (by omega)
            ·
              by_cases bound : j < 380
              ·
                exact segmentRange a17S5P37 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P38 j (by omega) (by omega)
  ·
    by_cases bound : j < 590
    ·
      by_cases bound : j < 490
      ·
        by_cases bound : j < 440
        ·
          by_cases bound : j < 410
          ·
            by_cases bound : j < 400
            ·
              exact segmentRange a17S5P39 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P40 j (by omega) (by omega)
          ·
            by_cases bound : j < 420
            ·
              exact segmentRange a17S5P41 j (by omega) (by omega)
            ·
              by_cases bound : j < 430
              ·
                exact segmentRange a17S5P42 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P43 j (by omega) (by omega)
        ·
          by_cases bound : j < 460
          ·
            by_cases bound : j < 450
            ·
              exact segmentRange a17S5P44 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P45 j (by omega) (by omega)
          ·
            by_cases bound : j < 470
            ·
              exact segmentRange a17S5P46 j (by omega) (by omega)
            ·
              by_cases bound : j < 480
              ·
                exact segmentRange a17S5P47 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P48 j (by omega) (by omega)
      ·
        by_cases bound : j < 540
        ·
          by_cases bound : j < 510
          ·
            by_cases bound : j < 500
            ·
              exact segmentRange a17S5P49 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P50 j (by omega) (by omega)
          ·
            by_cases bound : j < 520
            ·
              exact segmentRange a17S5P51 j (by omega) (by omega)
            ·
              by_cases bound : j < 530
              ·
                exact segmentRange a17S5P52 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P53 j (by omega) (by omega)
        ·
          by_cases bound : j < 560
          ·
            by_cases bound : j < 550
            ·
              exact segmentRange a17S5P54 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P55 j (by omega) (by omega)
          ·
            by_cases bound : j < 570
            ·
              exact segmentRange a17S5P56 j (by omega) (by omega)
            ·
              by_cases bound : j < 580
              ·
                exact segmentRange a17S5P57 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P58 j (by omega) (by omega)
    ·
      by_cases bound : j < 690
      ·
        by_cases bound : j < 640
        ·
          by_cases bound : j < 610
          ·
            by_cases bound : j < 600
            ·
              exact segmentRange a17S5P59 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P60 j (by omega) (by omega)
          ·
            by_cases bound : j < 620
            ·
              exact segmentRange a17S5P61 j (by omega) (by omega)
            ·
              by_cases bound : j < 630
              ·
                exact segmentRange a17S5P62 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P63 j (by omega) (by omega)
        ·
          by_cases bound : j < 660
          ·
            by_cases bound : j < 650
            ·
              exact segmentRange a17S5P64 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P65 j (by omega) (by omega)
          ·
            by_cases bound : j < 670
            ·
              exact segmentRange a17S5P66 j (by omega) (by omega)
            ·
              by_cases bound : j < 680
              ·
                exact segmentRange a17S5P67 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P68 j (by omega) (by omega)
      ·
        by_cases bound : j < 740
        ·
          by_cases bound : j < 710
          ·
            by_cases bound : j < 700
            ·
              exact segmentRange a17S5P69 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P70 j (by omega) (by omega)
          ·
            by_cases bound : j < 720
            ·
              exact segmentRange a17S5P71 j (by omega) (by omega)
            ·
              by_cases bound : j < 730
              ·
                exact segmentRange a17S5P72 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P73 j (by omega) (by omega)
        ·
          by_cases bound : j < 760
          ·
            by_cases bound : j < 750
            ·
              exact segmentRange a17S5P74 j (by omega) (by omega)
            ·
              exact segmentRange a17S5P75 j (by omega) (by omega)
          ·
            by_cases bound : j < 770
            ·
              exact segmentRange a17S5P76 j (by omega) (by omega)
            ·
              by_cases bound : j < 780
              ·
                exact segmentRange a17S5P77 j (by omega) (by omega)
              ·
                exact segmentRange a17S5P78 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P0 : segment (checkRow a17 a17Domains a17Hints 6) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P1 : segment (checkRow a17 a17Domains a17Hints 6) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P2 : segment (checkRow a17 a17Domains a17Hints 6) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P3 : segment (checkRow a17 a17Domains a17Hints 6) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P4 : segment (checkRow a17 a17Domains a17Hints 6) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P5 : segment (checkRow a17 a17Domains a17Hints 6) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P6 : segment (checkRow a17 a17Domains a17Hints 6) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P7 : segment (checkRow a17 a17Domains a17Hints 6) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P8 : segment (checkRow a17 a17Domains a17Hints 6) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P9 : segment (checkRow a17 a17Domains a17Hints 6) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P10 : segment (checkRow a17 a17Domains a17Hints 6) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P11 : segment (checkRow a17 a17Domains a17Hints 6) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P12 : segment (checkRow a17 a17Domains a17Hints 6) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P13 : segment (checkRow a17 a17Domains a17Hints 6) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P14 : segment (checkRow a17 a17Domains a17Hints 6) 140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P15 : segment (checkRow a17 a17Domains a17Hints 6) 150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P16 : segment (checkRow a17 a17Domains a17Hints 6) 160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P17 : segment (checkRow a17 a17Domains a17Hints 6) 170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P18 : segment (checkRow a17 a17Domains a17Hints 6) 180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P19 : segment (checkRow a17 a17Domains a17Hints 6) 190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P20 : segment (checkRow a17 a17Domains a17Hints 6) 200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P21 : segment (checkRow a17 a17Domains a17Hints 6) 210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P22 : segment (checkRow a17 a17Domains a17Hints 6) 220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P23 : segment (checkRow a17 a17Domains a17Hints 6) 230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P24 : segment (checkRow a17 a17Domains a17Hints 6) 240 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P25 : segment (checkRow a17 a17Domains a17Hints 6) 250 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P26 : segment (checkRow a17 a17Domains a17Hints 6) 260 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P27 : segment (checkRow a17 a17Domains a17Hints 6) 270 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P28 : segment (checkRow a17 a17Domains a17Hints 6) 280 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P29 : segment (checkRow a17 a17Domains a17Hints 6) 290 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P30 : segment (checkRow a17 a17Domains a17Hints 6) 300 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P31 : segment (checkRow a17 a17Domains a17Hints 6) 310 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P32 : segment (checkRow a17 a17Domains a17Hints 6) 320 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P33 : segment (checkRow a17 a17Domains a17Hints 6) 330 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P34 : segment (checkRow a17 a17Domains a17Hints 6) 340 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P35 : segment (checkRow a17 a17Domains a17Hints 6) 350 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P36 : segment (checkRow a17 a17Domains a17Hints 6) 360 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P37 : segment (checkRow a17 a17Domains a17Hints 6) 370 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P38 : segment (checkRow a17 a17Domains a17Hints 6) 380 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P39 : segment (checkRow a17 a17Domains a17Hints 6) 390 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P40 : segment (checkRow a17 a17Domains a17Hints 6) 400 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P41 : segment (checkRow a17 a17Domains a17Hints 6) 410 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P42 : segment (checkRow a17 a17Domains a17Hints 6) 420 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P43 : segment (checkRow a17 a17Domains a17Hints 6) 430 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P44 : segment (checkRow a17 a17Domains a17Hints 6) 440 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P45 : segment (checkRow a17 a17Domains a17Hints 6) 450 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P46 : segment (checkRow a17 a17Domains a17Hints 6) 460 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P47 : segment (checkRow a17 a17Domains a17Hints 6) 470 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P48 : segment (checkRow a17 a17Domains a17Hints 6) 480 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P49 : segment (checkRow a17 a17Domains a17Hints 6) 490 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P50 : segment (checkRow a17 a17Domains a17Hints 6) 500 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P51 : segment (checkRow a17 a17Domains a17Hints 6) 510 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P52 : segment (checkRow a17 a17Domains a17Hints 6) 520 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P53 : segment (checkRow a17 a17Domains a17Hints 6) 530 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P54 : segment (checkRow a17 a17Domains a17Hints 6) 540 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P55 : segment (checkRow a17 a17Domains a17Hints 6) 550 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P56 : segment (checkRow a17 a17Domains a17Hints 6) 560 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P57 : segment (checkRow a17 a17Domains a17Hints 6) 570 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P58 : segment (checkRow a17 a17Domains a17Hints 6) 580 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P59 : segment (checkRow a17 a17Domains a17Hints 6) 590 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P60 : segment (checkRow a17 a17Domains a17Hints 6) 600 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P61 : segment (checkRow a17 a17Domains a17Hints 6) 610 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P62 : segment (checkRow a17 a17Domains a17Hints 6) 620 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P63 : segment (checkRow a17 a17Domains a17Hints 6) 630 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P64 : segment (checkRow a17 a17Domains a17Hints 6) 640 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P65 : segment (checkRow a17 a17Domains a17Hints 6) 650 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P66 : segment (checkRow a17 a17Domains a17Hints 6) 660 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P67 : segment (checkRow a17 a17Domains a17Hints 6) 670 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P68 : segment (checkRow a17 a17Domains a17Hints 6) 680 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P69 : segment (checkRow a17 a17Domains a17Hints 6) 690 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P70 : segment (checkRow a17 a17Domains a17Hints 6) 700 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P71 : segment (checkRow a17 a17Domains a17Hints 6) 710 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P72 : segment (checkRow a17 a17Domains a17Hints 6) 720 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P73 : segment (checkRow a17 a17Domains a17Hints 6) 730 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P74 : segment (checkRow a17 a17Domains a17Hints 6) 740 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P75 : segment (checkRow a17 a17Domains a17Hints 6) 750 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P76 : segment (checkRow a17 a17Domains a17Hints 6) 760 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P77 : segment (checkRow a17 a17Domains a17Hints 6) 770 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P78 : segment (checkRow a17 a17Domains a17Hints 6) 780 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P79 : segment (checkRow a17 a17Domains a17Hints 6) 790 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P80 : segment (checkRow a17 a17Domains a17Hints 6) 800 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P81 : segment (checkRow a17 a17Domains a17Hints 6) 810 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P82 : segment (checkRow a17 a17Domains a17Hints 6) 820 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P83 : segment (checkRow a17 a17Domains a17Hints 6) 830 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P84 : segment (checkRow a17 a17Domains a17Hints 6) 840 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P85 : segment (checkRow a17 a17Domains a17Hints 6) 850 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P86 : segment (checkRow a17 a17Domains a17Hints 6) 860 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P87 : segment (checkRow a17 a17Domains a17Hints 6) 870 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P88 : segment (checkRow a17 a17Domains a17Hints 6) 880 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P89 : segment (checkRow a17 a17Domains a17Hints 6) 890 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P90 : segment (checkRow a17 a17Domains a17Hints 6) 900 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P91 : segment (checkRow a17 a17Domains a17Hints 6) 910 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P92 : segment (checkRow a17 a17Domains a17Hints 6) 920 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P93 : segment (checkRow a17 a17Domains a17Hints 6) 930 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P94 : segment (checkRow a17 a17Domains a17Hints 6) 940 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P95 : segment (checkRow a17 a17Domains a17Hints 6) 950 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P96 : segment (checkRow a17 a17Domains a17Hints 6) 960 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P97 : segment (checkRow a17 a17Domains a17Hints 6) 970 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P98 : segment (checkRow a17 a17Domains a17Hints 6) 980 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P99 : segment (checkRow a17 a17Domains a17Hints 6) 990 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P100 : segment (checkRow a17 a17Domains a17Hints 6) 1000 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P101 : segment (checkRow a17 a17Domains a17Hints 6) 1010 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P102 : segment (checkRow a17 a17Domains a17Hints 6) 1020 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P103 : segment (checkRow a17 a17Domains a17Hints 6) 1030 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P104 : segment (checkRow a17 a17Domains a17Hints 6) 1040 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P105 : segment (checkRow a17 a17Domains a17Hints 6) 1050 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P106 : segment (checkRow a17 a17Domains a17Hints 6) 1060 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P107 : segment (checkRow a17 a17Domains a17Hints 6) 1070 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P108 : segment (checkRow a17 a17Domains a17Hints 6) 1080 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P109 : segment (checkRow a17 a17Domains a17Hints 6) 1090 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P110 : segment (checkRow a17 a17Domains a17Hints 6) 1100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P111 : segment (checkRow a17 a17Domains a17Hints 6) 1110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P112 : segment (checkRow a17 a17Domains a17Hints 6) 1120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P113 : segment (checkRow a17 a17Domains a17Hints 6) 1130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P114 : segment (checkRow a17 a17Domains a17Hints 6) 1140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P115 : segment (checkRow a17 a17Domains a17Hints 6) 1150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P116 : segment (checkRow a17 a17Domains a17Hints 6) 1160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P117 : segment (checkRow a17 a17Domains a17Hints 6) 1170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P118 : segment (checkRow a17 a17Domains a17Hints 6) 1180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P119 : segment (checkRow a17 a17Domains a17Hints 6) 1190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P120 : segment (checkRow a17 a17Domains a17Hints 6) 1200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P121 : segment (checkRow a17 a17Domains a17Hints 6) 1210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P122 : segment (checkRow a17 a17Domains a17Hints 6) 1220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P123 : segment (checkRow a17 a17Domains a17Hints 6) 1230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P124 : segment (checkRow a17 a17Domains a17Hints 6) 1240 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P125 : segment (checkRow a17 a17Domains a17Hints 6) 1250 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P126 : segment (checkRow a17 a17Domains a17Hints 6) 1260 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P127 : segment (checkRow a17 a17Domains a17Hints 6) 1270 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P128 : segment (checkRow a17 a17Domains a17Hints 6) 1280 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P129 : segment (checkRow a17 a17Domains a17Hints 6) 1290 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P130 : segment (checkRow a17 a17Domains a17Hints 6) 1300 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P131 : segment (checkRow a17 a17Domains a17Hints 6) 1310 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P132 : segment (checkRow a17 a17Domains a17Hints 6) 1320 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P133 : segment (checkRow a17 a17Domains a17Hints 6) 1330 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P134 : segment (checkRow a17 a17Domains a17Hints 6) 1340 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P135 : segment (checkRow a17 a17Domains a17Hints 6) 1350 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P136 : segment (checkRow a17 a17Domains a17Hints 6) 1360 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P137 : segment (checkRow a17 a17Domains a17Hints 6) 1370 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P138 : segment (checkRow a17 a17Domains a17Hints 6) 1380 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P139 : segment (checkRow a17 a17Domains a17Hints 6) 1390 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P140 : segment (checkRow a17 a17Domains a17Hints 6) 1400 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P141 : segment (checkRow a17 a17Domains a17Hints 6) 1410 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P142 : segment (checkRow a17 a17Domains a17Hints 6) 1420 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P143 : segment (checkRow a17 a17Domains a17Hints 6) 1430 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P144 : segment (checkRow a17 a17Domains a17Hints 6) 1440 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P145 : segment (checkRow a17 a17Domains a17Hints 6) 1450 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P146 : segment (checkRow a17 a17Domains a17Hints 6) 1460 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P147 : segment (checkRow a17 a17Domains a17Hints 6) 1470 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P148 : segment (checkRow a17 a17Domains a17Hints 6) 1480 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P149 : segment (checkRow a17 a17Domains a17Hints 6) 1490 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P150 : segment (checkRow a17 a17Domains a17Hints 6) 1500 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P151 : segment (checkRow a17 a17Domains a17Hints 6) 1510 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P152 : segment (checkRow a17 a17Domains a17Hints 6) 1520 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P153 : segment (checkRow a17 a17Domains a17Hints 6) 1530 7 = true := by decide +kernel
theorem a17S6 (j : Nat) (hj : j < 1537) : (checkRow a17 a17Domains a17Hints 6) j = true := by
  by_cases bound : j < 770
  ·
    by_cases bound : j < 380
    ·
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
                exact segmentRange a17S6P0 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P1 j (by omega) (by omega)
            ·
              by_cases bound : j < 30
              ·
                exact segmentRange a17S6P2 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P3 j (by omega) (by omega)
          ·
            by_cases bound : j < 60
            ·
              by_cases bound : j < 50
              ·
                exact segmentRange a17S6P4 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P5 j (by omega) (by omega)
            ·
              by_cases bound : j < 70
              ·
                exact segmentRange a17S6P6 j (by omega) (by omega)
              ·
                by_cases bound : j < 80
                ·
                  exact segmentRange a17S6P7 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P8 j (by omega) (by omega)
        ·
          by_cases bound : j < 140
          ·
            by_cases bound : j < 110
            ·
              by_cases bound : j < 100
              ·
                exact segmentRange a17S6P9 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P10 j (by omega) (by omega)
            ·
              by_cases bound : j < 120
              ·
                exact segmentRange a17S6P11 j (by omega) (by omega)
              ·
                by_cases bound : j < 130
                ·
                  exact segmentRange a17S6P12 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P13 j (by omega) (by omega)
          ·
            by_cases bound : j < 160
            ·
              by_cases bound : j < 150
              ·
                exact segmentRange a17S6P14 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P15 j (by omega) (by omega)
            ·
              by_cases bound : j < 170
              ·
                exact segmentRange a17S6P16 j (by omega) (by omega)
              ·
                by_cases bound : j < 180
                ·
                  exact segmentRange a17S6P17 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P18 j (by omega) (by omega)
      ·
        by_cases bound : j < 280
        ·
          by_cases bound : j < 230
          ·
            by_cases bound : j < 210
            ·
              by_cases bound : j < 200
              ·
                exact segmentRange a17S6P19 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P20 j (by omega) (by omega)
            ·
              by_cases bound : j < 220
              ·
                exact segmentRange a17S6P21 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P22 j (by omega) (by omega)
          ·
            by_cases bound : j < 250
            ·
              by_cases bound : j < 240
              ·
                exact segmentRange a17S6P23 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P24 j (by omega) (by omega)
            ·
              by_cases bound : j < 260
              ·
                exact segmentRange a17S6P25 j (by omega) (by omega)
              ·
                by_cases bound : j < 270
                ·
                  exact segmentRange a17S6P26 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P27 j (by omega) (by omega)
        ·
          by_cases bound : j < 330
          ·
            by_cases bound : j < 300
            ·
              by_cases bound : j < 290
              ·
                exact segmentRange a17S6P28 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P29 j (by omega) (by omega)
            ·
              by_cases bound : j < 310
              ·
                exact segmentRange a17S6P30 j (by omega) (by omega)
              ·
                by_cases bound : j < 320
                ·
                  exact segmentRange a17S6P31 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P32 j (by omega) (by omega)
          ·
            by_cases bound : j < 350
            ·
              by_cases bound : j < 340
              ·
                exact segmentRange a17S6P33 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P34 j (by omega) (by omega)
            ·
              by_cases bound : j < 360
              ·
                exact segmentRange a17S6P35 j (by omega) (by omega)
              ·
                by_cases bound : j < 370
                ·
                  exact segmentRange a17S6P36 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P37 j (by omega) (by omega)
    ·
      by_cases bound : j < 570
      ·
        by_cases bound : j < 470
        ·
          by_cases bound : j < 420
          ·
            by_cases bound : j < 400
            ·
              by_cases bound : j < 390
              ·
                exact segmentRange a17S6P38 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P39 j (by omega) (by omega)
            ·
              by_cases bound : j < 410
              ·
                exact segmentRange a17S6P40 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P41 j (by omega) (by omega)
          ·
            by_cases bound : j < 440
            ·
              by_cases bound : j < 430
              ·
                exact segmentRange a17S6P42 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P43 j (by omega) (by omega)
            ·
              by_cases bound : j < 450
              ·
                exact segmentRange a17S6P44 j (by omega) (by omega)
              ·
                by_cases bound : j < 460
                ·
                  exact segmentRange a17S6P45 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P46 j (by omega) (by omega)
        ·
          by_cases bound : j < 520
          ·
            by_cases bound : j < 490
            ·
              by_cases bound : j < 480
              ·
                exact segmentRange a17S6P47 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P48 j (by omega) (by omega)
            ·
              by_cases bound : j < 500
              ·
                exact segmentRange a17S6P49 j (by omega) (by omega)
              ·
                by_cases bound : j < 510
                ·
                  exact segmentRange a17S6P50 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P51 j (by omega) (by omega)
          ·
            by_cases bound : j < 540
            ·
              by_cases bound : j < 530
              ·
                exact segmentRange a17S6P52 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P53 j (by omega) (by omega)
            ·
              by_cases bound : j < 550
              ·
                exact segmentRange a17S6P54 j (by omega) (by omega)
              ·
                by_cases bound : j < 560
                ·
                  exact segmentRange a17S6P55 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P56 j (by omega) (by omega)
      ·
        by_cases bound : j < 670
        ·
          by_cases bound : j < 620
          ·
            by_cases bound : j < 590
            ·
              by_cases bound : j < 580
              ·
                exact segmentRange a17S6P57 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P58 j (by omega) (by omega)
            ·
              by_cases bound : j < 600
              ·
                exact segmentRange a17S6P59 j (by omega) (by omega)
              ·
                by_cases bound : j < 610
                ·
                  exact segmentRange a17S6P60 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P61 j (by omega) (by omega)
          ·
            by_cases bound : j < 640
            ·
              by_cases bound : j < 630
              ·
                exact segmentRange a17S6P62 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P63 j (by omega) (by omega)
            ·
              by_cases bound : j < 650
              ·
                exact segmentRange a17S6P64 j (by omega) (by omega)
              ·
                by_cases bound : j < 660
                ·
                  exact segmentRange a17S6P65 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P66 j (by omega) (by omega)
        ·
          by_cases bound : j < 720
          ·
            by_cases bound : j < 690
            ·
              by_cases bound : j < 680
              ·
                exact segmentRange a17S6P67 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P68 j (by omega) (by omega)
            ·
              by_cases bound : j < 700
              ·
                exact segmentRange a17S6P69 j (by omega) (by omega)
              ·
                by_cases bound : j < 710
                ·
                  exact segmentRange a17S6P70 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P71 j (by omega) (by omega)
          ·
            by_cases bound : j < 740
            ·
              by_cases bound : j < 730
              ·
                exact segmentRange a17S6P72 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P73 j (by omega) (by omega)
            ·
              by_cases bound : j < 750
              ·
                exact segmentRange a17S6P74 j (by omega) (by omega)
              ·
                by_cases bound : j < 760
                ·
                  exact segmentRange a17S6P75 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P76 j (by omega) (by omega)
  ·
    by_cases bound : j < 1150
    ·
      by_cases bound : j < 960
      ·
        by_cases bound : j < 860
        ·
          by_cases bound : j < 810
          ·
            by_cases bound : j < 790
            ·
              by_cases bound : j < 780
              ·
                exact segmentRange a17S6P77 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P78 j (by omega) (by omega)
            ·
              by_cases bound : j < 800
              ·
                exact segmentRange a17S6P79 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P80 j (by omega) (by omega)
          ·
            by_cases bound : j < 830
            ·
              by_cases bound : j < 820
              ·
                exact segmentRange a17S6P81 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P82 j (by omega) (by omega)
            ·
              by_cases bound : j < 840
              ·
                exact segmentRange a17S6P83 j (by omega) (by omega)
              ·
                by_cases bound : j < 850
                ·
                  exact segmentRange a17S6P84 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P85 j (by omega) (by omega)
        ·
          by_cases bound : j < 910
          ·
            by_cases bound : j < 880
            ·
              by_cases bound : j < 870
              ·
                exact segmentRange a17S6P86 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P87 j (by omega) (by omega)
            ·
              by_cases bound : j < 890
              ·
                exact segmentRange a17S6P88 j (by omega) (by omega)
              ·
                by_cases bound : j < 900
                ·
                  exact segmentRange a17S6P89 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P90 j (by omega) (by omega)
          ·
            by_cases bound : j < 930
            ·
              by_cases bound : j < 920
              ·
                exact segmentRange a17S6P91 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P92 j (by omega) (by omega)
            ·
              by_cases bound : j < 940
              ·
                exact segmentRange a17S6P93 j (by omega) (by omega)
              ·
                by_cases bound : j < 950
                ·
                  exact segmentRange a17S6P94 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P95 j (by omega) (by omega)
      ·
        by_cases bound : j < 1050
        ·
          by_cases bound : j < 1000
          ·
            by_cases bound : j < 980
            ·
              by_cases bound : j < 970
              ·
                exact segmentRange a17S6P96 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P97 j (by omega) (by omega)
            ·
              by_cases bound : j < 990
              ·
                exact segmentRange a17S6P98 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P99 j (by omega) (by omega)
          ·
            by_cases bound : j < 1020
            ·
              by_cases bound : j < 1010
              ·
                exact segmentRange a17S6P100 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P101 j (by omega) (by omega)
            ·
              by_cases bound : j < 1030
              ·
                exact segmentRange a17S6P102 j (by omega) (by omega)
              ·
                by_cases bound : j < 1040
                ·
                  exact segmentRange a17S6P103 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P104 j (by omega) (by omega)
        ·
          by_cases bound : j < 1100
          ·
            by_cases bound : j < 1070
            ·
              by_cases bound : j < 1060
              ·
                exact segmentRange a17S6P105 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P106 j (by omega) (by omega)
            ·
              by_cases bound : j < 1080
              ·
                exact segmentRange a17S6P107 j (by omega) (by omega)
              ·
                by_cases bound : j < 1090
                ·
                  exact segmentRange a17S6P108 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P109 j (by omega) (by omega)
          ·
            by_cases bound : j < 1120
            ·
              by_cases bound : j < 1110
              ·
                exact segmentRange a17S6P110 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P111 j (by omega) (by omega)
            ·
              by_cases bound : j < 1130
              ·
                exact segmentRange a17S6P112 j (by omega) (by omega)
              ·
                by_cases bound : j < 1140
                ·
                  exact segmentRange a17S6P113 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P114 j (by omega) (by omega)
    ·
      by_cases bound : j < 1340
      ·
        by_cases bound : j < 1240
        ·
          by_cases bound : j < 1190
          ·
            by_cases bound : j < 1170
            ·
              by_cases bound : j < 1160
              ·
                exact segmentRange a17S6P115 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P116 j (by omega) (by omega)
            ·
              by_cases bound : j < 1180
              ·
                exact segmentRange a17S6P117 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P118 j (by omega) (by omega)
          ·
            by_cases bound : j < 1210
            ·
              by_cases bound : j < 1200
              ·
                exact segmentRange a17S6P119 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P120 j (by omega) (by omega)
            ·
              by_cases bound : j < 1220
              ·
                exact segmentRange a17S6P121 j (by omega) (by omega)
              ·
                by_cases bound : j < 1230
                ·
                  exact segmentRange a17S6P122 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P123 j (by omega) (by omega)
        ·
          by_cases bound : j < 1290
          ·
            by_cases bound : j < 1260
            ·
              by_cases bound : j < 1250
              ·
                exact segmentRange a17S6P124 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P125 j (by omega) (by omega)
            ·
              by_cases bound : j < 1270
              ·
                exact segmentRange a17S6P126 j (by omega) (by omega)
              ·
                by_cases bound : j < 1280
                ·
                  exact segmentRange a17S6P127 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P128 j (by omega) (by omega)
          ·
            by_cases bound : j < 1310
            ·
              by_cases bound : j < 1300
              ·
                exact segmentRange a17S6P129 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P130 j (by omega) (by omega)
            ·
              by_cases bound : j < 1320
              ·
                exact segmentRange a17S6P131 j (by omega) (by omega)
              ·
                by_cases bound : j < 1330
                ·
                  exact segmentRange a17S6P132 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P133 j (by omega) (by omega)
      ·
        by_cases bound : j < 1440
        ·
          by_cases bound : j < 1390
          ·
            by_cases bound : j < 1360
            ·
              by_cases bound : j < 1350
              ·
                exact segmentRange a17S6P134 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P135 j (by omega) (by omega)
            ·
              by_cases bound : j < 1370
              ·
                exact segmentRange a17S6P136 j (by omega) (by omega)
              ·
                by_cases bound : j < 1380
                ·
                  exact segmentRange a17S6P137 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P138 j (by omega) (by omega)
          ·
            by_cases bound : j < 1410
            ·
              by_cases bound : j < 1400
              ·
                exact segmentRange a17S6P139 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P140 j (by omega) (by omega)
            ·
              by_cases bound : j < 1420
              ·
                exact segmentRange a17S6P141 j (by omega) (by omega)
              ·
                by_cases bound : j < 1430
                ·
                  exact segmentRange a17S6P142 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P143 j (by omega) (by omega)
        ·
          by_cases bound : j < 1490
          ·
            by_cases bound : j < 1460
            ·
              by_cases bound : j < 1450
              ·
                exact segmentRange a17S6P144 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P145 j (by omega) (by omega)
            ·
              by_cases bound : j < 1470
              ·
                exact segmentRange a17S6P146 j (by omega) (by omega)
              ·
                by_cases bound : j < 1480
                ·
                  exact segmentRange a17S6P147 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P148 j (by omega) (by omega)
          ·
            by_cases bound : j < 1510
            ·
              by_cases bound : j < 1500
              ·
                exact segmentRange a17S6P149 j (by omega) (by omega)
              ·
                exact segmentRange a17S6P150 j (by omega) (by omega)
            ·
              by_cases bound : j < 1520
              ·
                exact segmentRange a17S6P151 j (by omega) (by omega)
              ·
                by_cases bound : j < 1530
                ·
                  exact segmentRange a17S6P152 j (by omega) (by omega)
                ·
                  exact segmentRange a17S6P153 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P0 : segment (checkRow a17 a17Domains a17Hints 7) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P1 : segment (checkRow a17 a17Domains a17Hints 7) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P2 : segment (checkRow a17 a17Domains a17Hints 7) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P3 : segment (checkRow a17 a17Domains a17Hints 7) 30 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P4 : segment (checkRow a17 a17Domains a17Hints 7) 40 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P5 : segment (checkRow a17 a17Domains a17Hints 7) 50 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P6 : segment (checkRow a17 a17Domains a17Hints 7) 60 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P7 : segment (checkRow a17 a17Domains a17Hints 7) 70 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P8 : segment (checkRow a17 a17Domains a17Hints 7) 80 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P9 : segment (checkRow a17 a17Domains a17Hints 7) 90 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P10 : segment (checkRow a17 a17Domains a17Hints 7) 100 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P11 : segment (checkRow a17 a17Domains a17Hints 7) 110 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P12 : segment (checkRow a17 a17Domains a17Hints 7) 120 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P13 : segment (checkRow a17 a17Domains a17Hints 7) 130 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P14 : segment (checkRow a17 a17Domains a17Hints 7) 140 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P15 : segment (checkRow a17 a17Domains a17Hints 7) 150 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P16 : segment (checkRow a17 a17Domains a17Hints 7) 160 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P17 : segment (checkRow a17 a17Domains a17Hints 7) 170 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P18 : segment (checkRow a17 a17Domains a17Hints 7) 180 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P19 : segment (checkRow a17 a17Domains a17Hints 7) 190 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P20 : segment (checkRow a17 a17Domains a17Hints 7) 200 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P21 : segment (checkRow a17 a17Domains a17Hints 7) 210 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P22 : segment (checkRow a17 a17Domains a17Hints 7) 220 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P23 : segment (checkRow a17 a17Domains a17Hints 7) 230 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P24 : segment (checkRow a17 a17Domains a17Hints 7) 240 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P25 : segment (checkRow a17 a17Domains a17Hints 7) 250 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P26 : segment (checkRow a17 a17Domains a17Hints 7) 260 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P27 : segment (checkRow a17 a17Domains a17Hints 7) 270 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P28 : segment (checkRow a17 a17Domains a17Hints 7) 280 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P29 : segment (checkRow a17 a17Domains a17Hints 7) 290 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P30 : segment (checkRow a17 a17Domains a17Hints 7) 300 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P31 : segment (checkRow a17 a17Domains a17Hints 7) 310 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P32 : segment (checkRow a17 a17Domains a17Hints 7) 320 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P33 : segment (checkRow a17 a17Domains a17Hints 7) 330 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P34 : segment (checkRow a17 a17Domains a17Hints 7) 340 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P35 : segment (checkRow a17 a17Domains a17Hints 7) 350 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P36 : segment (checkRow a17 a17Domains a17Hints 7) 360 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P37 : segment (checkRow a17 a17Domains a17Hints 7) 370 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P38 : segment (checkRow a17 a17Domains a17Hints 7) 380 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P39 : segment (checkRow a17 a17Domains a17Hints 7) 390 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P40 : segment (checkRow a17 a17Domains a17Hints 7) 400 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P41 : segment (checkRow a17 a17Domains a17Hints 7) 410 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P42 : segment (checkRow a17 a17Domains a17Hints 7) 420 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P43 : segment (checkRow a17 a17Domains a17Hints 7) 430 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P44 : segment (checkRow a17 a17Domains a17Hints 7) 440 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P45 : segment (checkRow a17 a17Domains a17Hints 7) 450 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P46 : segment (checkRow a17 a17Domains a17Hints 7) 460 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P47 : segment (checkRow a17 a17Domains a17Hints 7) 470 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P48 : segment (checkRow a17 a17Domains a17Hints 7) 480 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P49 : segment (checkRow a17 a17Domains a17Hints 7) 490 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P50 : segment (checkRow a17 a17Domains a17Hints 7) 500 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P51 : segment (checkRow a17 a17Domains a17Hints 7) 510 10 = true := by decide +kernel
theorem a17S7 (j : Nat) (hj : j < 520) : (checkRow a17 a17Domains a17Hints 7) j = true := by
  by_cases bound : j < 260
  ·
    by_cases bound : j < 130
    ·
      by_cases bound : j < 60
      ·
        by_cases bound : j < 30
        ·
          by_cases bound : j < 10
          ·
            exact segmentRange a17S7P0 j (by omega) (by omega)
          ·
            by_cases bound : j < 20
            ·
              exact segmentRange a17S7P1 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P2 j (by omega) (by omega)
        ·
          by_cases bound : j < 40
          ·
            exact segmentRange a17S7P3 j (by omega) (by omega)
          ·
            by_cases bound : j < 50
            ·
              exact segmentRange a17S7P4 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P5 j (by omega) (by omega)
      ·
        by_cases bound : j < 90
        ·
          by_cases bound : j < 70
          ·
            exact segmentRange a17S7P6 j (by omega) (by omega)
          ·
            by_cases bound : j < 80
            ·
              exact segmentRange a17S7P7 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P8 j (by omega) (by omega)
        ·
          by_cases bound : j < 110
          ·
            by_cases bound : j < 100
            ·
              exact segmentRange a17S7P9 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P10 j (by omega) (by omega)
          ·
            by_cases bound : j < 120
            ·
              exact segmentRange a17S7P11 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P12 j (by omega) (by omega)
    ·
      by_cases bound : j < 190
      ·
        by_cases bound : j < 160
        ·
          by_cases bound : j < 140
          ·
            exact segmentRange a17S7P13 j (by omega) (by omega)
          ·
            by_cases bound : j < 150
            ·
              exact segmentRange a17S7P14 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P15 j (by omega) (by omega)
        ·
          by_cases bound : j < 170
          ·
            exact segmentRange a17S7P16 j (by omega) (by omega)
          ·
            by_cases bound : j < 180
            ·
              exact segmentRange a17S7P17 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P18 j (by omega) (by omega)
      ·
        by_cases bound : j < 220
        ·
          by_cases bound : j < 200
          ·
            exact segmentRange a17S7P19 j (by omega) (by omega)
          ·
            by_cases bound : j < 210
            ·
              exact segmentRange a17S7P20 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P21 j (by omega) (by omega)
        ·
          by_cases bound : j < 240
          ·
            by_cases bound : j < 230
            ·
              exact segmentRange a17S7P22 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P23 j (by omega) (by omega)
          ·
            by_cases bound : j < 250
            ·
              exact segmentRange a17S7P24 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P25 j (by omega) (by omega)
  ·
    by_cases bound : j < 390
    ·
      by_cases bound : j < 320
      ·
        by_cases bound : j < 290
        ·
          by_cases bound : j < 270
          ·
            exact segmentRange a17S7P26 j (by omega) (by omega)
          ·
            by_cases bound : j < 280
            ·
              exact segmentRange a17S7P27 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P28 j (by omega) (by omega)
        ·
          by_cases bound : j < 300
          ·
            exact segmentRange a17S7P29 j (by omega) (by omega)
          ·
            by_cases bound : j < 310
            ·
              exact segmentRange a17S7P30 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P31 j (by omega) (by omega)
      ·
        by_cases bound : j < 350
        ·
          by_cases bound : j < 330
          ·
            exact segmentRange a17S7P32 j (by omega) (by omega)
          ·
            by_cases bound : j < 340
            ·
              exact segmentRange a17S7P33 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P34 j (by omega) (by omega)
        ·
          by_cases bound : j < 370
          ·
            by_cases bound : j < 360
            ·
              exact segmentRange a17S7P35 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P36 j (by omega) (by omega)
          ·
            by_cases bound : j < 380
            ·
              exact segmentRange a17S7P37 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P38 j (by omega) (by omega)
    ·
      by_cases bound : j < 450
      ·
        by_cases bound : j < 420
        ·
          by_cases bound : j < 400
          ·
            exact segmentRange a17S7P39 j (by omega) (by omega)
          ·
            by_cases bound : j < 410
            ·
              exact segmentRange a17S7P40 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P41 j (by omega) (by omega)
        ·
          by_cases bound : j < 430
          ·
            exact segmentRange a17S7P42 j (by omega) (by omega)
          ·
            by_cases bound : j < 440
            ·
              exact segmentRange a17S7P43 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P44 j (by omega) (by omega)
      ·
        by_cases bound : j < 480
        ·
          by_cases bound : j < 460
          ·
            exact segmentRange a17S7P45 j (by omega) (by omega)
          ·
            by_cases bound : j < 470
            ·
              exact segmentRange a17S7P46 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P47 j (by omega) (by omega)
        ·
          by_cases bound : j < 500
          ·
            by_cases bound : j < 490
            ·
              exact segmentRange a17S7P48 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P49 j (by omega) (by omega)
          ·
            by_cases bound : j < 510
            ·
              exact segmentRange a17S7P50 j (by omega) (by omega)
            ·
              exact segmentRange a17S7P51 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S8P0 : segment (checkRow a17 a17Domains a17Hints 8) 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S8P1 : segment (checkRow a17 a17Domains a17Hints 8) 10 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S8P2 : segment (checkRow a17 a17Domains a17Hints 8) 20 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S8P3 : segment (checkRow a17 a17Domains a17Hints 8) 30 10 = true := by decide +kernel
theorem a17S8 (j : Nat) (hj : j < 40) : (checkRow a17 a17Domains a17Hints 8) j = true := by
  by_cases bound : j < 20
  ·
    by_cases bound : j < 10
    ·
      exact segmentRange a17S8P0 j (by omega) (by omega)
    ·
      exact segmentRange a17S8P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 30
    ·
      exact segmentRange a17S8P2 j (by omega) (by omega)
    ·
      exact segmentRange a17S8P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S9P0 : segment (checkRow a17 a17Domains a17Hints 9) 0 1 = true := by decide +kernel
theorem a17S9 (j : Nat) (hj : j < 1) : (checkRow a17 a17Domains a17Hints 9) j = true := by
  exact segmentRange a17S9P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Complete : Complete a17 a17Domains a17Hints := by
  intro k hk j hj
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a17S4 j hj
  · exact a17S5 j hj
  · exact a17S6 j hj
  · exact a17S7 j hj
  · exact a17S8 j hj
  · exact a17S9 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S9P0 : segment (checkRow a18 a18Domains a18Hints 9) 0 1 = true := by decide +kernel
theorem a18S9 (j : Nat) (hj : j < 1) : (checkRow a18 a18Domains a18Hints 9) j = true := by
  exact segmentRange a18S9P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Complete : Complete a18 a18Domains a18Hints := by
  intro k hk j hj
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a18S9 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0Bound : Lower true (roots a0) (target a0) 4 := by
  have ready : Ready a0 a0Domains (asRow a0Pos) (asRow a0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a0
  exact frozen ready a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Bound : Lower true (roots a1) (target a1) 4 := by
  have ready : Ready a1 a1Domains (asRow a1Pos) (asRow a1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a1
  exact frozen ready a1Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Bound : Lower true (roots a2) (target a2) 3 := by
  have ready : Ready a2 a2Domains (asRow a2Pos) (asRow a2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a2
  exact frozen ready a2Complete (by decide +kernel) (by decide) [(inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D0 : Slice true (roots a3) (target a3) (repeatWord 3689348814741910323) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 4] ++ fixRows 2 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D1 : Slice true (roots a3) (target a3) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 33, flipInput 5] ++ fixRows 4 0)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D2 : Slice true (roots a3) (target a3) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 67, flipInput 2] ++ fixRows 16 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D3 : Slice true (roots a3) (target a3) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, flipInput 1] ++ fixRows 0 32)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D4 : Slice true (roots a3) (target a3) (repeatWord 1085102592318504960) 3 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 4 32)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Bound : Lower true (roots a3) (target a3) 7 := by
  have ready : Ready a3 a3Domains (asRow a3Pos) (asRow a3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a3D0 (safeCons a3D1 (safeCons a3D2 (safeCons a3D3 (safeCons a3D4 (safeNil a3)))))
  exact frozen ready a3Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Bound : Lower true (roots a4) (target a4) 3 := by
  have ready : Ready a4 a4Domains (asRow a4Pos) (asRow a4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a4
  exact frozen ready a4Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17), (inputs.getD 1 zero, 0, 2), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D0 : Slice true (roots a5) (target a5) (repeatWord 12297829382473034410) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 1)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D1 : Slice true (roots a5) (target a5) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D2 : Slice true (roots a5) (target a5) (repeatWord 4294967295) 4 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 83, flipInput 0, flipInput 2] ++ fixRows 32 0)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D3 : Slice true (roots a5) (target a5) (repeatWord 17361641481138401520) 3 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 83] ++ fixRows 0 4)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D4 : Slice true (roots a5) (target a5) (repeatWord 2863311530) 3 :=
  signedSlice (ms := ([swapRows 66, swapRows 67, swapRows 84] ++ fixRows 32 1)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Bound : Lower true (roots a5) (target a5) 7 := by
  have ready : Ready a5 a5Domains (asRow a5Pos) (asRow a5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a5D0 (safeCons a5D1 (safeCons a5D2 (safeCons a5D3 (safeCons a5D4 (safeNil a5)))))
  exact frozen ready a5Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D0 : Slice true (roots a6) (target a6) (repeatWord 14757395258967641292) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 2)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D1 : Slice true (roots a6) (target a6) (repeatWord 7378697629483820646) 4 :=
  signedSlice (ms := ([swapRows 33, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D2 : Slice true (roots a6) (target a6) (repeatWord 3689517697150995660) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D3 : Slice true (roots a6) (target a6) (repeatWord 12297829382473034410) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 83, flipInput 4] ++ fixRows 0 1)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D4 : Slice true (roots a6) (target a6) (repeatWord 18446744069414584320) 3 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Bound : Lower true (roots a6) (target a6) 6 := by
  have ready : Ready a6 a6Domains (asRow a6Pos) (asRow a6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a6D0 (safeCons a6D1 (safeCons a6D2 (safeCons a6D3 (safeCons a6D4 (safeNil a6)))))
  exact frozen ready a6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D0 : Slice true (roots a7) (target a7) (repeatWord 4340410370284600380) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D1 : Slice true (roots a7) (target a7) (repeatWord 14757226376558555955) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 4 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D2 : Slice true (roots a7) (target a7) (repeatWord 3689348817318890700) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D3 : Slice true (roots a7) (target a7) (repeatWord 1085350949055099120) 4 :=
  signedSlice (ms := ([swapRows 16] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D4 : Slice true (roots a7) (target a7) (repeatWord 17361641477348724495) 4 :=
  signedSlice (ms := ([swapRows 16] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D5 : Slice true (roots a7) (target a7) (repeatWord 281474976645120) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 67, flipInput 2] ++ fixRows 0 0 ++ identifyRows 4 5 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Bound : Lower true (roots a7) (target a7) 6 := by
  have ready : Ready a7 a7Domains (asRow a7Pos) (asRow a7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a7D0 (safeCons a7D1 (safeCons a7D2 (safeCons a7D3 (safeCons a7D4 (safeCons a7D5 (safeNil a7))))))
  exact frozen ready a7Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 18, 22), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D0 : Slice true (roots a8) (target a8) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 67, flipInput 2] ++ fixRows 16 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Bound : Lower true (roots a8) (target a8) 6 := by
  have ready : Ready a8 a8Domains (asRow a8Pos) (asRow a8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a8D0 (safeNil a8)
  exact frozen ready a8Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Bound : Lower true (roots a9) (target a9) 6 := by
  have ready : Ready a9 a9Domains (asRow a9Pos) (asRow a9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a9
  exact frozen ready a9Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D0 : Slice true (roots a10) (target a10) (repeatWord 6510615555426900570) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a9) (G := (neg (target a9))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a9Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Bound : Lower true (roots a10) (target a10) 6 := by
  have ready : Ready a10 a10Domains (asRow a10Pos) (asRow a10Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a10D0 (safeNil a10)
  exact frozen ready a10Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D0 : Slice true (roots a11) (target a11) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Bound : Lower true (roots a11) (target a11) 5 := by
  have ready : Ready a11 a11Domains (asRow a11Pos) (asRow a11Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a11D0 (safeNil a11)
  exact frozen ready a11Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D0 : Slice true (roots a12) (target a12) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Bound : Lower true (roots a12) (target a12) 5 := by
  have ready : Ready a12 a12Domains (asRow a12Pos) (asRow a12Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a12D0 (safeNil a12)
  exact frozen ready a12Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D0 : Slice true (roots a13) (target a13) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 67, swapRows 84, flipInput 1] ++ fixRows 0 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Bound : Lower true (roots a13) (target a13) 5 := by
  have ready : Ready a13 a13Domains (asRow a13Pos) (asRow a13Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a13D0 (safeNil a13)
  exact frozen ready a13Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 18, 22), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D0 : Slice true (roots a14) (target a14) (repeatWord 12297829382473034410) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, flipInput 4] ++ fixRows 0 1)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Bound : Lower true (roots a14) (target a14) 5 := by
  have ready : Ready a14 a14Domains (asRow a14Pos) (asRow a14Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a14D0 (safeNil a14)
  exact frozen ready a14Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Bound : Lower true (roots a15) (target a15) 4 := by
  have ready : Ready a15 a15Domains (asRow a15Pos) (asRow a15Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a15
  exact frozen ready a15Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17), (inputs.getD 1 zero, 0, 2), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Bound : Lower true (roots a16) (target a16) 4 := by
  have ready : Ready a16 a16Domains (asRow a16Pos) (asRow a16Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a16
  exact frozen ready a16Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D0 : Slice true (roots a17) (target a17) (repeatWord 7378697629483820646) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D1 : Slice true (roots a17) (target a17) (repeatWord 6148914692668172970) 7 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, flipInput 1, flipInput 2, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D2 : Slice true (roots a17) (target a17) (repeatWord 4340410370284600380) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D3 : Slice true (roots a17) (target a17) (repeatWord 12297829382473034410) 6 :=
  signedSlice (ms := ([swapRows 32, flipInput 1, flipInput 2, flipInput 5] ++ fixRows 0 1)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D4 : Slice true (roots a17) (target a17) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 4] ++ fixRows 2 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D5 : Slice true (roots a17) (target a17) (repeatWord 1085102592571150095) 6 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D6 : Slice true (roots a17) (target a17) (repeatWord 18446744069414584320) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, swapRows 83, flipInput 0, flipInput 1, flipInput 2, flipInput 4] ++ fixRows 0 32)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D7 : Slice true (roots a17) (target a17) (repeatWord 11068046444225730969) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 false)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D8 : Slice true (roots a17) (target a17) (repeatWord 11936128518282651045) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 2 false)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D9 : Slice true (roots a17) (target a17) (repeatWord 6510615555426900570) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 66, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D10 : Slice true (roots a17) (target a17) (repeatWord 14757395256390660915) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 5 false)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D11 : Slice true (roots a17) (target a17) (repeatWord 3689348817318890700) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D12 : Slice true (roots a17) (target a17) (repeatWord 17361641477348724495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 65, swapRows 84, flipInput 1, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D13 : Slice true (roots a17) (target a17) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, flipInput 1, flipInput 5] ++ fixRows 1 0)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D14 : Slice true (roots a17) (target a17) (repeatWord 14757395258967641292) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 2)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D15 : Slice true (roots a17) (target a17) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 83, swapRows 84, flipInput 0, flipInput 1, flipInput 2] ++ fixRows 16 0)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D16 : Slice true (roots a17) (target a17) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a14) (G := (target a14)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a14Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D17 : Slice true (roots a17) (target a17) (repeatWord 12297735558912431445) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 84, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D18 : Slice true (roots a17) (target a17) (repeatWord 6149008514797120170) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D19 : Slice true (roots a17) (target a17) (repeatWord 14757226376558555955) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 84, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 4 false)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D20 : Slice true (roots a17) (target a17) (repeatWord 3689517697150995660) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D21 : Slice true (roots a17) (target a17) (repeatWord 17361393124654452495) 5 :=
  signedSlice (ms := ([swapRows 32, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D22 : Slice true (roots a17) (target a17) (repeatWord 281474976645120) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 33, swapRows 83, swapRows 84, flipInput 0, flipInput 1, flipInput 2] ++ fixRows 0 0 ++ identifyRows 4 5 true)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D23 : Slice true (roots a17) (target a17) (repeatWord 17361641481138401520) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 4)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D24 : Slice true (roots a17) (target a17) (repeatWord 18446462603027742720) 4 :=
  signedSlice (ms := ([swapRows 33] ++ fixRows 0 16)) (base := roots a16) (G := (target a16)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a16Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D25 : Slice true (roots a17) (target a17) (repeatWord 2459565876494606882) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 4] ++ fixRows 2 1)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D26 : Slice true (roots a17) (target a17) (repeatWord 93823560602965) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 67, flipInput 2] ++ fixRows 17 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D27 : Slice true (roots a17) (target a17) (repeatWord 6148914689804861440) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 67, swapRows 84, flipInput 1] ++ fixRows 1 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D28 : Slice true (roots a17) (target a17) (repeatWord 868082074056920076) 4 :=
  signedSlice (ms := ([] ++ fixRows 4 2)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D29 : Slice true (roots a17) (target a17) (repeatWord 18446462598732906495) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a16) (G := (target a16)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a16Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D30 : Slice true (roots a17) (target a17) (repeatWord 723401728380766730) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 83, flipInput 4] ++ fixRows 4 1)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D31 : Slice true (roots a17) (target a17) (repeatWord 2863311530) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, flipInput 4] ++ fixRows 32 1)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D32 : Slice true (roots a17) (target a17) (repeatWord 3472328296227680304) 3 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 83] ++ fixRows 2 4)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D33 : Slice true (roots a17) (target a17) (repeatWord 3689348813882916864) 3 :=
  signedSlice (ms := ([swapRows 33] ++ fixRows 2 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D34 : Slice true (roots a17) (target a17) (repeatWord 1085102592318504960) 3 :=
  signedSlice (ms := ([] ++ fixRows 4 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Bound : Lower true (roots a17) (target a17) 10 := by
  have ready : Ready a17 a17Domains (asRow a17Pos) (asRow a17Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a17D0 (safeCons a17D1 (safeCons a17D2 (safeCons a17D3 (safeCons a17D4 (safeCons a17D5 (safeCons a17D6 (safeCons a17D7 (safeCons a17D8 (safeCons a17D9 (safeCons a17D10 (safeCons a17D11 (safeCons a17D12 (safeCons a17D13 (safeCons a17D14 (safeCons a17D15 (safeCons a17D16 (safeCons a17D17 (safeCons a17D18 (safeCons a17D19 (safeCons a17D20 (safeCons a17D21 (safeCons a17D22 (safeCons a17D23 (safeCons a17D24 (safeCons a17D25 (safeCons a17D26 (safeCons a17D27 (safeCons a17D28 (safeCons a17D29 (safeCons a17D30 (safeCons a17D31 (safeCons a17D32 (safeCons a17D33 (safeCons a17D34 (safeNil a17)))))))))))))))))))))))))))))))))))
  exact frozen ready a17Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D0 : Slice true (roots a18) (target a18) (repeatWord 72056494543077120) 10 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 3 4 true)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Bound : Lower true (roots a18) (target a18) 10 := by
  have ready : Ready a18 a18Domains (asRow a18Pos) (asRow a18Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a18D0 (safeNil a18)
  exact frozen ready a18Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 5, 21), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots := roots a18
def fullWord := target a18
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813000 * 2 ^ 32 + 4276144320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_43906.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩, ⟨.and,[3,6]⟩, ⟨.or,[3,5]⟩, ⟨.and,[0,8]⟩, ⟨.or,[7,9]⟩, ⟨.or,[2,10]⟩, ⟨.and,[2,7]⟩, ⟨.and,[0,4]⟩, ⟨.or,[12,13]⟩, ⟨.or,[1,14]⟩, ⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276144320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276144320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_43906
open PEqualNP.Outside.L_meta_43906 in
theorem PEqualNP.Outside.L_meta_43906 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276144320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276144320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := solve a18Bound

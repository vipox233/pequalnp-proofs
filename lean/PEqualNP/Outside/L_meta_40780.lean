import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40780.Model
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

end PEqualNP.Outside.L_meta_40780.Model

namespace PEqualNP.Outside.L_meta_40780
open PEqualNP.Outside.L_meta_40780.Model
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

def page0 : List Nat := [0xf20fa65f0cbe18f, 0xe30fa43fc43e10f, 0xd31fe61f883f087, 0x26f00000000088f, 0x340048, 0x14eb6db23688b18, 0x10f63446163447a, 0x24b184215135882, 0xf230842b492302c, 0x10f130843c88210, 0xb0009d34883c482, 0xe997d2000500040, 0xb087e20fa61f8c3, 0x1d90c839008240b, 0x3d3d3e4ce3cd292, 0x5e17110d20443d, 0x4443b92e02186a9, 0x8798a415a5c0625, 0x7258453502e4b80, 0x8deeab08879054f, 0xa81c59c445cc530, 0x7314c38b388a7a0, 0xb9b442987157111, 0xb1d56110d20c388]
def page1 : List Nat := [0xf8ab88a7a0a811, 0x82905977150d511, 0x4348110b52e021e, 0x29e8d10a815a9d4, 0xce571118354830e, 0x443a3eeaa188710, 0xa21a43a350f6254, 0x10c454830ea1cc, 0x5ee4b088a985a97, 0x8165dc54394443a, 0xb20000000000010, 0x804da000000036e, 0x22000f806, 0x8000000200002e0, 0x800000000015811, 0x5872, 0x78038a0, 0xd3012040e000000, 0x249244814012040, 0x8850b6d9249236d, 0xac222a617ab0886, 0xa8818e22e629867, 0x7cb0086886bc439, 0xe8298dbe6da0a61]
def page2 : List Nat := [0xe7c8b10a61ce21, 0xc1a2c433fb2a871, 0x8619f10e8a184fa, 0xe2b242a067a42a2, 0x62a05f2c018a813, 0xcf8ac90a613fab0, 0x19ae85ce21a8298, 0x416f9b082984fac, 0x90a2a184fcca21a, 0x3906bea690a81ba, 0x988798a41779b68, 0xa0a81bb1322a187, 0x19e22c4298678a7, 0x2887885d88c1aa4, 0xa05de6c20e413eb, 0xea710a813eb08a6, 0xc813eab442186b, 0xae90e6a204feca9, 0x48710cfaad10881, 0x84fead21a433eab, 0x6da0a639f10a8a1, 0xe213fab442a05be, 0xfa3062a05eac221, 0xa6a067a83a2e635]
def page3 : List Nat := [0xddac221e41af308, 0xc8a8813eb008a90, 0x87ba9322a206ec4, 0xa1aa221d3ec2a18, 0xa90cfcca21a21ce, 0xba861aa433eb006, 0x21e635eab487a0e, 0x1cea188710dbac0, 0x12a221eb8a710a8, 0x907588622a41b7b, 0xacb10c81779b682, 0xa883d621e82904f, 0x77a3663904fa0d9, 0xa8298dbaada1e63, 0xe7a43a28613e32, 0x8d10a817ab08871, 0x8613fb2a421857e, 0xe32a8690eec428a, 0xa6a05d88d98e413, 0x6bc429a881aeb10, 0x798e413fab664a0, 0x413eb068b98f988, 0x90a6a205f2c021a, 0x2a04fcca21a43ae]
def page4 : List Nat := [0xbe6d10a619fab68, 0x8a881ae22e62985, 0x13eb088a986ec42, 0x36629057e8d98a8, 0x885dac221a41762, 0x2c021a41f421a40, 0xa613fab082985d, 0x9e22a8298cfeada, 0x243185de8d98a41, 0x4fac1a2e656e1b, 0xca21a41f4b00869, 0xc613fab68690ddc, 0xfa1e6b10cfacb10, 0x62985de8c1aa41a, 0x4faada1c43afab6, 0xd98a813fab44298, 0x613fb2a42204fea, 0xb12a221df2c020a, 0x690f3a86a908777, 0xbac229a81cea188, 0x21a433eb066b10e, 0x1ae29a42a05eac2, 0xb6849867cc222a6, 0x9057e8d992816f9]
def page5 : List Nat := [0xeca90c61d621e83, 0x88879f21e8b10cf, 0xb6312a221f3a872, 0x88a90eea428a881, 0x85b8c6a0a639ea1, 0x6c22a419f22a429, 0xe839e22a42985de, 0xe232432057ac021, 0x6ba0f98861aa415, 0xcfeada12613eb06, 0x422a613eb288710, 0x83afab08698e7ac, 0x21a8398e7eac21a, 0xa18dde8c18e41ce, 0xea4c8a8613e8368, 0xa0a81ce21e8398e, 0x1098001803638a7, 0x1e299d400000, 0xf75f8300c0c0900, 0x44c380878819ea, 0x97a220806602040, 0x1a0000004160103, 0x102176000006c04, 0x145051b84304b0]
def page6 : List Nat := [0x824200e618d, 0x1100002000005a, 0x400000007870281, 0x200000000032d, 0x180000000800000, 0x40000000, 0x180000000a, 0x80000000380, 0x2800000012000, 0xc0000000580000, 0x80000001a000000, 0x4408300000003, 0x120202000881070, 0x808300024041000, 0x20e000901070004, 0x80028041800130, 0x1201010008c08, 0x64041800243206, 0xa1903000c808380, 0x80045130400001, 0x4c0481038a628, 0x151030400a1821a, 0x540c1002a208080, 0x3414018a820200c]
def page7 : List Nat := [0x10068a66280335, 0x401aa098200d4c5, 0x1a1a181610100c0, 0x222201e1e1a1a1a, 0x3030302c2a28262, 0x640403c36343232, 0x4c4c4c4a4a48464, 0x85652504e4e4e4c, 0x746e6e66625e5e5, 0x68682807e7c7876, 0x92928e8c8c8a888, 0x696969696969494, 0xa4a4a4a09c9a989, 0xeb6b2aeaca6a6a4, 0xcecccacacac8c6b, 0x8d8d8d8d8d6d6d2, 0xe2e0dededcdad8d, 0x6f4f2f0ececeaea, 0x50502fefcf8f8f, 0x3110f0b09050505, 0x1f1d1d191715151, 0xeaa60c4912b2723, 0x22c58c61c21a51a, 0xb28790118c8c238]
def page8 : List Nat := [0x8a01028090600c, 0x3020143cc5cb101, 0xc05943146a0c16, 0x28038ca8c39660e, 0x3c600a00cca6026, 0x2804aaa98680e37, 0x6a489c6868a2196, 0x3e6b82b2ca201c, 0xb16397009238006, 0x50c03459850c03c, 0xca828ab0e5a048a, 0x21ebb830830c2d0, 0x5102f86a881470c, 0x14d42be22e637d1, 0x7f35d06dea498df, 0x8574d641afa9a81, 0xc83ef20c42da4a1, 0x8a98ef10d41bf9a, 0xea8063fe21902f8, 0x6fea2a1fbc8110b, 0x41ff99681fd4388, 0x3cc7fc42207f4d7, 0x10530bfa2e63dc4, 0x7f350c7faa221ff]
def page9 : List Nat := [0x87f48440be22a43, 0xc617d05ccbfa421, 0x8b18d7cd410fe90, 0xf10e61fe434867e, 0x2da4b105f45630f, 0x30be22a61fd2190, 0x843fe63a04f514, 0x10d31bfa2c43e92, 0xfd43486fa0b10f7, 0x5fcd742f620e41, 0xe217f3590ef8a6a, 0x8298dbd4941bf9a, 0xe90e61bc43d07fe, 0x3f862a057cd440f, 0x20be22a21fe2150, 0x5102f86a90fbd05, 0x11730efa1e636d2, 0xdf31cc2ea2a185f, 0x87f10f109ea2821, 0xa617d1590e7e8a1, 0x86887f10d20fe90, 0xfa2c63ec31c83f8, 0x2f88a905d45440b, 0x43ff98a817f45c4]
def page10 : List Nat := [0x1442fa2ba1df540, 0x88430ff99281ff4, 0xff41cc6fe6a20ff, 0x87f0c740b692c61, 0x2215d35043f8839, 0xa221df45640f690, 0xe21c43df314c2fa, 0x33a8621ef90f41f, 0x40ff21c43ec4548, 0x1d02fea090d74d4, 0xd1431ffa2e63fd2, 0x7715103fa8298df, 0x6fd05409f22a61, 0xc217d50106fea2a, 0xba0df41731b692, 0xe8a8616d25902fa, 0xbde63907b10d20b, 0x30be1aa417f45cc, 0x5907fe8710ffd09, 0x485409e22a615f3, 0xfd45cc7fe6ba0ff, 0x85f14d41f490221, 0x8875c53503fc429, 0xba0fb10f20ff28]
def page11 : List Nat := [0xf9ac433d458c7fa, 0x7fe62884fd1410b, 0x20ffa0e61fd41cc, 0x5cc7faa421fb0d5, 0xd1441ff10c61fd0, 0xff42cc2ee2a185f, 0xdb49410ffa0a61, 0x87ef31483fe869, 0x83907f88740fea8, 0xe82e857f514c3de, 0x3f88690df11532b, 0x91a01147bf41d0, 0x20280c005d00001, 0x4091b10030041c0, 0x82700866140018, 0x103008000003400, 0x19398c8018a000, 0xb50200000066a80, 0x107060000003034, 0x4000780800080, 0x7f00004080001, 0x8091d1b04014, 0xc00041544c18000, 0x2000000000522]
def page12 : List Nat := [0x200000000c00000, 0x50000000, 0x1c0000000c, 0x90000000400, 0x2c00000014000, 0xd0000000600000, 0xc0000001c000000, 0xc48000000003, 0x43200000209000, 0x408380022040000, 0x208000901010004, 0x380024041800120, 0x981070004808, 0x26241400131200, 0xa09000005008300, 0x64000014120a000, 0x8c08080028, 0x240202001189, 0x90c8000048240, 0x31020c001881000, 0x808080062041c00, 0x20c00190104000c, 0x380064041c00320, 0x198900000cc08]
def page13 : List Nat := [0x6804180033120a, 0xa0905000d048000, 0x80000343200001, 0x14c5010008a26, 0x1150404008a8182, 0x54d0d0022a48680, 0x434009a8202004, 0xc10028a06080143, 0x4019a8202009144, 0x68a06080335341, 0xa8898200d14cc50, 0x628080351140401, 0xc0a0240600c006a, 0xa1584e118400e82, 0xc2107a1c86c1905, 0xc2b8a4270962488, 0xa3c0e6368d0310b, 0x4611243908408f, 0x4531424d9304a12, 0xc6117e5c1665615, 0xa701bc6c1a46618, 0xc7c1ea789da751c, 0x68c22085a0e809f, 0x297a54932428f23]
def page14 : List Nat := [0x8a3a86a0a7a9ba6, 0x4b3ac4ae2aaa929, 0xcbe2f4bbae6b72d, 0x6ca320c4308c0af, 0xcd7b54d3b48d033, 0xae538ce0b78dcb6, 0x2f1bbaed3ace8b9, 0x8ffbf2fabe0f63d, 0xb094210641503c0, 0x713c47104390c42, 0xb2047b1b46717c5, 0x52bca728c9d2548, 0xd35cd132cc72fcb, 0xb40cf93c4e938cd, 0xa194751743d0, 0x4c5846a2060b0c1, 0x83868b080808014, 0x161013d0c0c50e1, 0xa0834303190830c, 0x8d1c346a418a0b0, 0x204442c60b0a741, 0x490c161870c0400, 0x20400186144e3, 0x40018a0c2c68b0a]
def page15 : List Nat := [0x62d6830c305040, 0x6042c28a0809f85, 0xa1844586061450, 0x80a0a0858e16196, 0xc00a08181801610, 0x284161870c0a0, 0x81420a1c3068318, 0x18100051a0060a0, 0x16340060850684, 0x3a36283020a1018, 0x1af163860d182c5, 0x831a06305050808, 0x1458a0c14184242, 0x628729203540608, 0x80c00a188cf021, 0xa182c3032228606, 0x60a3868b0c1000, 0x230061468b5e384, 0x850678ac58c1828, 0x1000b1a003040a0, 0xc0850e2c3470a0a, 0xc30b8b083078b0, 0x4060400a18b4503, 0x2b1431a0c1a3458]
def page16 : List Nat := [0x68b1a286030c0c6, 0x2846c286be5c28, 0x3058614446040a1, 0x43c628160c08d14, 0x1c35a93163070c5, 0xa0a1000b1a2828b, 0x3020068c182830, 0x9c1011b8b18282, 0x18514187080c09, 0x14f021628704040, 0x43458508344060e, 0x183470c0a0c68c1, 0x202111051410006, 0xa06b4198181858, 0x5830a345860a100, 0xb0d1c25c8a18c0, 0x91c1816141000c1, 0xa2c20b141828108, 0x3c0850b1c1828a1, 0x6160c61c321828e, 0x8d600cd8d761862, 0x60a0a3868a0a120, 0x4586080400c1a10, 0x1820c1414201003]
def page17 : List Nat := [0x25420d1811a0c1a, 0x42858e54a160c2, 0xb0a2c30a1c3189e, 0xb18386800a1030, 0x28a0c1458608259, 0x100a1a346141c2c, 0x284b31434005081, 0x42d40d22305860a, 0x6b050606313060, 0x23e3418c1618202, 0x2c1c183851c1c28, 0x2112e3070b1a305, 0xc68200112850428, 0x2928a06345055e2, 0x82c203183458518, 0x86050c2e307060, 0x18a542f1a0068b, 0xc141470d161824, 0x82e163450300107, 0x77907f20fe207e9, 0x6907f21ffa1ff08, 0x187e90fea1ff10f, 0x97ea0ffa07ea07f, 0xff18ff98ff987f9]
def page18 : List Nat := [0xf887e21fe887e18, 0x87e907fa0fe20f, 0x7e98fea17f207e, 0x7fa17e187e997f1, 0x8140178420e42cc, 0x19800683018, 0x400001800004, 0x38000180000a0, 0x34000180000b00, 0xf00007000, 0x10c80080400302, 0x262401302008810, 0x43200a090050080, 0x190090080460401, 0x80662403302012, 0x40343201a0900d0, 0x9888705844382c1, 0x5311d04f0d8c4b0, 0xd1c1a59181755d4, 0x25642361e09f9e1, 0x490705269a866e6, 0x4a9202ad44181aa, 0x2a883e20c90814b, 0x100640296920ee7]
def page19 : List Nat := [0x3144059074324c5, 0x510724a883054aa, 0x4aca09ad4418749, 0xca5641870a498e0, 0x484c74accb484c7, 0x4ac83438ea4bd4b, 0x951b52ca852c2a, 0xb1924028695012b, 0x598115a4ab51060, 0x59060625465a549, 0x8d11f8649f2a00a, 0xcc35688fc688b85, 0x6bc07d63447da22, 0x1a221aa621891ac, 0x5ba0a616a28184f, 0x1856926635e8498, 0x48085a20a615a48, 0x3868884f9a0215a, 0x615a4918d712221, 0x32013a68085b8a0, 0x4ca78800020001, 0xfc21fc43f98ff30, 0xfa61f8c3f18fc31, 0xfa21f0c3e98fc10]
def page20 : List Nat := [0xc01002b300000, 0x3d3c0d646912480, 0x20ca527d8d41105, 0x5044192a6e30282, 0x364974192949c60, 0x630ab49b41d034d, 0xb498504c66f6251, 0x41c426f624d6409, 0x74d3649410b949a, 0x151630d3cd92590, 0x108f518504c6776, 0x4d8505076441494, 0x25032e414944097, 0x674149410d38db5, 0x895109b899158c3, 0xadd8d411074e36, 0x5501063e464563, 0x9074f3649440cd5, 0xe3645640d34d925, 0x97419bd89458425, 0x9b49a454c74f364, 0x5251026d26d4d41, 0x34f3649410cb10, 0x41117108f55a411]
def page21 : List Nat := [0x543ad1814110735, 0xd4585050e6d26d4, 0x358427756905109, 0x34c36895109bd89, 0x614143cd50c5150, 0x31b949a414426d2, 0xdb525033545105, 0x5063f56d0540d3, 0x5f63516109b4985, 0x91610ab49b41502, 0x9d55b410433441, 0x991590334454c51, 0xf3f4d36494409b8, 0x10276280023, 0x94c000001a00380, 0x951c70000b202a8, 0x0, 0x492492249249249, 0xc1741c92491b6db, 0x7e454c6faa020df, 0xdfd4543b692e83, 0xa636d25042fa0b2, 0x2a207d4c510bea2, 0xea2c616e25442fa]
def page22 : List Nat := [0x3f621085f51610b, 0x43dea1c83fb4090, 0x35037a8620df141, 0x41741faa0883bd4, 0x3c45443e883085f, 0x5f91630bba8a81, 0xc213f45042fea2a, 0x83a07dd0531bf1a, 0xea28217c454437a, 0x2fa8a085fd4d419, 0x40dfa0e81bf4090, 0x5d02fa2b186fd05, 0x45740be282837f1, 0xbc41103ea63885f, 0x85f91510fb20a21, 0xa217f15103ee210, 0x2a205d45440faa0, 0xa28a816d25906ee, 0x6fe8b085f4d610b, 0x10be282637f0590, 0x5902fa2b205f117, 0x4d640df208817f1, 0xbe41903ee82085f, 0x6d50441b7a9281]
def page23 : List Nat := [0x821f741842f8a2a, 0x8298dfd1410fa20, 0xfa82837d45c43e8, 0x37883205f91610b, 0x41fb20e217f45c4, 0x3d027c8a886f504, 0x50710b692881bd4, 0x7e501077a82a07d, 0x4a85e0036000005, 0x28e608041800fa1, 0x408a80004004e09, 0x48ae322aa10a82, 0xc042a0000727a0c, 0x3c63461, 0x100000000400, 0xa000000040000, 0x380000001800000, 0x80000000, 0x2800000012, 0x209020000c48180, 0x40c00110204000, 0x20004c48000026, 0x400143200000a09, 0x8c48180042040]
def page24 : List Nat := [0x310202001201010, 0xc08180062040800, 0x204001a0101000c, 0x8228280000341, 0x228882021144410, 0x228080051130406, 0x18a03454101000a, 0x80141041404988, 0x9144410028a02, 0x3450104018a8202, 0x90e0406a228080, 0xa11224070e1a305, 0xd1213e78d99305c, 0xad4a950a1427468, 0x2d9a3262c17ac56, 0x8f1a344850a13e7, 0x3a54a8cd992e447, 0xdfbd72dd9b35ab5, 0x366cd972e3c586f, 0x386fdfbb6ebcd9b, 0x30a206080271e3c, 0x41c088200790004, 0x804308b88016080, 0x23421080302a026]
def page25 : List Nat := [0x9021070524ad90, 0x50201a42c20c401, 0x40c202022388180, 0x446f10310218414, 0x2c022200e1033a, 0x432230400910a08, 0x99220603e590210, 0x81fa2040d110a88, 0x1f883fc61fa63f8, 0xfa87fc83fe83fe2, 0x821fa83fa81fe81, 0x190085fc81fc21f, 0x800008000035690, 0xa0000400001, 0x81000000480001c, 0x480080400312060, 0x409102002090210, 0x6989004c081a20, 0x250480280401312, 0xc2040143200a090, 0x302010810284080, 0x1008c481c6040e, 0x80482402402032, 0x4033020788102c4]
def page26 : List Nat := [0x1a0902d0480680, 0xd6cbd4223650687, 0x60972c549d2a1b, 0x2d8401229aabc08, 0xc0682c10201e1c, 0x620608c532b8408, 0x310cf8a18023c41, 0x45040ba34691410, 0xb0a6e04080a06d2, 0x2d840222c020600, 0xc08038820290c74, 0xe200d8a280a88ab, 0x85050da30511a23, 0x866d26141319b49, 0x61516308f518504, 0x6209bd893584277, 0x74d850486776151, 0x359027516141439, 0x25e36496409bd89, 0x6141318f919158c, 0x209d4585050a3d4, 0x8d9258423e46456, 0x5e825d361414297, 0xd00002101600093]
def page27 : List Nat := [0xbf12c217e454806, 0x42fea2905fd4940, 0x940be92c817e358, 0x42482fea6a06f50, 0xdd4540ee98a61ed, 0x17f5050efc4a885, 0x905f51620be92c2, 0xaa21f531443da42, 0xa8b185f14143bf1, 0xb7a92617d35842f, 0xaf8a098df14121, 0x620af1aa417c505, 0x458c2fea098df91, 0xf4d640be8ac417e, 0x17f514c3ea42885, 0x985fd4121bf22a6, 0x2a21bd43503ba86, 0xa2b185fd41429f2, 0x309000090066fef, 0x4000008f24, 0x1f00ecd80421, 0xe08000000000000, 0xea50e000001, 0xc00008000040]
def page28 : List Nat := [0x24064240e424080, 0x440a844026240e6, 0x286406864028, 0xc71c50c30400000, 0xd349134d2c92071, 0xe181f7df7df6d74, 0x12a279e79638e38, 0x321072400260938, 0x332103210321010, 0xd10fe303a2b3511, 0x30fd43fe10fd42f, 0xfe40fd21fd31fd, 0x1a7fd20fe20fd4, 0x321098009054c00, 0x48f2c8100987654, 0x18c26ca2481c656, 0xa5a610861660852, 0x5e1c861261260c1, 0x544c7cc1654c248, 0x346a90cea2c2828, 0x184de4da2e611ea, 0xa8da8a6537b128b, 0x80652f9b64ba047, 0x1e232a0194e8c2a]
def page29 : List Nat := [0x68b984de4da2e21, 0x47e8d8ae413b8b, 0x8c92c213bb0a8b1, 0xc2136132a020c7c, 0xfa364b884dec49a, 0x2ba04da4c282631, 0x4d8c4a80872f9b6, 0x292c812f9b4a221, 0x832fb1a8b084eec, 0x9348a98cda4da9a, 0xb104ee2da286536, 0xdc4c8ac812f1b22, 0x9ac81379366b884, 0x537b128b084eec2, 0x362ba04ea2c2826, 0x984ee2d9ae41379, 0x86ca80851fa362b, 0x8063371322b184b, 0x3a8b6a4a1c788ca, 0x22b204ee2d29087, 0x4b86ca80832f1b, 0xc292c612f9b62b9, 0xc6136930a0a0cee, 0xa8b6a6a147c8c8a]
def page30 : List Nat := [0x6b904ee2d9ae813, 0x4ba6da92831fa36, 0xd9ae813bb0a8b18, 0x412f9b68b904de4, 0x9b0a0a14bec6a2c, 0x10cd84ca80632e, 0xbc6c92c811e232a, 0xa9263379362b984, 0x33b8b66a2147a8d, 0xb0a090cbe6da284, 0x184ba6d22a432e9, 0xe8d9ae211f2324b, 0x2e812f9b64a20c7, 0x37934a221cee2d9, 0xaa021cda4c28287, 0xc7a8c282653a30, 0x6da2e21379366a2, 0x2873b8b68b904be, 0x79368a18cea2c28, 0x6b204ee2d92e613, 0x47e8d9286337b12, 0xd92e611f2326b10, 0x832f1b24b0847e8, 0x8b48a994ba6c282]
def page31 : List Nat := [0xb0847c8c8ac413a, 0xbe6d92e211f2326, 0x282632e9b6a2a14, 0x336936a2a1c7a8c, 0xaa02147e8d9a84, 0x10c7e8d288653a3, 0xa8c282432e1b2a0, 0xe253bb0a6b1047, 0x1020000, 0x5200ce00004a0, 0x200080001620972, 0x1c01260000007, 0xa1c014afe0022ca, 0x4218017a0000012, 0x8b0a043608eebb, 0x13200001c008e0, 0x4006a92000152, 0xae00f6017600820, 0x5b06b26e0c9aa6, 0x55b233a3a000, 0x511040a0000005e, 0x4410204a2208182, 0x4101a8882060d4, 0x288a2208103512]
def page32 : List Nat := [0xe22890207114441, 0xa22408205112040, 0x982091444c1048, 0x408211502040e29, 0x2084540c104a2a0, 0x251524240e8a919, 0x49404102a2a6648, 0x503041292808206, 0x90502a4a4628192, 0x40892998a09494, 0x426a0208193501, 0x89a910a064d4081, 0x6a6428213524140, 0x808205514041022, 0x428154502040ea2, 0xa075148c50228a4, 0x2315232412a2990, 0xc54d0903e2a6648, 0x533140d92918a09, 0x8850464a6828172, 0x14099a990a06cd4, 0x2e8a44281f3534, 0x1a2998a04d14c85, 0xa28a20618410408]
def page33 : List Nat := [0x240e38c30c28a28, 0x861861861651249, 0x28a079c71a69a69, 0xaaa8a289a692492, 0x4cb0c30bacaaaaa, 0x303ef3cebaeb8db, 0xd34b2cb2471c714, 0x75534514513cd34, 0x11c46e185f75b65, 0x864cb2b51690239, 0xa034d9e98722230, 0x5293d6e3164b08, 0xebbeea0cdd49d44, 0x87da85903c15a4d, 0x31fa20c217e354, 0x458c37887205f54, 0xf14131be8ac617e, 0x37f45c83b863185, 0x20df45640f61924, 0x8043dc434c6fe4a, 0xa6418df89610bea, 0xbfa9a837f35d03b, 0xfb865187b50821, 0x421be1ae217c505]
def page34 : List Nat := [0x15d02fa4b185f0d, 0xb08620dea18837f, 0x37e35842fe6a20f, 0xa05f11710bfa928, 0x2c417d158837a83, 0x886a0dfc5720bea, 0xbf92e81ec328837, 0x87d885105f4d620, 0x542bfa2e217f450, 0x454cbd88490dfd4, 0xf54042be282837d, 0x1f541c42fea2a1d, 0x885f4d640be22e6, 0x9263f4414c6fe6b, 0xea6a16f10d42bfa, 0xfa10c217f35c82f, 0xcafa4b087b50832, 0x943faa08437d500, 0x458837883205fd4, 0x74cb30bfa28637e, 0x3f5410c6fe8b987, 0xa15f09710f69904, 0x9263dd31cc2f8a0, 0xaa021dfd4532ee1]
def page35 : List Nat := [0xbe228657c35c82f, 0xcb7a87a05fd1432, 0xb20fa90e217e454, 0x458c2fa8a98fb4c, 0xfc5730f6212657d, 0x37d25902fe4a18d, 0x885f54041fa9884, 0x1a657e510cafe4b, 0xa87985f91610ee2, 0xfa18c217f25cc3b, 0x6f88b907d10521, 0x720be9aa43bd421, 0x50486fca221fb48, 0xd0c521dea16817c, 0x1dd430cafe6a10f, 0x996f10941be9ac2, 0x2a637c450c6f8a0, 0x887185f11421bf2, 0xbea2c21bc42903b, 0x86fc6b105f51521, 0xc42bf9a8857e454, 0x5210fba8618ef50, 0xd4c710bf288857e, 0x78151000000007]
def page36 : List Nat := [0x3e80010000, 0x8003846e9280428, 0xb81007b80000082, 0x26b880b00439a8, 0xf81228400003180, 0x30057800038800, 0x48800070a78000, 0x13a805cd9800c8, 0x19810000005a80, 0x2c80007c800, 0x9918568df8300, 0x40023d88149800, 0xf006f8000000100, 0x800000338000171, 0xf802980045b806a, 0x1e82006c804, 0x8000000000, 0x180000001000, 0x2800000020000, 0x808000000300000, 0x180004081000040, 0x800040820000408, 0x408300004082, 0x8081000080800]
def page37 : List Nat := [0x80838000808180, 0x848280008084000, 0x483800084830000, 0x800000848400008, 0x18000c0808000c0, 0xc0848000c08, 0xc4830000c482, 0xc8840000c4848, 0x100800000c88480, 0x8100010080800, 0x482800104820001, 0x808001088380010, 0x180044081000440, 0x800440820004408, 0x4408300044082, 0x48081000480800, 0x480838004808180, 0x848280048084000, 0x483800484830004, 0x800004848400048, 0x18004c0808004c0, 0x4c0848004c08, 0x4c4830004c482, 0x4c8840004c4848]
def page38 : List Nat := [0x500800004c88480, 0x8100050080800, 0x482800504820005, 0x808005088380050, 0x180084081000840, 0x800840820008408, 0x8408300084082, 0x88081000880800, 0x880838008808180, 0x848280088084000, 0x483800884830008, 0x800008848400088, 0x18008c0808008c0, 0x8c0848008c08, 0x8c4830008c482, 0x8c8840008c4848, 0x900800008c88480, 0x8100090080800, 0x482800904820009, 0x808009088380090, 0x1800c4081000c40, 0x800c4082000c408, 0xc4083000c4082, 0xc8081000c80800]
def page39 : List Nat := [0xc8083800c808180, 0x8482800c8084000, 0x483800c8483000c, 0x80000c8484000c8, 0x1800cc080800cc0, 0xcc084800cc08, 0xcc483000cc482, 0xcc884000cc4848, 0xd0080000cc88480, 0x81000d0080800, 0x482800d0482000d, 0x2800d0883800d0, 0x3c8408503484085, 0x484085044840850, 0xc40c5034c40c502, 0x80c9044c40c504c, 0x105024c80c904cc, 0x903d0410502d04, 0x48180802005081, 0x6c2e140903c180b, 0xe2c1409c48200f0, 0x1f0ec74371a8c45, 0x3c9a4c251208841, 0x25f2d960aa52281]
def page40 : List Nat := [0x381b8d66933990c, 0x9027f3e9e8ee74, 0xe9449239188842a, 0x54a9d46a04ea652, 0xed6eb3582b958ab, 0x6ca63b1582bf5e2, 0x6c359a8d2683399, 0xb9d4e772b89bcdb, 0xfd7dbe9ecf478b, 0x8843a17078340a0, 0x92431d8dc5e2b12, 0xf3599cc25d2b944, 0xa350a813e9ecea6, 0x566b20a853a994a, 0x536030129483d1b, 0x3010b636100555, 0x2561a5d5b014726, 0x5f306d6261007f3, 0xc46030228843a23, 0x575352028314306, 0x94c2c80157c401a, 0x114121a6501001, 0xc75394443006967, 0x4f4738754625891]
def page41 : List Nat := [0x163620066096612, 0x1b574544007b790, 0x14a49014c35893a, 0x417c4d3e72700, 0x335e22056f5d5c, 0x2f02010c3c3b428, 0x273661f04760200, 0x235f54530071700, 0xa3c591d134e8539, 0x462b5452011a598, 0xe696800871d7e42, 0x7882137c4003002, 0xa0e407d4d482704, 0x851b7d415c5b026, 0x20011647f143874, 0x6e8332124e65080, 0xe1d246a01003706, 0xd22607318407e1, 0x9023a39416a1764, 0x4300873b60247a7, 0x438686701316c45, 0x4a0002012a81127, 0x8863c602406504b, 0x47344b490173214]
def page42 : List Nat := [0x5316d6b82315e22, 0x586407323038881, 0x61a6b0f03020a04, 0x1e7e42397481305, 0x8334f1372710086, 0x5f1c1b230300108, 0xd2d553f15132222, 0x4c3331407b7a004, 0xa1e3b773877235e, 0x51045a841c7d418, 0xfc43fc41651605, 0xfd43fe10ff40fe2, 0xc42ff20fe30fd31, 0x30fc31fd41fd32f, 0xfd42fd21fe40ff, 0x40fc32fc21ff1, 0x8db44000000b00, 0x95670dd14, 0x1800008000020, 0x180000a0000400, 0x120000800003800, 0x708483042414000, 0x62410212101090, 0x32210189090c483]
def page43 : List Nat := [0x90510482064424, 0x4832424144220e2, 0x411212109090748, 0x10989094c483262, 0x550482264425322, 0x4204054220ea090, 0x102090810384081, 0x10084083420416, 0x83c4040e202051, 0x406302011010888, 0x1181098c081c60, 0x190081480406402, 0x62040f102058810, 0x1020d88105c4082, 0x103c8081640403, 0x806404232020f9, 0x4273020798101cc, 0x5a0101d0080660, 0xa4886c502803402, 0xda57d552d10f4cc, 0xc29a72562e05e9c, 0x4a136d0c284001a, 0x520c50e14109203, 0x69418200048951e]
def page44 : List Nat := [0x84f9c8202001ac5, 0x2129d3250608080, 0x9d426d02f661c28, 0xc1b348d68608002, 0x582b4c0c0800470, 0x443e7adc182000, 0xe48a8b26f220708, 0x3a58d295c202010, 0x3e91885080031e, 0x357e182000a70ca, 0xc030200110183c7, 0x1627040400384f5, 0x5cb22501828008c, 0xea9907080441930, 0x6e0c10100790973, 0xa68e83050011cb8, 0xc010100871a3058, 0xa19087c9111439d, 0x3b2a1908504c3b2, 0x20b7928809f4fcc, 0x7fa07e213cfd14, 0xef187e107e207f9, 0x200000a00185, 0x80000010000060]
def page45 : List Nat := [0x8d104297653108c, 0x9f4fa7f9208c8f8, 0x21e5e40ecfa1a80, 0x21a61d3a8638ac0, 0xa1ac021e6e40ecf, 0x40ecfa1a8153100, 0x9bd03b3c869865f, 0x7474ea1ce2b0087, 0x400000000000071, 0x80000000000006, 0x113000000001302, 0x8180000000098, 0x280448000000005, 0x24021c00000000, 0x981082040000000, 0x50084101800000, 0x2820208180000, 0x240140406000, 0xa18b0021c0000, 0x20050c58010e00c, 0x6005da0e628c310, 0x30c4284d149b2c6, 0x97ecfa1a816fd1c, 0x881885fd700c540]
def page46 : List Nat := [0x37f5c0414c2ee9b, 0x358043dfc6eb008, 0x2fcb80829869d4, 0xe018c812f59e431, 0x985df3710310bf2, 0x91d600c75f23082, 0x130bfae021e21bf, 0xe3828621dfc7150, 0x633fd9c31502c, 0x7f570c310dfa8eb, 0x43c437f38ac021d, 0xbde4e186213f59f, 0xa8d884fd760c640, 0x1bf4dd601075e21, 0x106309faec21e2, 0xc27b8b8c0a1df97, 0xe2b00873fd9c414, 0x886dc434db10df8, 0x185404c2efb9a81, 0x5409bacfa1861bf, 0xf23a61885f9700c, 0x1e2137d9e434c2d, 0xbc474c310f3a862, 0x464c36f8bec6a05]
def page47 : List Nat := [0xb7a8e18621afc5e, 0xa81886df630c540, 0x17bc9c40c42ee39, 0x391a30afeae2062, 0x427eb3c878869c4, 0xec20c613f5d8430, 0x2c71c26000009fa, 0x4288985611ccdb7, 0x2800000000080, 0x40000000000180, 0xe000000000, 0x2400000, 0xe0000000000500, 0x1e000000000, 0x4000000, 0x120000000000880, 0x26000000000, 0x5000000, 0x180000000000a80, 0x32000000000, 0x2041800000, 0xe0000000408380, 0x1021e000000081, 0x6041000000]
def page48 : List Nat := [0xf0000000c08380, 0x40206000000181, 0x8041800000, 0x200000010c8800, 0x110206000000881, 0x22041000000, 0x60000004408280, 0x11021c000000881, 0x26041000000, 0x30000004c08380, 0x14020c000000a01, 0x46041000000, 0x80000008c08380, 0x23021e000001181, 0x48040c00000, 0xe0000009008300, 0x310206000001201, 0x62041000000, 0xf000000c408700, 0x310224000001881, 0x62044c00000, 0x3000000cc08200, 0x34020c000001a01, 0x8c26082800000]
def page49 : List Nat := [0x900018c5010500, 0x240412000980a02, 0x26c08082800130, 0x90004d8c410780, 0x230412000a00982, 0x28608682800140, 0xe0005180c10500, 0x31408000a31882, 0x2c008280c00160, 0x700058010d0480, 0x130412001230982, 0x48c26082800246, 0xe000c580c10400, 0x304140018b0202, 0x64c08082800326, 0xa000cd81010480, 0x304120019b0202, 0x68c06082800346, 0xa000d580c10500, 0x14040c001ab0202, 0x6c628082400363, 0x9000d8c5010500, 0x43412001b20982, 0x48c260c0000560]
def page50 : List Nat := [0x10c4d8c5018002, 0x130600189b18a03, 0x248c260c0441246, 0x110c9188c18008, 0x10600219231183, 0xe260620c0047130, 0x11c4c0c418088, 0x10600380a1821b, 0x6280620c0073140, 0x1cc500c41808e, 0x3106029b8201883, 0x6086620c0137040, 0x50c10cc4180a8, 0x43602a18b0021b, 0x62c0086c2543160, 0x151c0c0c418028, 0x110600a38181883, 0xc060686c0170043, 0x5d80c0d0d80ae, 0x240602bb0189203, 0xc080486c0176031, 0x5d810090d80ae, 0x230602bb0209183, 0xc086020c0176041]
def page51 : List Nat := [0x5d810c04180ae, 0x310602bb0219883, 0xc620486c0176043, 0x5d8c4090d80ae, 0x343602bb1881a1b, 0xe260482c0176310, 0x1c409184c18048, 0x40601881230983, 0x66c080c0710336, 0xc40d580c18062, 0x140601881ab0203, 0x6c6280c0710363, 0x1c5c18050d8062, 0x1306018b8300a1b, 0xe48c260c0717246, 0x1c5cd8c5018062, 0x3106038b9b18a03, 0xe080620c0727030, 0x1d1c0c0c418064, 0x231601a38181883, 0xc260082c0373140, 0xdd84c010580ee, 0x243603bb098121b, 0xc260486c2776130]
def page52 : List Nat := [0x1dd85000c5806e, 0x343601bb0a0018b, 0xc280686c0776140, 0xdd8500d0d84ee, 0x3201a18140f0b06, 0x46433b39322c272, 0xd68635f5853504a, 0x8f8b857f7a73706, 0x7b2ada5a29e9a92, 0xe8e3dbd4cfc7bfb, 0xd4a4bfffaf5f1ed, 0x9897960b8d8c2c2, 0xd370b1a05063e1f, 0xd1b06053f62612, 0xd05216766650b3f, 0xb706f0b0c393f0, 0xd2c4849363e1706, 0x2557561b417f7e2, 0x50b04033e0d7b29, 0xf30206a2b1f060, 0x594224f005d180e, 0xc4c1a010d32279, 0xc1f04211e801c2c, 0x467a792d0b402d2]
def page53 : List Nat := [0x86e6d0b8a192c0c, 0x1b000d103d0c012, 0xc13163076753152, 0x807843a3f14050, 0x3908f2051454485, 0x380b121104401d2, 0xf83822e1b1a500f, 0x150b0f0231224f2, 0xf1a43353e0d6c6b, 0x910c7c2e1b7d532, 0x4630b3b0e219392, 0x2e5c5a1a2d2a336, 0xf260a1a8988095b, 0x29091b87860a2a4, 0xe69682c3c0c2b42, 0x34542625558e1a4, 0x75f2f605e1b2c2b, 0x2d0b4d8b192d0b4, 0xc0c59582918811c, 0x117473400b78772, 0xc1a31002472710c, 0xf51831f790d30bf, 0xbf4d810bf4d840b, 0xff10f10bf91930]
def page54 : List Nat := [0x30f7d0e30b718d4, 0x630b74d840afd18, 0x5a40b7d8d40ff10, 0xd8143ff90530bfc, 0xf50130ff10c10bf, 0xfd8c710ff50f10f, 0xbf58031ef90c40, 0x43ff50330bdc584, 0x830bf18143bf41a, 0x1b30bf185309fd5, 0xc640ff8c310bf5, 0x750c43bfc5830ff, 0xbf51a31bf18543e, 0xfd90710ff10310, 0x30ef50d40bf91a3, 0xb40bfc5b43f710e, 0x1a43bbc9840bf4d, 0xd0f10b7cd840bfc, 0xfd0240bf4da40ff, 0xbf91a31bf41a41e, 0xbfc1b43ff10530, 0x41bfc5b30ffc5a3, 0xb43ef10e40bf980, 0x5840ff90f10bf41]
def page55 : List Nat := [0xc5a40bdc5830bfc, 0xf4db10ff50310ff, 0xff8c540bfc5a43b, 0xbf41a31bfc5a30, 0x41f7d0c30f7cc23, 0xa41bf51810bfc1a, 0x9830f750f30bf4d, 0x58041bf4d841bbc, 0xfd03109fd5840bf, 0xffcc310bf8d810f, 0xbf51a30bf58043, 0x40af11930bf5183, 0xd30bfd8d40ef50f, 0x5b40bf51b10f750, 0xc310bf98043bfc, 0xf51830bf91810ff, 0xff0c540ffd0130a, 0xbf98443ef90e40, 0x40efd0d40af9193, 0x31ff90310bf185, 0x23eff4c310bf98, 0xb320e1a0013b900, 0x140280040002552, 0xd246b000018240e]
def page56 : List Nat := [0xbf02120002009, 0xb000600c570000e, 0xb149000a995d57a, 0x200240f0004, 0x1000000006000, 0x60000000280000, 0xe000000, 0x480000002, 0x160000000a0, 0x680000003000, 0x1e0000000e0000, 0x880000004000000, 0x120000000, 0x5000000026, 0x160000000a80, 0x600000002e000, 0xf0000000c80000, 0x400030210000081, 0xc08500006042, 0x312080001810f0, 0x8480006243c00, 0x21c0002010a0001, 0x700008240c00040, 0x219000001048]
def page57 : List Nat := [0x8642800043212, 0x881040004408180, 0x42000130208000, 0xa0004c08480026, 0xc0013021e000981, 0x5008180026044, 0x140214000a01090, 0xc8480028043800, 0x21c000a190a0005, 0x380042043c00210, 0x1181090008c08, 0x46043c00230214, 0x1890f0008c48200, 0x4240024020c001, 0xe0009008500048, 0x800241206001201, 0x90c8480048243, 0x3102080012190a0, 0x408780062043800, 0x23000188113000c, 0x480066041000310, 0x19810a000cc08, 0x66044c0033021e, 0xa010a000d008480]
def page58 : List Nat := [0x642800343212001, 0xc0c410000068, 0x30343402181a1a, 0xc45010086228080, 0x340400189202000, 0xd0088048680031, 0x400201882001009, 0x8226080441130, 0x209182011048c10, 0x602080041330400, 0xa1a0010c0410088, 0x80043143402218, 0x10c8c10088646, 0x43240402219202, 0xcc410088662080, 0x130402230982001, 0xd0008c26082446, 0x400300a1a011805, 0xc226080461130, 0x308a02011845010, 0x228680461143400, 0xa020118c501000c, 0x280063140412318, 0x4188c500a0c46]
def page59 : List Nat := [0x10624140283120a, 0x1890d00a0c48680, 0x343402831a1a004, 0x100a6028080106, 0x400980a1a004c05, 0x26048280530241, 0x98121a014c090d0, 0xc02080130340400, 0x202004d804100a6, 0x825360404029b0, 0x14d81050026c08, 0x5362404009b020a, 0xd89050026c48080, 0x3104009b120a014, 0x10026c62080536, 0x4129b1a02014d8d, 0x28028680540130, 0xa01982015008c50, 0x626080543043412, 0x8820150c5010028, 0x80543330402a19, 0x15180410028668, 0x546030400a30082, 0x180c104a8c06080]
def page60 : List Nat := [0x31402a3018a005, 0xc100a8c46080146, 0x402a3118a005188, 0xa8c62080146231, 0xa3198200518c410, 0x6280146330402, 0x20a005800c500ac, 0x680160041402b00, 0x958010d00ac008, 0x630041400b0021a, 0xd80410046228080, 0x314031b0082018, 0x10048062080640, 0x4012192020190c9, 0x48c02080646010, 0x230982019184c10, 0xc46080246130413, 0x18a009188c100c8, 0x280246231403231, 0x9800c500cc006, 0x26004140330020a, 0x8010d00cc008680, 0x4340130021a099, 0xc5004c208680661]
def page61 : List Nat := [0x40183118a01c188, 0x60c48280706241, 0x83121a01c1890d0, 0xc68680706343401, 0x20201c400c100e0, 0x80710130401880, 0x1c405010062026, 0x310143401880a02, 0x408c100e2046080, 0x23140388118a00c, 0x50062048080310, 0x40188120a01c409, 0x62048680710243, 0x8b018200c40d0d0, 0xc08080316030403, 0x18200c5810100e2, 0x803162304038b1, 0xc5890100e2c48, 0x3162434038b121a, 0x58cc100e2c66080, 0x3404038b1a0200c, 0xd00e2c68680316, 0x41393018201c58d, 0x4e4c08080726030]
def page62 : List Nat := [0x980a0200c981010, 0x46080330143401, 0x88200cc08c100e6, 0x80330310403981, 0x9cd810100e6c08, 0x3401304039b0202, 0x9010068028680, 0x310401a0120201d, 0x10068062080740, 0x401a18a0201d0c5, 0xe8646080743230, 0xa3018200d0cc410, 0xc06082746030403, 0x18209d580c10068, 0x82756040401ab0, 0xd8050d006ac08, 0x763140403b18a02, 0x8016006c628082, 0x1b860138400d02a, 0x300b02909421078, 0x418fa3c0e0358d0, 0x5413e4c1264690e, 0x68994611765a95c, 0x7e1ea779d0711b0]
def page63 : List Nat := [0x912348a21c82a02, 0xa5a869ea7098250, 0xb82d8b3ac2ae2a8, 0xce322c630cbfaee, 0xe3382ddb66d5b44, 0xf83d4f23bceb396, 0xb41f04402fdbea, 0x1ec6d194571343d, 0x32cbd2bca125489, 0x47d11404f7394db, 0x7563545474dd29, 0x4003508351a61a, 0x871784c2203010, 0x54aa01833098191, 0xac240646a302c12, 0x8c309818268b450, 0x131181ec5200418, 0x4c1e12359a84a47, 0x21c0104cf077060, 0x8a00625111d048f, 0x481b16070322a0d, 0x68e030082c8d460, 0x808c70605c8dc2, 0x78223a8e84a3822]
def page64 : List Nat := [0x84708bcde41207c, 0x4321456410982c0, 0x4a36120b8401815, 0x4290918cc4250c0, 0xb8bc940c4ca0d0, 0x901e12503846812, 0x65a0c848260172b, 0x104966b20b0acb, 0x5c2a0f09035deee, 0xc0c09a72004a090, 0x705c1007009fcf, 0x1c060200800e06f, 0xf180b04c180a8b8, 0x882024720b9c41, 0x4c1e0508ac56012, 0x4380238dc4121c8, 0x88787cbd2c0f42, 0x68260c76bb01e1d, 0xc1609030ca64028, 0x118ccec7507a740, 0xc260e040782210, 0xe200909020ad561, 0x784c7c3f6e1708, 0x44200e09009d0e7]
def page65 : List Nat := [0xe110903c08c7630, 0x339981813032693, 0x20841006bedf40f, 0x8984b8342451070, 0xb0481a097f03c0, 0xe822d86b8301cff, 0xc0d838320c0f038, 0x89bac8e52094201, 0x4524910903c1851, 0x60d0903c0801168, 0x3e9f09e13014321, 0x4420c96403c1801, 0x612110b4660e008, 0x7184be0c2f1745, 0x3c0e4008369b20d, 0xc121c3c5e010098, 0x1f048220507bdde, 0xa4d04009335980d, 0x700a05000d091, 0x21ba9d2462204c1, 0x481aef7703c1e0d, 0xe13063b5d8040f8, 0x1f3cde411090501, 0xa1c0df180486245]
def page66 : List Nat := [0xa38094349046190, 0x7abd01e11032592, 0x48860e040f0220c, 0x20d0a2e936301d8, 0x23041e2f00983c2, 0x8f67a258481605, 0x40181c081813068, 0xf8380c552a0702, 0x802001b045acd5, 0x8a3090c02210018, 0x499442431030094, 0x314301090902294, 0xc1306025f84e268, 0x4823c1a33093f42, 0x6402135aad02c30, 0xe138d058240d054, 0x743a1a49091408, 0x4822021c04178bb, 0x90582124264c230, 0x404970b75b0341, 0x4641055aa82613, 0xca652858260f028, 0x10804246d360340, 0x7024a285034246e]
def page67 : List Nat := [0x81207c7874118ec, 0x98a85c2d032790, 0xe02610032bd5c3e, 0xa0c07040080f7cb, 0xd84c1ed067b381, 0x41c381cb6ca612, 0x60c080047c11613, 0x538180216532942, 0x746509448482617, 0x2580695cac30098, 0x780580bf08848b, 0x941c08693441a0c, 0x2026290024c4618, 0x781a210f148482, 0x482008099d02e73, 0xa05238f97ce61f8, 0x932d940c1c04c8, 0x1c4e076f374262c, 0xf107fa61fe41169, 0xffe61fe43ff207, 0xfe87fc31fe207f1, 0x81fe31ff887f043, 0xfe30fea1ffd03fa, 0xb0008463bf861]
def page68 : List Nat := [0x54f000000440000, 0x60000200000c0, 0x48000200000e00, 0x3c0001c0000a000, 0x800013000090000, 0xc0000540002, 0x204041020000019, 0x212181010c0800, 0x1000c4808624003, 0x800804244020220, 0x44320020901104, 0x29810010c848864, 0x500802604253020, 0x8640140212a0101, 0x200a190950c80a, 0x9008c084c604063, 0x80c804023120318, 0x64120120109900, 0x32190190c804824, 0xc4080e204024321, 0x804033020398100, 0x3203a1900d0080e, 0xb0804006864274, 0x8a4a11e1916928f]
def page69 : List Nat := [0x45c0bcb7b3afaba, 0xbc00238660b85e7, 0xb4c8a44e440396f, 0x943917036d858e6, 0x6fb0f2664199623, 0x3ae3640e40a0167, 0xd868e282c16bac4, 0x97df44106aaa0a3, 0xe31881e2972783, 0xd751c40e2eba0c4, 0x906450820101162, 0x8a098773c1160f1, 0xe0153092c86963, 0x8e4903d20513984, 0x7f39a40a0266248, 0x126488]
def storagePage (p : Nat) : List Nat := (if p < 35 then (if p < 17 then (if p < 8 then (if p < 4 then (if p < 2 then (if p < 1 then page0 else page1) else (if p < 3 then page2 else page3)) else (if p < 6 then (if p < 5 then page4 else page5) else (if p < 7 then page6 else page7))) else (if p < 12 then (if p < 10 then (if p < 9 then page8 else page9) else (if p < 11 then page10 else page11)) else (if p < 14 then (if p < 13 then page12 else page13) else (if p < 15 then page14 else (if p < 16 then page15 else page16))))) else (if p < 26 then (if p < 21 then (if p < 19 then (if p < 18 then page17 else page18) else (if p < 20 then page19 else page20)) else (if p < 23 then (if p < 22 then page21 else page22) else (if p < 24 then page23 else (if p < 25 then page24 else page25)))) else (if p < 30 then (if p < 28 then (if p < 27 then page26 else page27) else (if p < 29 then page28 else page29)) else (if p < 32 then (if p < 31 then page30 else page31) else (if p < 33 then page32 else (if p < 34 then page33 else page34)))))) else (if p < 52 then (if p < 43 then (if p < 39 then (if p < 37 then (if p < 36 then page35 else page36) else (if p < 38 then page37 else page38)) else (if p < 41 then (if p < 40 then page39 else page40) else (if p < 42 then page41 else page42))) else (if p < 47 then (if p < 45 then (if p < 44 then page43 else page44) else (if p < 46 then page45 else page46)) else (if p < 49 then (if p < 48 then page47 else page48) else (if p < 50 then page49 else (if p < 51 then page50 else page51))))) else (if p < 61 then (if p < 56 then (if p < 54 then (if p < 53 then page52 else page53) else (if p < 55 then page54 else page55)) else (if p < 58 then (if p < 57 then page56 else page57) else (if p < 59 then page58 else (if p < 60 then page59 else page60)))) else (if p < 65 then (if p < 63 then (if p < 62 then page61 else page62) else (if p < 64 then page63 else page64)) else (if p < 67 then (if p < 66 then page65 else page66) else (if p < 68 then page67 else (if p < 69 then page68 else page69)))))))
def storageWord (i : Nat) := (storagePage (i / 24)).getD (i % 24) 0
def a0Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xedbdedbdedbdedb, 0xdbdedbdedbdedbd, 0xdbdedbde])
  | 3 => BitVec.ofNat 152 (big [0xbeebbeebbeebbee, 0xeebbeebbeebbeeb, 0xeebbeebb])
  | 4 => BitVec.ofNat 152 (big [0x80a180a180a180a, 0xa180a180a180a1, 0xa180a18])
  | _ => 0

def a0Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x43204320432043, 0x432043204320432, 0x43204320])
  | 3 => BitVec.ofNat 152 (big [0x8c408c408c408c, 0x8c408c408c408c4, 0x8c408c40])
  | 4 => BitVec.ofNat 152 (big [0xdcfedcfedcfedcf, 0xcfedcfedcfedcfe, 0xcfedcfed])
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
def a0 : Atlas := ⟨3,rawDecor 26 a0Pos a0Neg,repeatWord 14700030438798327756,a0Count,a0Rec,(fun _ _ => 0),a0Loc⟩
def a0Domains : Catalog := []
def a1Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf7ffff6fffbfb6f, 0x7ffff6fffbfb6fb, 0xfbfb6fbf])
  | 1 => BitVec.ofNat 152 (big [0x9d9cedfc4fd1c9e, 0xd9cedfc4fd1c9e7, 0xfd1c9e79])
  | 3 => BitVec.ofNat 152 (big [0x5ff496b7167bf91, 0xff496b7167bf91e, 0x67bf91e5])
  | 4 => BitVec.ofNat 152 (big [0x6c3f76dee45e4f5, 0xc3f76dee45e4f57, 0x45e4f576])
  | _ => 0

def a1Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x40000004009128, 0x400000040091284, 0x912840])
  | 1 => BitVec.ofNat 152 (big [0x622994e18d10c86, 0x22994e18d10c868, 0xd10c8686])
  | 3 => BitVec.ofNat 152 (big [0xa13a21073740e11, 0x13a21073740e111, 0x740e111a])
  | 4 => BitVec.ofNat 152 (big [0x9144b81cb8120d5, 0x144b81cb8120d58, 0x8120d589])
  | _ => 0

def a1Count (k : Nat) : Nat :=
  match k with
  | 4 => 12
  | 5 => 1
  | _ => 0

def a1Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (3+i*15) 15
  | 5 => field storageWord (363+i*4) 4
  | _ => 0

def a1Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 12 24 (field storageWord (183+(tag % 24)*5) 5) tag
  | 5 => 0
  | _ => 0

def a1Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 312 3 351 2 303 3 i
  | 5 => hintsAt storageWord 385 3 391 3 367 3 i
  | _ => []

def a1 : Atlas := ⟨5,rawDecor 27 a1Pos a1Neg,repeatWord 17197745632164096648,a1Count,a1Rec,(fun _ _ => 0),a1Loc⟩
def a1Domains : Catalog := [(repeatWord 7378697629483820646, 4), (repeatWord 6172840429334713770, 4), (repeatWord 6149008514797120170, 4), (repeatWord 14714328930390887475, 4), (repeatWord 14757226376558555955, 4), (repeatWord 18374687579166474495, 4)]
def a2Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xf5eef5eef5eef5e, 0x5eef5eef5eef5ee, 0x5eef5eef])
  | 4 => BitVec.ofNat 152 (big [0x8e398e398e398e3, 0xe398e398e398e39, 0xe398e398])
  | 5 => BitVec.ofNat 152 (big [0x114211421142114, 0x142114211421142, 0x14211421])
  | _ => 0

def a2Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x292029202920292, 0x920292029202920, 0x92029202])
  | 4 => BitVec.ofNat 152 (big [0xbb24bb24bb24bb2, 0xb24bb24bb24bb24, 0xb24bb24b])
  | 5 => BitVec.ofNat 152 (big [0xfb6dfb6dfb6dfb6, 0xb6dfb6dfb6dfb6d, 0xb6dfb6df])
  | _ => 0

def a2Count (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def a2Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (409+i*3) 3
  | _ => 0

def a2Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => 0
  | _ => 0

def a2Hints : Hints := fun _ _ => []
def a2 : Atlas := ⟨2,rawDecor 52 a2Pos a2Neg,repeatWord 264917877780720,a2Count,a2Rec,(fun _ _ => 0),a2Loc⟩
def a2Domains : Catalog := []
def a3Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xd48b0cd18e8b2da, 0xb6a458668c74596, 0x33463a2c])
  | 2 => BitVec.ofNat 152 (big [0x9bd3ddd997bb1d3, 0x74de9eeeccbdd8e, 0x77665eec])
  | 3 => BitVec.ofNat 152 (big [0xc5dcefe61fd6f18, 0xc62ee77f30feb78, 0xbf987f5b])
  | 4 => BitVec.ofNat 152 (big [0x6fabf78ee9ea2ad, 0xab7d5fbc774f515, 0xde3ba7a8])
  | _ => 0

def a3Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xf376f45a2adfa9e, 0xa79bb7a2d156fd4, 0xd168ab7e])
  | 2 => BitVec.ofNat 152 (big [0xc0002a0c500141, 0x50600015062800a, 0xa831400])
  | 3 => BitVec.ofNat 152 (big [0x822240100052a10, 0x841112008002950, 0x40014a])
  | 4 => BitVec.ofNat 152 (big [0x6044804a008108c, 0x230224025004084, 0x1280204])
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
  | 2 => field storageWord (412+i*37) 37
  | 3 => field storageWord (488+i*26) 26
  | 4 => field storageWord (692+i*15) 15
  | 5 => field storageWord (858+i*4) 4
  | _ => 0

def a3Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => hashRow 2 2 (field storageWord (486+(tag % 2)*1) 1) tag
  | 3 => hashRow 6 12 (field storageWord (644+(tag % 12)*4) 4) tag
  | 4 => hashRow 6 6 (field storageWord (782+(tag % 6)*4) 4) tag
  | 5 => 0
  | _ => 0

def a3Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 814 4 842 2 806 2 i
  | 5 => hintsAt storageWord 868 2 872 2 862 2 i
  | _ => []

def a3 : Atlas := ⟨5,rawDecor 30 a3Pos a3Neg,repeatWord 18443352909265761216,a3Count,a3Rec,(fun _ _ => 0),a3Loc⟩
def a3Domains : Catalog := [(repeatWord 1085102592571150095, 4), (repeatWord 4340410370284600380, 4), (repeatWord 71777214294589695, 3), (repeatWord 281470681808895, 3)]
def a4Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xfbfffc7ff7fcfe9, 0xfbfffc7ff7fcfe9, 0xff7fcfe9])
  | 2 => BitVec.ofNat 152 (big [0xf5ffebf7dfef9bf, 0xf5ffebf7dfef9bf, 0x7dfef9bf])
  | 3 => BitVec.ofNat 152 (big [0x5e3ed7c8bedf776, 0x5e3ed7c8bedf776, 0x8bedf776])
  | 4 => BitVec.ofNat 152 (big [0x9ee39fea3f97e5e, 0x9ee39fea3f97e5e, 0xa3f97e5e])
  | _ => 0

def a4Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x401c2913144d41, 0x401c2913144d41, 0x13144d41])
  | 2 => BitVec.ofNat 152 (big [0xa4410648ca00ba, 0xa4410648ca00ba, 0x48ca00ba])
  | 3 => BitVec.ofNat 152 (big [0xa169188102bd374, 0xa169188102bd374, 0x102bd374])
  | 4 => BitVec.ofNat 152 (big [0x620e6a1e1602e0e, 0x620e6a1e1602e0e, 0xe1602e0e])
  | _ => 0

def a4Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a4Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (878+i*4) 4
  | _ => 0

def a4Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a4Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 883 1 885 1 882 1 i
  | _ => []

def a4 : Atlas := ⟨4,rawDecor 30 a4Pos a4Neg,repeatWord 18212768828193030336,a4Count,a4Rec,(fun _ _ => 0),a4Loc⟩
def a4Domains : Catalog := [(repeatWord 18374966859414961920, 4)]
def a5Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x5be15ec63acbf86, 0xdf0af631d65fc35, 0xeb2fe1aa])
  | 3 => BitVec.ofNat 152 (big [0x3cddfe8ff3eef6c, 0xe6eff47f9f77b67, 0xcfbbdb39])
  | 4 => BitVec.ofNat 152 (big [0xd7f7d3f03ff7a9f, 0xbfbe9f81ffbd4fe, 0xffdea7f6])
  | 5 => BitVec.ofNat 152 (big [0x104100003200a04, 0x820800019005020, 0xc8028100])
  | _ => 0

def a5Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xa47465990a5ad86, 0x23a32cc852d6c32, 0x296b6195])
  | 3 => BitVec.ofNat 152 (big [0xc226182c508662c, 0x1130c1628433160, 0x42198b06])
  | 4 => BitVec.ofNat 152 (big [0x26080ef06180a89, 0x304077830c05449, 0x8602a249])
  | 5 => BitVec.ofNat 152 (big [0xef2ffffcff8eead, 0x797fffe7fc7756f, 0xfe3bab7f])
  | _ => 0

def a5Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a5Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (886+i*4) 4
  | _ => 0

def a5Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a5Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 891 1 893 1 890 1 i
  | _ => []

def a5 : Atlas := ⟨4,rawDecor 58 a5Pos a5Neg,repeatWord 14699749188032265984,a5Count,a5Rec,(fun _ _ => 0),a5Loc⟩
def a5Domains : Catalog := [(repeatWord 14757395258967641292, 4)]
def a6Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x89180a0a4018891, 0x1889180a0a4018, 0x9180a0a4])
  | 2 => BitVec.ofNat 152 (big [0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff])
  | 3 => BitVec.ofNat 152 (big [0xe1a081308100e, 0x8100e1a0813081, 0xe1a0813])
  | 5 => BitVec.ofNat 152 (big [0x260444148124260, 0x124260444148124, 0x60444148])
  | _ => 0

def a6Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x4d57f0f6dc1d4d5, 0xc1d4d57f0f6dc1d, 0xd57f0f6d])
  | 2 => BitVec.ofNat 152 (big [0x4fc08244040f4fc, 0x40f4fc08244040f, 0xfc082440])
  | 3 => BitVec.ofNat 152 (big [0x4aee5fc6331f4ae, 0x31f4aee5fc6331f, 0xaee5fc63])
  | 5 => BitVec.ofNat 152 (big [0x278bc3ebe54f278, 0x54f278bc3ebe54f, 0x78bc3ebe])
  | _ => 0

def a6Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a6Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (894+i*4) 4
  | _ => 0

def a6Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a6Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 899 1 901 1 898 1 i
  | _ => []

def a6 : Atlas := ⟨4,rawDecor 46 a6Pos a6Neg,repeatWord 13511005861589232,a6Count,a6Rec,(fun _ _ => 0),a6Loc⟩
def a6Domains : Catalog := [(repeatWord 17361641481138401520, 4)]
def a7Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xd7ff77e5fbf29db, 0x7ff77e5fbf29db7, 0xbf29db7d])
  | 1 => BitVec.ofNat 152 (big [0xf9fded7fe69f7e6, 0x9fded7fe69f7e6e, 0x69f7e6ef])
  | 2 => BitVec.ofNat 152 (big [0xaab9bcfad6ade74, 0xab9bcfad6ade74b, 0x6ade74ba])
  | 3 => BitVec.ofNat 152 (big [0x7eea72e5bd65c9d, 0xeea72e5bd65c9db, 0xd65c9db7])
  | _ => 0

def a7Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x2020c2cc0090158, 0x20c2cc00901588, 0x9015882])
  | 1 => BitVec.ofNat 152 (big [0x49010222642286, 0x490102226422861, 0x64228610])
  | 2 => BitVec.ofNat 152 (big [0x70066648d11cc70, 0x66648d11cc704, 0x11cc7047])
  | 3 => BitVec.ofNat 152 (big [0x91181c23816bc85, 0x1181c23816bc854, 0x16bc8549])
  | _ => 0

def a7Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a7Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (902+i*4) 4
  | _ => 0

def a7Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a7Hints : Hints := fun _ _ => []
def a7 : Atlas := ⟨3,rawDecor 15 a7Pos a7Neg,repeatWord 16918030148870662856,a7Count,a7Rec,(fun _ _ => 0),a7Loc⟩
def a7Domains : Catalog := []
def a8Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xeb9c77beb4e99c3, 0xfd0adff5cf7fe88, 0x5b7ff87a])
  | 1 => BitVec.ofNat 152 (big [0xb6fb5891da9a735, 0x2de4b1aa71eacff, 0xebed4fff])
  | 2 => BitVec.ofNat 152 (big [0x975cbe9ebc56ac, 0x36ffb28e39e3577, 0xbce077c7])
  | 3 => BitVec.ofNat 152 (big [0x7f7bb74283375da, 0xaafb75670c117a7, 0x9e12fcd9])
  | 4 => BitVec.ofNat 152 (big [0x9f2ee1ed7556a3a, 0x537d0e16e71c187, 0x2e5fbffa])
  | _ => 0

def a8Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x800013a0a0a8880, 0x28000180402208, 0x584114])
  | 1 => BitVec.ofNat 152 (big [0x203a04141812701, 0xa445810021c88e2, 0x16008061])
  | 2 => BitVec.ofNat 152 (big [0x410149c9a2c50ac, 0x438a14de9021609, 0x91a0502])
  | 3 => BitVec.ofNat 152 (big [0x4f702412031155a, 0x8248e201a80585, 0xb4811068])
  | 4 => BitVec.ofNat 152 (big [0x1a0cc8065546232, 0xd034386c310846, 0xe803a881])
  | _ => 0

def a8Count (k : Nat) : Nat :=
  match k with
  | 4 => 23
  | 5 => 146
  | 6 => 158
  | 7 => 34
  | 8 => 1
  | _ => 0

def a8Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (906+i*49) 49
  | 5 => field storageWord (2631+i*38) 38
  | 6 => field storageWord (12259+i*27) 27
  | 7 => field storageWord (25615+i*16) 16
  | 8 => field storageWord (27980+i*5) 5
  | _ => 0

def a8Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 23 70 (field storageWord (2033+(tag % 70)*6) 6) tag
  | 5 => hashRow 146 73 (field storageWord (8179+(tag % 73)*9) 9) tag
  | 6 => hashRow 158 79 (field storageWord (16525+(tag % 79)*9) 9) tag
  | 7 => hashRow 34 17 (field storageWord (26159+(tag % 17)*6) 6) tag
  | 8 => 0
  | _ => 0

def a8Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2549 3 2621 2 2453 32 i
  | 5 => hintsAt storageWord 10189 8 11365 6 8836 33 i
  | 6 => hintsAt storageWord 19447 10 21037 7 17236 33 i
  | 7 => hintsAt storageWord 26870 8 27150 5 26261 21 i
  | 8 => hintsAt storageWord 27986 1 27988 1 27985 1 i
  | _ => []

def a8 : Atlas := ⟨8,rawDecor 31 a8Pos a8Neg,repeatWord 18368752179175156424,a8Count,a8Rec,(fun _ _ => 0),a8Loc⟩
def a8Domains : Catalog := [(repeatWord 1085102592571150095, 6), (repeatWord 7378697629483820646, 6), (repeatWord 11936128518282651045, 6), (repeatWord 6148914691236517205, 5), (repeatWord 3689348814741910323, 5), (repeatWord 17361641481138401520, 5), (repeatWord 18374966859414961920, 5), (repeatWord 18446462603027742720, 5), (repeatWord 14714328930390887475, 5), (repeatWord 14757226376558555955, 5), (repeatWord 18374687579166474495, 5), (repeatWord 71777214294589695, 4), (repeatWord 281470681808895, 4), (repeatWord 6124988953138320640, 4), (repeatWord 6148820867675914240, 4), (repeatWord 3472328296227680304, 4)]
def a9Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xd5755fe1bf4439b, 0x9b6dfc5f9456d5d, 0xb8cd70fb])
  | 2 => BitVec.ofNat 152 (big [0xcdb7b58de497796, 0xf264b9bf90dc96c, 0x3b7b2ddf])
  | 3 => BitVec.ofNat 152 (big [0x6b5b6aeec359e3d, 0x7ffb55f82bf2465, 0xce77f1ef])
  | 4 => BitVec.ofNat 152 (big [0x10c7cb7f9db306f, 0xdc0f0ee9e599bb6, 0xdfcbffe6])
  | 5 => BitVec.ofNat 152 (big [0xc4531e05a51521f, 0x9a408c1f001012c, 0x1000416f])
  | _ => 0

def a9Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x214410709f44301, 0x2684e540844d9c, 0x65682854])
  | 2 => BitVec.ofNat 152 (big [0xc608a1886092496, 0xd86202b9091062, 0x181082a9])
  | 3 => BitVec.ofNat 152 (big [0x28194204414923c, 0x3c0138ca20e224c, 0x36a50084])
  | 4 => BitVec.ofNat 152 (big [0x1487582194b102b, 0x2212c0a08130282, 0x4997303a])
  | 5 => BitVec.ofNat 152 (big [0x7cdffe25f5fd23f, 0xbebffafbf3f67fe, 0x7fbf77fe])
  | _ => 0

def a9Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 7 => 1
  | _ => 0

def a9Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (27989+i*16) 16
  | 7 => field storageWord (28047+i*5) 5
  | _ => 0

def a9Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | 7 => 0
  | _ => 0

def a9Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 28023 3 28029 3 28005 3 i
  | 7 => hintsAt storageWord 28070 3 28076 3 28052 3 i
  | _ => []

def a9 : Atlas := ⟨7,rawDecor 62 a9Pos a9Neg,repeatWord 18212768828247506880,a9Count,a9Rec,(fun _ _ => 0),a9Loc⟩
def a9Domains : Catalog := [(repeatWord 3689348814741910323, 5), (repeatWord 14757395258967641292, 5), (repeatWord 1085102592571150095, 5), (repeatWord 17361641481138401520, 5), (repeatWord 18446462603027742720, 5), (repeatWord 18374966855136706560, 4), (repeatWord 18446462598732840960, 4)]
def a10Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xeff6ff86ab4fb75, 0xcdff7f3dbf48973, 0xdfb9ee2f])
  | 2 => BitVec.ofNat 152 (big [0xb34fbba5f0f69d4, 0x74d2fb26964fe0e, 0x148de457])
  | 3 => BitVec.ofNat 152 (big [0xdcd9d77fdefa6aa, 0x7bffa2fbeff769d, 0x6b7f9fff])
  | 4 => BitVec.ofNat 152 (big [0x8886d58792de330, 0x6df2921b2604402, 0x12b82c50])
  | 5 => BitVec.ofNat 152 (big [0xb6b719e7b3bd11b, 0xe53f948708cddfa, 0xb2d23adb])
  | _ => 0

def a10Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x27a0d980084d925, 0x2160e6388820001, 0x403220])
  | 2 => BitVec.ofNat 152 (big [0x904c5a3460f68d0, 0x8b129502f249d86, 0xc1f40bf])
  | 3 => BitVec.ofNat 152 (big [0x8110217d612202, 0x8110802513000, 0x84900082])
  | 4 => BitVec.ofNat 152 (big [0x8fb7dfffd6deb33, 0xeb99f691b71f425, 0xf6d447e6])
  | 5 => BitVec.ofNat 152 (big [0x8e1b0160b3a811b, 0xf48a4b57005c1ba, 0x81c54908])
  | _ => 0

def a10Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a10Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (28094+i*5) 5
  | _ => 0

def a10Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a10Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 28123 4 28131 3 28099 3 i
  | _ => []

def a10 : Atlas := ⟨7,rawDecor 62 a10Pos a10Neg,repeatWord 18212838148147314624,a10Count,a10Rec,(fun _ _ => 0),a10Loc⟩
def a10Domains : Catalog := [(repeatWord 3689517697150995660, 6), (repeatWord 18374687579166474495, 6), (repeatWord 1085102592571150095, 5), (repeatWord 17361641481138401520, 5), (repeatWord 18446462603027742720, 5), (repeatWord 4294967295, 5), (repeatWord 18446744069414584320, 5), (repeatWord 57421771435671756, 4)]
def a11Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfffbdfbefbffdf6, 0xffbdfbefbffdf6f, 0xbffdf6ff])
  | 2 => BitVec.ofNat 152 (big [0xcde7e5fba5f072b, 0xde7e5fba5f072ba, 0x5f072bac])
  | 4 => BitVec.ofNat 152 (big [0x7d1a070ef83e8b2, 0xd1a070ef83e8b23, 0x83e8b237])
  | 5 => BitVec.ofNat 152 (big [0xe9ef9779f452cf, 0xe9ef9779f452cff, 0xf452cff0])
  | _ => 0

def a11Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x401080900150, 0x4010809001500, 0x90015000])
  | 2 => BitVec.ofNat 152 (big [0x14509a7260a462a, 0x4509a7260a462a5, 0xa462a51])
  | 4 => BitVec.ofNat 152 (big [0x82d3b653d2b68aa, 0x2d3b653d2b68aac, 0x2b68aac8])
  | 5 => BitVec.ofNat 152 (big [0xe8e01615826608f, 0x8e01615826608f0, 0x26608f0e])
  | _ => 0

def a11Count (k : Nat) : Nat :=
  match k with
  | 3 => 15
  | 4 => 12
  | 5 => 1
  | _ => 0

def a11Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (28155+i*26) 26
  | 4 => field storageWord (28620+i*15) 15
  | 5 => field storageWord (28906+i*4) 4
  | _ => 0

def a11Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 15 15 (field storageWord (28545+(tag % 15)*5) 5) tag
  | 4 => hashRow 12 12 (field storageWord (28800+(tag % 12)*5) 5) tag
  | 5 => 0
  | _ => 0

def a11Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 28861 3 28900 1 28860 1 i
  | 5 => hintsAt storageWord 28911 1 28913 1 28910 1 i
  | _ => []

def a11 : Atlas := ⟨5,rawDecor 53 a11Pos a11Neg,repeatWord 12297917687000637600,a11Count,a11Rec,(fun _ _ => 0),a11Loc⟩
def a11Domains : Catalog := [(repeatWord 281470681808895, 4)]
def a12Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xdeffdcf7f49c6ae, 0xdeffdcf7f49c6ae, 0x7f49c6ae])
  | 3 => BitVec.ofNat 152 (big [0x3f4fb9bc937c1c7, 0x3f4fb9bc937c1c7, 0xc937c1c7])
  | 4 => BitVec.ofNat 152 (big [0x566473883d37c17, 0x566473883d37c17, 0x83d37c17])
  | 5 => BitVec.ofNat 152 (big [0x4011c52908c0ae, 0x4011c52908c0ae, 0x2908c0ae])
  | _ => 0

def a12Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x20022010401140a, 0x20022010401140a, 0x401140a])
  | 3 => BitVec.ofNat 152 (big [0xc28846aa92020c5, 0xc28846aa92020c5, 0xa92020c5])
  | 4 => BitVec.ofNat 152 (big [0xa91f6490e39741f, 0xa91f6490e39741f, 0xe39741f])
  | 5 => BitVec.ofNat 152 (big [0xfbbff7bbfbdf4ff, 0xfbbff7bbfbdf4ff, 0xbfbdf4ff])
  | _ => 0

def a12Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a12Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (28914+i*4) 4
  | _ => 0

def a12Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a12Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 28919 1 28921 1 28918 1 i
  | _ => []

def a12 : Atlas := ⟨4,rawDecor 60 a12Pos a12Neg,repeatWord 17294087486980489200,a12Count,a12Rec,(fun _ _ => 0),a12Loc⟩
def a12Domains : Catalog := [(repeatWord 71777214294589695, 3)]
def a13Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfffdfffcd3fdef0, 0xddfbef7775bf433, 0xdff7dbef])
  | 2 => BitVec.ofNat 152 (big [0xe20799772e8378f, 0xaafdf69e9ffdbcc, 0xbf9e74db])
  | 3 => BitVec.ofNat 152 (big [0xc8d74989fc2c3b6, 0x8ddc987cf1568fc, 0x6dbbbbf9])
  | 4 => BitVec.ofNat 152 (big [0xcf5ab7580b40db2, 0x5d8f4673b10a8d3, 0xf37233c5])
  | 5 => BitVec.ofNat 152 (big [0x74a3473f3e7215f, 0x2b5757c9ab6cffd, 0x7d0aed9f])
  | _ => 0

def a13Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x44018041005840, 0x4000000000, 0x500])
  | 2 => BitVec.ofNat 152 (big [0xca0b81306a8268e, 0x1a10a24e18b1285, 0xd43a624c])
  | 3 => BitVec.ofNat 152 (big [0xc8356083cc283b4, 0xcec229b3a9d48b4, 0xf1c41a98])
  | 4 => BitVec.ofNat 152 (big [0x490ae5588b425b2, 0xb3b9a9fb937b655, 0x506ac8ff])
  | 5 => BitVec.ofNat 152 (big [0x21a0c38a0672113, 0x149649e9236cc49, 0x9c18043])
  | _ => 0

def a13Count (k : Nat) : Nat :=
  match k with
  | 3 => 3
  | 4 => 51
  | 5 => 83
  | 6 => 15
  | 7 => 1
  | _ => 0

def a13Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (28922+i*49) 49
  | 4 => field storageWord (29072+i*38) 38
  | 5 => field storageWord (31360+i*27) 27
  | 6 => field storageWord (36457+i*16) 16
  | 7 => field storageWord (38157+i*5) 5
  | _ => 0

def a13Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 3 3 (field storageWord (29069+(tag % 3)*1) 1) tag
  | 4 => hashRow 51 26 (field storageWord (31010+(tag % 26)*7) 7) tag
  | 5 => hashRow 83 42 (field storageWord (33601+(tag % 42)*8) 8) tag
  | 6 => hashRow 15 8 (field storageWord (36697+(tag % 8)*5) 5) tag
  | 7 => 0
  | _ => 0

def a13Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 31200 3 31356 1 31192 4 i
  | 5 => hintsAt storageWord 35191 7 35779 6 33937 33 i
  | 6 => hintsAt storageWord 37493 7 37605 6 36737 21 i
  | 7 => hintsAt storageWord 38177 3 38183 3 38162 3 i
  | _ => []

def a13 : Atlas := ⟨7,rawDecor 61 a13Pos a13Neg,repeatWord 18062525210034875040,a13Count,a13Rec,(fun _ _ => 0),a13Loc⟩
def a13Domains : Catalog := [(repeatWord 71777214294589695, 6), (repeatWord 6149008514797120170, 6), (repeatWord 17361393124654452495, 6), (repeatWord 18446462598732906495, 6), (repeatWord 281470681808895, 5), (repeatWord 6510615555426900570, 5), (repeatWord 6172840429334713770, 5), (repeatWord 6148914692668172970, 5), (repeatWord 17298308644996116495, 5), (repeatWord 17361641477348724495, 5), (repeatWord 18374966855153418495, 5)]
def a14Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x52de5bd4f728f43, 0xce93f8ff1afaf4a, 0x7bf3dfb7])
  | 2 => BitVec.ofNat 152 (big [0x9ced94d1d97e198, 0x182b7f7dcfc1cb5, 0xc4fbf453])
  | 3 => BitVec.ofNat 152 (big [0xa331772a90f5837, 0xf9f6f302bee62f6, 0xfcf4af69])
  | 4 => BitVec.ofNat 152 (big [0x710b25aae2cf26c, 0xb3cde7a6e56e5ef, 0xee378a7c])
  | 5 => BitVec.ofNat 152 (big [0x9ef3a9254e9249d, 0x742bdfbef9919dd, 0x1f7ef0a9])
  | _ => 0

def a14Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x810000500042, 0x10000021002808, 0x4a0000])
  | 2 => BitVec.ofNat 152 (big [0x15450211807c188, 0x800c4a2042cc434, 0x60943189])
  | 3 => BitVec.ofNat 152 (big [0x13446299034835, 0xa08309008910c6, 0xa510922a])
  | 4 => BitVec.ofNat 152 (big [0x5c01219642cb208, 0xd4b14801856c100, 0x8a56040])
  | 5 => BitVec.ofNat 152 (big [0xca82410e4a82415, 0x48e281d4a8110c1, 0x8021c244])
  | _ => 0

def a14Count (k : Nat) : Nat :=
  match k with
  | 4 => 16
  | 5 => 40
  | 6 => 12
  | 7 => 1
  | _ => 0

def a14Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (38198+i*38) 38
  | 5 => field storageWord (38886+i*27) 27
  | 6 => field storageWord (40892+i*16) 16
  | 7 => field storageWord (41438+i*5) 5
  | _ => 0

def a14Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 16 16 (field storageWord (38806+(tag % 16)*5) 5) tag
  | 5 => hashRow 40 40 (field storageWord (39966+(tag % 40)*7) 7) tag
  | 6 => hashRow 12 12 (field storageWord (41084+(tag % 12)*5) 5) tag
  | 7 => 0
  | _ => 0

def a14Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 40486 6 40732 4 40246 20 i
  | 6 => hintsAt storageWord 41184 6 41262 4 41144 4 i
  | 7 => hintsAt storageWord 41451 2 41455 1 41443 4 i
  | _ => []

def a14 : Atlas := ⟨7,rawDecor 61 a14Pos a14Neg,repeatWord 18445331179787430560,a14Count,a14Rec,(fun _ _ => 0),a14Loc⟩
def a14Domains : Catalog := [(repeatWord 1085102592571150095, 5), (repeatWord 71777214294589695, 5), (repeatWord 281470681808895, 5), (repeatWord 4294967295, 5), (repeatWord 6510615555426900570, 5), (repeatWord 6172840429334713770, 5), (repeatWord 6149008514797120170, 5), (repeatWord 6148914692668172970, 5), (repeatWord 252645135, 4), (repeatWord 1095216660735, 4)]
def a15Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xbeffbfffff77f7d, 0xffffff7ffffd7fe, 0xffffef7f])
  | 2 => BitVec.ofNat 152 (big [0xc7e4f4bb50eb28f, 0xaac0feb2e406b6f, 0xe9b65cd6])
  | 3 => BitVec.ofNat 152 (big [0x6f23f54ed3a86da, 0xccce80921afaae1, 0xd498bfd3])
  | 4 => BitVec.ofNat 152 (big [0xd956cb4b719999b, 0x1794e3e4c5dbe59, 0x78f2dfe8])
  | 5 => BitVec.ofNat 152 (big [0xe199e3404ead8b6, 0x5f6dc8efb943fef, 0xb20f9d96])
  | _ => 0

def a15Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x504000044140, 0x4000000011100, 0x800000])
  | 2 => BitVec.ofNat 152 (big [0x9560d0bd14a328f, 0x80aa8766ad08a66, 0x2330993e])
  | 3 => BitVec.ofNat 152 (big [0x6f483256d3a861a, 0x1f39a69008e82f3, 0xe11d8535])
  | 4 => BitVec.ofNat 152 (big [0xf852db2bc999899, 0x43813158614a058, 0x910a6ff1])
  | 5 => BitVec.ofNat 152 (big [0x2c88abc14e298b6, 0xf2a54506b922e0b, 0xa474c201])
  | _ => 0

def a15Count (k : Nat) : Nat :=
  match k with
  | 4 => 96
  | 5 => 128
  | 6 => 20
  | 7 => 1
  | _ => 0

def a15Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (41457+i*38) 38
  | 5 => field storageWord (48327+i*27) 27
  | 6 => field storageWord (61104+i*16) 16
  | 7 => field storageWord (64414+i*5) 5
  | _ => 0

def a15Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 96 96 (field storageWord (45105+(tag % 96)*8) 8) tag
  | 5 => hashRow 128 128 (field storageWord (51783+(tag % 128)*8) 8) tag
  | 6 => hashRow 20 20 (field storageWord (61424+(tag % 20)*6) 6) tag
  | 7 => 0
  | _ => 0

def a15Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 47457 6 48039 6 45873 33 i
  | 5 => hintsAt storageWord 57255 9 58416 8 52807 32 i
  | 6 => hintsAt storageWord 63014 8 63182 7 61544 21 i
  | 7 => hintsAt storageWord 64459 4 64467 4 64419 4 i
  | _ => []

def a15 : Atlas := ⟨7,rawDecor 62 a15Pos a15Neg,repeatWord 18216159772788182208,a15Count,a15Rec,(fun _ _ => 0),a15Loc⟩
def a15Domains : Catalog := [(repeatWord 4340410370284600380, 6), (repeatWord 3732415143318664140, 6), (repeatWord 3689517697150995660, 6), (repeatWord 3689348817318890700, 6), (repeatWord 17298308644996116495, 6), (repeatWord 17361393124654452495, 6), (repeatWord 17361641477348724495, 6), (repeatWord 18374687579166474495, 6), (repeatWord 18374966855153418495, 6), (repeatWord 18446462598732906495, 6)]
def a16Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdf7dfffffff5df2, 0xf5eff7b9fffa33f, 0xffffd9ff])
  | 1 => BitVec.ofNat 152 (big [0x2ccf4add13fa29d, 0xbe78286635bffd5, 0x66b96f6f])
  | 2 => BitVec.ofNat 152 (big [0x1ad54279c696cbc, 0xf0a85ca7dec3947, 0x83caf537])
  | 3 => BitVec.ofNat 152 (big [0xe6929c2f632be6f, 0x3fb57ef77cddff9, 0x73efaef8])
  | 4 => BitVec.ofNat 152 (big [0x7dab7fa09ccf70d, 0x7af3af4f8bfddcf, 0xffdaf7ce])
  | _ => 0

def a16Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x609b1488d50812, 0x20000000c00034, 0x784030])
  | 1 => BitVec.ofNat 152 (big [0x2d408b9533ea294, 0xd66784a605963c6, 0x95080c58])
  | 2 => BitVec.ofNat 152 (big [0x504562bb4696cac, 0x655cee8ad8c5fa3, 0xb32034d])
  | 3 => BitVec.ofNat 152 (big [0xd0d20c02622166d, 0x311531a1304cf41, 0x2580a045])
  | 4 => BitVec.ofNat 152 (big [0xd98040b0508f509, 0x81a8f74d02b948b, 0xd2840a0e])
  | _ => 0

def a16Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a16Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (64507+i*5) 5
  | _ => 0

def a16Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a16Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 64513 1 64515 1 64512 1 i
  | _ => []

def a16 : Atlas := ⟨6,rawDecor 31 a16Pos a16Neg,repeatWord 17197745597804358272,a16Count,a16Rec,(fun _ _ => 0),a16Loc⟩
def a16Domains : Catalog := [(repeatWord 17361641481138401520, 6)]
def a17Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x6612c9d8cb5e138, 0x1401225601d03a5, 0x9544c050])
  | 2 => BitVec.ofNat 152 (big [0x6a8fcbe7c73635b, 0x57fbc0fea7d8293, 0x9127c168])
  | 3 => BitVec.ofNat 152 (big [0x9fd3ec3b5c794b9, 0x89ff76d931cbd3f, 0xfcfdfe1f])
  | 4 => BitVec.ofNat 152 (big [0x3c3d9e1c2ad8b76, 0xff9dff76eefe16d, 0x36d625f5])
  | 5 => BitVec.ofNat 152 (big [0x7a36ebc3c38fba9, 0x57615ee75370aa2, 0xa71dd5d6])
  | _ => 0

def a17Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x5777f99a4afe5fc, 0xdbf7f3dec6dfbbd, 0xff26b7be])
  | 2 => BitVec.ofNat 152 (big [0xa905c0ef073225b, 0xa0128162b128351, 0x441869c3])
  | 3 => BitVec.ofNat 152 (big [0x5543a08a48304a8, 0x20c2980042000, 0x2000200a])
  | 4 => BitVec.ofNat 152 (big [0x14180002c8154, 0xc9831144468838c, 0x50096a0])
  | 5 => BitVec.ofNat 152 (big [0x7e601a24c18dba1, 0x2f4074801b70ca6, 0x894982c])
  | _ => 0

def a17Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a17Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (64516+i*5) 5
  | _ => 0

def a17Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a17Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 64522 1 64524 1 64521 1 i
  | _ => []

def a17 : Atlas := ⟨6,rawDecor 62 a17Pos a17Neg,repeatWord 18443352909253128960,a17Count,a17Rec,(fun _ _ => 0),a17Loc⟩
def a17Domains : Catalog := [(repeatWord 17361641481138401520, 6)]
def a18Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf7df77fe1fbdc3f, 0xf7feffffffcffd5, 0x93ffebf7])
  | 1 => BitVec.ofNat 152 (big [0x6ce299fde6ebfd9, 0x7bb1df7f697e67b, 0xeeebd6f8])
  | 2 => BitVec.ofNat 152 (big [0x7d769a31e0f73f5, 0x88a598d67774d7a, 0xfd8d3eda])
  | 3 => BitVec.ofNat 152 (big [0xbbfd7f4f995c57e, 0xd5fef6ee96af9d5, 0xb3b5ff0f])
  | 5 => BitVec.ofNat 152 (big [0xd8f4cd81ef46fc5, 0xae6dcd63edfc72f, 0x7ffb946a])
  | _ => 0

def a18Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x620103521a35809, 0x4c800331a404d16, 0x8c37008b])
  | 1 => BitVec.ofNat 152 (big [0x24a8482ee6cb658, 0x15402c6e5848648, 0x15c08c24])
  | 2 => BitVec.ofNat 152 (big [0xd947903880b43f5, 0xd09ab0c1d1249fa, 0x4b7b9209])
  | 3 => BitVec.ofNat 152 (big [0x99d8f8292148576, 0x273284e1a82089, 0x73088a20])
  | 5 => BitVec.ofNat 152 (big [0x8374e5912d46d85, 0xbafca0bad7c803, 0x12ac03c9])
  | _ => 0

def a18Count (k : Nat) : Nat :=
  match k with
  | 4 => 2
  | 5 => 6
  | 6 => 1
  | _ => 0

def a18Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (64525+i*27) 27
  | 5 => field storageWord (64583+i*16) 16
  | 6 => field storageWord (64863+i*5) 5
  | _ => 0

def a18Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 2 2 (field storageWord (64579+(tag % 2)*2) 2) tag
  | 5 => hashRow 6 6 (field storageWord (64679+(tag % 6)*4) 4) tag
  | 6 => 0
  | _ => 0

def a18Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 64808 4 64836 3 64703 21 i
  | 6 => hintsAt storageWord 64880 3 64886 2 64868 3 i
  | _ => []

def a18 : Atlas := ⟨6,rawDecor 47 a18Pos a18Neg,repeatWord 16918030147792185984,a18Count,a18Rec,(fun _ _ => 0),a18Loc⟩
def a18Domains : Catalog := [(repeatWord 14757395258967641292, 5), (repeatWord 71777214294589695, 5), (repeatWord 6172840429334713770, 5), (repeatWord 17361641481138401520, 4), (repeatWord 18446744069414584320, 4)]
def a19Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xeffffff7ffeedfd, 0xffffd7fefcc7fdf, 0xfbfbffee])
  | 2 => BitVec.ofNat 152 (big [0x7f9f5c9bdbb1ffa, 0x6ff67b7dfffd7bf, 0xde9edbd7])
  | 3 => BitVec.ofNat 152 (big [0xfcfefbeef6dfbc7, 0xfbbfbebb5f3b8e4, 0xefef2cff])
  | 4 => BitVec.ofNat 152 (big [0xbe7cb3eef5ff2e7, 0xfb4baefff37aeef, 0xff7f3dfb])
  | 5 => BitVec.ofNat 152 (big [0x77bbfc19db3df3b, 0x17ff7977affff7b, 0x9d97ffdf])
  | _ => 0

def a19Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xe12c3f1633645d5, 0xd500b80dca41d93, 0x8822682])
  | 2 => BitVec.ofNat 152 (big [0xe71a41d14990bfa, 0xb2a518b1b1b44ac, 0x6352b008])
  | 3 => BitVec.ofNat 152 (big [0xbdb0d6ea8e9fb44, 0x569a4ac4b683020, 0x910810f8])
  | 4 => BitVec.ofNat 152 (big [0x85ca178f1eb2a3, 0x9b33151481c34d, 0x236dbb00])
  | 5 => BitVec.ofNat 152 (big [0x16831e20fa3dc2b, 0x4071e1667a2eb42, 0x7228086f])
  | _ => 0

def a19Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a19Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (64894+i*5) 5
  | _ => 0

def a19Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a19Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 64900 1 64902 1 64899 1 i
  | _ => []

def a19 : Atlas := ⟨5,rawDecor 62 a19Pos a19Neg,repeatWord 18212768827375091712,a19Count,a19Rec,(fun _ _ => 0),a19Loc⟩
def a19Domains : Catalog := [(repeatWord 17361641481138401520, 5)]
def a20Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfebfffd7fff6bfb, 0xffffefffefffbff, 0x7ffffbff])
  | 2 => BitVec.ofNat 152 (big [0x99edb96c0ccf475, 0xabcb3e84727b786, 0x8f8f2e9a])
  | 3 => BitVec.ofNat 152 (big [0x57cc9dba5aabee7, 0xe65edcebfc9ffaf, 0xeff6af7b])
  | 4 => BitVec.ofNat 152 (big [0xadf7727df55d73e, 0xdbf1fbd7937d5da, 0xd7dfd78d])
  | 5 => BitVec.ofNat 152 (big [0x3f76ddbcb21f69d, 0xecabf0c91068ca6, 0xdd839c58])
  | _ => 0

def a20Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xca0dc00734a6188, 0x1414900401003c, 0x40321408])
  | 2 => BitVec.ofNat 152 (big [0x98eed1630ccf075, 0x14a609762a59e22, 0x4ba69491])
  | 3 => BitVec.ofNat 152 (big [0x25001f784209e63, 0xbe84044a2c07b83, 0x3cc8ca86])
  | 4 => BitVec.ofNat 152 (big [0x24e236488158636, 0xda021697b42c1c0, 0x2b09c961])
  | 5 => BitVec.ofNat 152 (big [0xf11e4c94121769d, 0xbaeabc5106cef7, 0xf6704d4a])
  | _ => 0

def a20Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a20Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (64903+i*5) 5
  | _ => 0

def a20Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a20Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 64909 1 64911 1 64908 1 i
  | _ => []

def a20 : Atlas := ⟨5,rawDecor 61 a20Pos a20Neg,repeatWord 18062436175362828800,a20Count,a20Rec,(fun _ _ => 0),a20Loc⟩
def a20Domains : Catalog := [(repeatWord 17361641481138401520, 5)]
def a21Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf3937c5dde3439c, 0xf7cbaefffaefdc4, 0x336ffbf3])
  | 1 => BitVec.ofNat 152 (big [0xaced9beee12b6e3, 0xbebe6921f50a86f, 0xf7b0341f])
  | 2 => BitVec.ofNat 152 (big [0x230f723e32c2e6d, 0xd23c55f93d9c67a, 0x9dc255ef])
  | 3 => BitVec.ofNat 152 (big [0x3cfaa3b321c9937, 0xfd1f761151baf37, 0xcdb506ba])
  | 5 => BitVec.ofNat 152 (big [0xaaf0f2d4ccedca, 0x8ff7d6d6db1e1a, 0x4b43e20f])
  | _ => 0

def a21Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x0])
  | 1 => BitVec.ofNat 152 (big [0xa845902ad0296e0, 0x5a091a046103880, 0x8e2085a])
  | 2 => BitVec.ofNat 152 (big [0x3008e00cb682e2d, 0xc96c88238ddc443, 0x89417290])
  | 3 => BitVec.ofNat 152 (big [0x54a2021009c0117, 0x430251b102c727, 0x208c700])
  | 5 => BitVec.ofNat 152 (big [0x86cb4b250c4e9ca, 0x603d1980281918, 0xa3bf3c83])
  | _ => 0

def a21Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a21Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (64912+i*5) 5
  | _ => 0

def a21Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a21Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 64918 1 64920 1 64917 1 i
  | _ => []

def a21 : Atlas := ⟨5,rawDecor 47 a21Pos a21Neg,repeatWord 18368774315163971242,a21Count,a21Rec,(fun _ _ => 0),a21Loc⟩
def a21Domains : Catalog := [(repeatWord 6148914691236517205, 5)]
def a22Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf3ee5f4cdf9cfa0, 0xfade1b7bbddbb5b, 0xc3d4b7fe])
  | 1 => BitVec.ofNat 152 (big [0xaee52ef2647275f, 0xaff9ffae7b747b4, 0xbe1f588f])
  | 2 => BitVec.ofNat 152 (big [0x2633c153b73b957, 0x8845e5e723c74d7, 0x9bb7f95])
  | 3 => BitVec.ofNat 152 (big [0xe81ae6bd307faba, 0x556ba2c2ddb22ee, 0x3ce40339])
  | 4 => BitVec.ofNat 152 (big [0xb9d1f1b58fc348f, 0xe56faf79d17bc65, 0xff2cacc3])
  | 5 => BitVec.ofNat 152 (big [0xc71da98371a5edd, 0x8b9d74cdeec4da8, 0x597f585e])
  | _ => 0

def a22Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x2680c00c988920, 0x808600583000040, 0x31004f4])
  | 1 => BitVec.ofNat 152 (big [0xb4c52660447275b, 0x3731be365360a95, 0xac57188b])
  | 2 => BitVec.ofNat 152 (big [0x2633c153b71a816, 0xccc545e025c56d3, 0xa8294371])
  | 3 => BitVec.ofNat 152 (big [0x4812629d3077290, 0x50491002cfbb236, 0x60e44208])
  | 4 => BitVec.ofNat 152 (big [0xf991d1b4060148f, 0x6458a305005f821, 0xdc092200])
  | 5 => BitVec.ofNat 152 (big [0xc30ca98331a5ecd, 0xa99830cd8e24d0a, 0x55445846])
  | _ => 0

def a22Count (k : Nat) : Nat :=
  match k with
  | 6 => 7
  | 7 => 50
  | 8 => 103
  | 9 => 18
  | 10 => 1
  | _ => 0

def a22Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (64921+i*50) 50
  | 7 => field storageWord (66102+i*39) 39
  | 8 => field storageWord (77560+i*28) 28
  | 9 => field storageWord (97572+i*17) 17
  | 10 => field storageWord (100253+i*6) 6
  | _ => 0

def a22Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => hashRow 7 4 (field storageWord (65271+(tag % 4)*3) 3) tag
  | 7 => hashRow 50 25 (field storageWord (68052+(tag % 25)*7) 7) tag
  | 8 => hashRow 103 52 (field storageWord (80444+(tag % 52)*8) 8) tag
  | 9 => hashRow 18 18 (field storageWord (97878+(tag % 18)*6) 6) tag
  | 10 => 0
  | _ => 0

def a22Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 65998 5 66038 4 65283 55 i
  | 7 => hintsAt storageWord 75112 8 75520 8 68227 45 i
  | 8 => hintsAt storageWord 90331 10 91371 9 80860 33 i
  | 9 => hintsAt storageWord 99267 8 99419 6 97986 21 i
  | 10 => hintsAt storageWord 100271 2 100275 2 100259 4 i
  | _ => []

def a22 : Atlas := ⟨10,rawDecor 63 a22Pos a22Neg,repeatWord 18368752178902510208,a22Count,a22Rec,(fun _ _ => 0),a22Loc⟩
def a22Domains : Catalog := [(repeatWord 17361641481138401520, 9), (repeatWord 18446744069414584320, 9), (repeatWord 6510615555426900570, 8), (repeatWord 6172840429334713770, 8), (repeatWord 6149008514797120170, 8), (repeatWord 6148914692668172970, 8), (repeatWord 3732415143318664140, 8), (repeatWord 3689517697150995660, 8), (repeatWord 18374687579166474495, 8), (repeatWord 14757395258967641292, 8), (repeatWord 11068046444225730969, 8), (repeatWord 1085102592571150095, 7), (repeatWord 4294967295, 7), (repeatWord 7378697629483820646, 7), (repeatWord 71777214294589695, 7), (repeatWord 281470681808895, 7), (repeatWord 6148914691236517205, 6), (repeatWord 3689348814741910323, 6), (repeatWord 18374966859414961920, 6), (repeatWord 18446462603027742720, 6), (repeatWord 6124988953138320640, 5), (repeatWord 6148820867675914240, 5), (repeatWord 57421771435671756, 5), (repeatWord 225176545447116, 5), (repeatWord 1095216660735, 5), (repeatWord 876173328588, 4)]
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
theorem a1S4P0 : segment (checkRow a1 a1Domains a1Hints 4) 0 12 = true := by decide +kernel
theorem a1S4 (j : Nat) (hj : j < 12) : (checkRow a1 a1Domains a1Hints 4) j = true := by
  exact segmentRange a1S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S5P0 : segment (checkRow a1 a1Domains a1Hints 5) 0 1 = true := by decide +kernel
theorem a1S5 (j : Nat) (hj : j < 1) : (checkRow a1 a1Domains a1Hints 5) j = true := by
  exact segmentRange a1S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Complete : Complete a1 a1Domains a1Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a1S4 j hj
  · exact a1S5 j hj
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
theorem a4S4P0 : segment (checkRow a4 a4Domains a4Hints 4) 0 1 = true := by decide +kernel
theorem a4S4 (j : Nat) (hj : j < 1) : (checkRow a4 a4Domains a4Hints 4) j = true := by
  exact segmentRange a4S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Complete : Complete a4 a4Domains a4Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a4S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S4P0 : segment (checkRow a5 a5Domains a5Hints 4) 0 1 = true := by decide +kernel
theorem a5S4 (j : Nat) (hj : j < 1) : (checkRow a5 a5Domains a5Hints 4) j = true := by
  exact segmentRange a5S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Complete : Complete a5 a5Domains a5Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a5S4 j hj
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
theorem a7S3P0 : segment (checkRow a7 a7Domains a7Hints 3) 0 1 = true := by decide +kernel
theorem a7S3 (j : Nat) (hj : j < 1) : (checkRow a7 a7Domains a7Hints 3) j = true := by
  exact segmentRange a7S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Complete : Complete a7 a7Domains a7Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a7S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S4P0 : segment (checkRow a8 a8Domains a8Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S4P1 : segment (checkRow a8 a8Domains a8Hints 4) 16 7 = true := by decide +kernel
theorem a8S4 (j : Nat) (hj : j < 23) : (checkRow a8 a8Domains a8Hints 4) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a8S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a8S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P0 : segment (checkRow a8 a8Domains a8Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P1 : segment (checkRow a8 a8Domains a8Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P2 : segment (checkRow a8 a8Domains a8Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P3 : segment (checkRow a8 a8Domains a8Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P4 : segment (checkRow a8 a8Domains a8Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P5 : segment (checkRow a8 a8Domains a8Hints 5) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P6 : segment (checkRow a8 a8Domains a8Hints 5) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P7 : segment (checkRow a8 a8Domains a8Hints 5) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P8 : segment (checkRow a8 a8Domains a8Hints 5) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S5P9 : segment (checkRow a8 a8Domains a8Hints 5) 144 2 = true := by decide +kernel
theorem a8S5 (j : Nat) (hj : j < 146) : (checkRow a8 a8Domains a8Hints 5) j = true := by
  by_cases bound : j < 80
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a8S5P0 j (by omega) (by omega)
      ·
        exact segmentRange a8S5P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a8S5P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 64
        ·
          exact segmentRange a8S5P3 j (by omega) (by omega)
        ·
          exact segmentRange a8S5P4 j (by omega) (by omega)
  ·
    by_cases bound : j < 112
    ·
      by_cases bound : j < 96
      ·
        exact segmentRange a8S5P5 j (by omega) (by omega)
      ·
        exact segmentRange a8S5P6 j (by omega) (by omega)
    ·
      by_cases bound : j < 128
      ·
        exact segmentRange a8S5P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 144
        ·
          exact segmentRange a8S5P8 j (by omega) (by omega)
        ·
          exact segmentRange a8S5P9 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P0 : segment (checkRow a8 a8Domains a8Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P1 : segment (checkRow a8 a8Domains a8Hints 6) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P2 : segment (checkRow a8 a8Domains a8Hints 6) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P3 : segment (checkRow a8 a8Domains a8Hints 6) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P4 : segment (checkRow a8 a8Domains a8Hints 6) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P5 : segment (checkRow a8 a8Domains a8Hints 6) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P6 : segment (checkRow a8 a8Domains a8Hints 6) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P7 : segment (checkRow a8 a8Domains a8Hints 6) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P8 : segment (checkRow a8 a8Domains a8Hints 6) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S6P9 : segment (checkRow a8 a8Domains a8Hints 6) 144 14 = true := by decide +kernel
theorem a8S6 (j : Nat) (hj : j < 158) : (checkRow a8 a8Domains a8Hints 6) j = true := by
  by_cases bound : j < 80
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a8S6P0 j (by omega) (by omega)
      ·
        exact segmentRange a8S6P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a8S6P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 64
        ·
          exact segmentRange a8S6P3 j (by omega) (by omega)
        ·
          exact segmentRange a8S6P4 j (by omega) (by omega)
  ·
    by_cases bound : j < 112
    ·
      by_cases bound : j < 96
      ·
        exact segmentRange a8S6P5 j (by omega) (by omega)
      ·
        exact segmentRange a8S6P6 j (by omega) (by omega)
    ·
      by_cases bound : j < 128
      ·
        exact segmentRange a8S6P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 144
        ·
          exact segmentRange a8S6P8 j (by omega) (by omega)
        ·
          exact segmentRange a8S6P9 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S7P0 : segment (checkRow a8 a8Domains a8Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S7P1 : segment (checkRow a8 a8Domains a8Hints 7) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S7P2 : segment (checkRow a8 a8Domains a8Hints 7) 32 2 = true := by decide +kernel
theorem a8S7 (j : Nat) (hj : j < 34) : (checkRow a8 a8Domains a8Hints 7) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a8S7P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 32
    ·
      exact segmentRange a8S7P1 j (by omega) (by omega)
    ·
      exact segmentRange a8S7P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S8P0 : segment (checkRow a8 a8Domains a8Hints 8) 0 1 = true := by decide +kernel
theorem a8S8 (j : Nat) (hj : j < 1) : (checkRow a8 a8Domains a8Hints 8) j = true := by
  exact segmentRange a8S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Complete : Complete a8 a8Domains a8Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a8S4 j hj
  · exact a8S5 j hj
  · exact a8S6 j hj
  · exact a8S7 j hj
  · exact a8S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S6P0 : segment (checkRow a9 a9Domains a9Hints 6) 0 1 = true := by decide +kernel
theorem a9S6 (j : Nat) (hj : j < 1) : (checkRow a9 a9Domains a9Hints 6) j = true := by
  exact segmentRange a9S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S7P0 : segment (checkRow a9 a9Domains a9Hints 7) 0 1 = true := by decide +kernel
theorem a9S7 (j : Nat) (hj : j < 1) : (checkRow a9 a9Domains a9Hints 7) j = true := by
  exact segmentRange a9S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Complete : Complete a9 a9Domains a9Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a9S6 j hj
  · exact a9S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S7P0 : segment (checkRow a10 a10Domains a10Hints 7) 0 1 = true := by decide +kernel
theorem a10S7 (j : Nat) (hj : j < 1) : (checkRow a10 a10Domains a10Hints 7) j = true := by
  exact segmentRange a10S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Complete : Complete a10 a10Domains a10Hints := by
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
  · exact a10S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S3P0 : segment (checkRow a11 a11Domains a11Hints 3) 0 15 = true := by decide +kernel
theorem a11S3 (j : Nat) (hj : j < 15) : (checkRow a11 a11Domains a11Hints 3) j = true := by
  exact segmentRange a11S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S4P0 : segment (checkRow a11 a11Domains a11Hints 4) 0 12 = true := by decide +kernel
theorem a11S4 (j : Nat) (hj : j < 12) : (checkRow a11 a11Domains a11Hints 4) j = true := by
  exact segmentRange a11S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S5P0 : segment (checkRow a11 a11Domains a11Hints 5) 0 1 = true := by decide +kernel
theorem a11S5 (j : Nat) (hj : j < 1) : (checkRow a11 a11Domains a11Hints 5) j = true := by
  exact segmentRange a11S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Complete : Complete a11 a11Domains a11Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a11S3 j hj
  · exact a11S4 j hj
  · exact a11S5 j hj
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
theorem a13S3P0 : segment (checkRow a13 a13Domains a13Hints 3) 0 3 = true := by decide +kernel
theorem a13S3 (j : Nat) (hj : j < 3) : (checkRow a13 a13Domains a13Hints 3) j = true := by
  exact segmentRange a13S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S4P0 : segment (checkRow a13 a13Domains a13Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S4P1 : segment (checkRow a13 a13Domains a13Hints 4) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S4P2 : segment (checkRow a13 a13Domains a13Hints 4) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S4P3 : segment (checkRow a13 a13Domains a13Hints 4) 48 3 = true := by decide +kernel
theorem a13S4 (j : Nat) (hj : j < 51) : (checkRow a13 a13Domains a13Hints 4) j = true := by
  by_cases bound : j < 32
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a13S4P0 j (by omega) (by omega)
    ·
      exact segmentRange a13S4P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 48
    ·
      exact segmentRange a13S4P2 j (by omega) (by omega)
    ·
      exact segmentRange a13S4P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S5P0 : segment (checkRow a13 a13Domains a13Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S5P1 : segment (checkRow a13 a13Domains a13Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S5P2 : segment (checkRow a13 a13Domains a13Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S5P3 : segment (checkRow a13 a13Domains a13Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S5P4 : segment (checkRow a13 a13Domains a13Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S5P5 : segment (checkRow a13 a13Domains a13Hints 5) 80 3 = true := by decide +kernel
theorem a13S5 (j : Nat) (hj : j < 83) : (checkRow a13 a13Domains a13Hints 5) j = true := by
  by_cases bound : j < 48
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a13S5P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 32
      ·
        exact segmentRange a13S5P1 j (by omega) (by omega)
      ·
        exact segmentRange a13S5P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 64
    ·
      exact segmentRange a13S5P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a13S5P4 j (by omega) (by omega)
      ·
        exact segmentRange a13S5P5 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S6P0 : segment (checkRow a13 a13Domains a13Hints 6) 0 15 = true := by decide +kernel
theorem a13S6 (j : Nat) (hj : j < 15) : (checkRow a13 a13Domains a13Hints 6) j = true := by
  exact segmentRange a13S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S7P0 : segment (checkRow a13 a13Domains a13Hints 7) 0 1 = true := by decide +kernel
theorem a13S7 (j : Nat) (hj : j < 1) : (checkRow a13 a13Domains a13Hints 7) j = true := by
  exact segmentRange a13S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Complete : Complete a13 a13Domains a13Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a13S3 j hj
  · exact a13S4 j hj
  · exact a13S5 j hj
  · exact a13S6 j hj
  · exact a13S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S4P0 : segment (checkRow a14 a14Domains a14Hints 4) 0 16 = true := by decide +kernel
theorem a14S4 (j : Nat) (hj : j < 16) : (checkRow a14 a14Domains a14Hints 4) j = true := by
  exact segmentRange a14S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P0 : segment (checkRow a14 a14Domains a14Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P1 : segment (checkRow a14 a14Domains a14Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S5P2 : segment (checkRow a14 a14Domains a14Hints 5) 32 8 = true := by decide +kernel
theorem a14S5 (j : Nat) (hj : j < 40) : (checkRow a14 a14Domains a14Hints 5) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a14S5P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 32
    ·
      exact segmentRange a14S5P1 j (by omega) (by omega)
    ·
      exact segmentRange a14S5P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P0 : segment (checkRow a14 a14Domains a14Hints 6) 0 12 = true := by decide +kernel
theorem a14S6 (j : Nat) (hj : j < 12) : (checkRow a14 a14Domains a14Hints 6) j = true := by
  exact segmentRange a14S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S7P0 : segment (checkRow a14 a14Domains a14Hints 7) 0 1 = true := by decide +kernel
theorem a14S7 (j : Nat) (hj : j < 1) : (checkRow a14 a14Domains a14Hints 7) j = true := by
  exact segmentRange a14S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Complete : Complete a14 a14Domains a14Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a14S4 j hj
  · exact a14S5 j hj
  · exact a14S6 j hj
  · exact a14S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P0 : segment (checkRow a15 a15Domains a15Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P1 : segment (checkRow a15 a15Domains a15Hints 4) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P2 : segment (checkRow a15 a15Domains a15Hints 4) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P3 : segment (checkRow a15 a15Domains a15Hints 4) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P4 : segment (checkRow a15 a15Domains a15Hints 4) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S4P5 : segment (checkRow a15 a15Domains a15Hints 4) 80 16 = true := by decide +kernel
theorem a15S4 (j : Nat) (hj : j < 96) : (checkRow a15 a15Domains a15Hints 4) j = true := by
  by_cases bound : j < 48
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a15S4P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 32
      ·
        exact segmentRange a15S4P1 j (by omega) (by omega)
      ·
        exact segmentRange a15S4P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 64
    ·
      exact segmentRange a15S4P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a15S4P4 j (by omega) (by omega)
      ·
        exact segmentRange a15S4P5 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P0 : segment (checkRow a15 a15Domains a15Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P1 : segment (checkRow a15 a15Domains a15Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P2 : segment (checkRow a15 a15Domains a15Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P3 : segment (checkRow a15 a15Domains a15Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P4 : segment (checkRow a15 a15Domains a15Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P5 : segment (checkRow a15 a15Domains a15Hints 5) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P6 : segment (checkRow a15 a15Domains a15Hints 5) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S5P7 : segment (checkRow a15 a15Domains a15Hints 5) 112 16 = true := by decide +kernel
theorem a15S5 (j : Nat) (hj : j < 128) : (checkRow a15 a15Domains a15Hints 5) j = true := by
  by_cases bound : j < 64
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a15S5P0 j (by omega) (by omega)
      ·
        exact segmentRange a15S5P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a15S5P2 j (by omega) (by omega)
      ·
        exact segmentRange a15S5P3 j (by omega) (by omega)
  ·
    by_cases bound : j < 96
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a15S5P4 j (by omega) (by omega)
      ·
        exact segmentRange a15S5P5 j (by omega) (by omega)
    ·
      by_cases bound : j < 112
      ·
        exact segmentRange a15S5P6 j (by omega) (by omega)
      ·
        exact segmentRange a15S5P7 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P0 : segment (checkRow a15 a15Domains a15Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P1 : segment (checkRow a15 a15Domains a15Hints 6) 16 4 = true := by decide +kernel
theorem a15S6 (j : Nat) (hj : j < 20) : (checkRow a15 a15Domains a15Hints 6) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a15S6P0 j (by omega) (by omega)
  ·
    exact segmentRange a15S6P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S7P0 : segment (checkRow a15 a15Domains a15Hints 7) 0 1 = true := by decide +kernel
theorem a15S7 (j : Nat) (hj : j < 1) : (checkRow a15 a15Domains a15Hints 7) j = true := by
  exact segmentRange a15S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Complete : Complete a15 a15Domains a15Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a15S4 j hj
  · exact a15S5 j hj
  · exact a15S6 j hj
  · exact a15S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P0 : segment (checkRow a16 a16Domains a16Hints 6) 0 1 = true := by decide +kernel
theorem a16S6 (j : Nat) (hj : j < 1) : (checkRow a16 a16Domains a16Hints 6) j = true := by
  exact segmentRange a16S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Complete : Complete a16 a16Domains a16Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a16S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P0 : segment (checkRow a17 a17Domains a17Hints 6) 0 1 = true := by decide +kernel
theorem a17S6 (j : Nat) (hj : j < 1) : (checkRow a17 a17Domains a17Hints 6) j = true := by
  exact segmentRange a17S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Complete : Complete a17 a17Domains a17Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a17S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S4P0 : segment (checkRow a18 a18Domains a18Hints 4) 0 2 = true := by decide +kernel
theorem a18S4 (j : Nat) (hj : j < 2) : (checkRow a18 a18Domains a18Hints 4) j = true := by
  exact segmentRange a18S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P0 : segment (checkRow a18 a18Domains a18Hints 5) 0 6 = true := by decide +kernel
theorem a18S5 (j : Nat) (hj : j < 6) : (checkRow a18 a18Domains a18Hints 5) j = true := by
  exact segmentRange a18S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P0 : segment (checkRow a18 a18Domains a18Hints 6) 0 1 = true := by decide +kernel
theorem a18S6 (j : Nat) (hj : j < 1) : (checkRow a18 a18Domains a18Hints 6) j = true := by
  exact segmentRange a18S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Complete : Complete a18 a18Domains a18Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a18S4 j hj
  · exact a18S5 j hj
  · exact a18S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P0 : segment (checkRow a19 a19Domains a19Hints 5) 0 1 = true := by decide +kernel
theorem a19S5 (j : Nat) (hj : j < 1) : (checkRow a19 a19Domains a19Hints 5) j = true := by
  exact segmentRange a19S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19Complete : Complete a19 a19Domains a19Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a19S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20S5P0 : segment (checkRow a20 a20Domains a20Hints 5) 0 1 = true := by decide +kernel
theorem a20S5 (j : Nat) (hj : j < 1) : (checkRow a20 a20Domains a20Hints 5) j = true := by
  exact segmentRange a20S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20Complete : Complete a20 a20Domains a20Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a20S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21S5P0 : segment (checkRow a21 a21Domains a21Hints 5) 0 1 = true := by decide +kernel
theorem a21S5 (j : Nat) (hj : j < 1) : (checkRow a21 a21Domains a21Hints 5) j = true := by
  exact segmentRange a21S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21Complete : Complete a21 a21Domains a21Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a21S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S6P0 : segment (checkRow a22 a22Domains a22Hints 6) 0 7 = true := by decide +kernel
theorem a22S6 (j : Nat) (hj : j < 7) : (checkRow a22 a22Domains a22Hints 6) j = true := by
  exact segmentRange a22S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S7P0 : segment (checkRow a22 a22Domains a22Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S7P1 : segment (checkRow a22 a22Domains a22Hints 7) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S7P2 : segment (checkRow a22 a22Domains a22Hints 7) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S7P3 : segment (checkRow a22 a22Domains a22Hints 7) 48 2 = true := by decide +kernel
theorem a22S7 (j : Nat) (hj : j < 50) : (checkRow a22 a22Domains a22Hints 7) j = true := by
  by_cases bound : j < 32
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a22S7P0 j (by omega) (by omega)
    ·
      exact segmentRange a22S7P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 48
    ·
      exact segmentRange a22S7P2 j (by omega) (by omega)
    ·
      exact segmentRange a22S7P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S8P0 : segment (checkRow a22 a22Domains a22Hints 8) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S8P1 : segment (checkRow a22 a22Domains a22Hints 8) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S8P2 : segment (checkRow a22 a22Domains a22Hints 8) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S8P3 : segment (checkRow a22 a22Domains a22Hints 8) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S8P4 : segment (checkRow a22 a22Domains a22Hints 8) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S8P5 : segment (checkRow a22 a22Domains a22Hints 8) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S8P6 : segment (checkRow a22 a22Domains a22Hints 8) 96 7 = true := by decide +kernel
theorem a22S8 (j : Nat) (hj : j < 103) : (checkRow a22 a22Domains a22Hints 8) j = true := by
  by_cases bound : j < 48
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a22S8P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 32
      ·
        exact segmentRange a22S8P1 j (by omega) (by omega)
      ·
        exact segmentRange a22S8P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 80
    ·
      by_cases bound : j < 64
      ·
        exact segmentRange a22S8P3 j (by omega) (by omega)
      ·
        exact segmentRange a22S8P4 j (by omega) (by omega)
    ·
      by_cases bound : j < 96
      ·
        exact segmentRange a22S8P5 j (by omega) (by omega)
      ·
        exact segmentRange a22S8P6 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S9P0 : segment (checkRow a22 a22Domains a22Hints 9) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S9P1 : segment (checkRow a22 a22Domains a22Hints 9) 16 2 = true := by decide +kernel
theorem a22S9 (j : Nat) (hj : j < 18) : (checkRow a22 a22Domains a22Hints 9) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a22S9P0 j (by omega) (by omega)
  ·
    exact segmentRange a22S9P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S10P0 : segment (checkRow a22 a22Domains a22Hints 10) 0 1 = true := by decide +kernel
theorem a22S10 (j : Nat) (hj : j < 1) : (checkRow a22 a22Domains a22Hints 10) j = true := by
  exact segmentRange a22S10P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22Complete : Complete a22 a22Domains a22Hints := by
  intro k hk j hj
  change k ≤ 10 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a22S6 j hj
  · exact a22S7 j hj
  · exact a22S8 j hj
  · exact a22S9 j hj
  · exact a22S10 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0Bound : Lower true (roots a0) (target a0) 4 := by
  have ready : Ready a0 a0Domains (asRow a0Pos) (asRow a0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a0
  exact frozen ready a0Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D0 : Slice true (roots a1) (target a1) (repeatWord 7378697629483820646) 4 :=
  signedSlice (ms := ([flipInput 3] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D1 : Slice true (roots a1) (target a1) (repeatWord 6172840429334713770) 4 :=
  signedSlice (ms := ([flipInput 1] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D2 : Slice true (roots a1) (target a1) (repeatWord 6149008514797120170) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D3 : Slice true (roots a1) (target a1) (repeatWord 14714328930390887475) 4 :=
  signedSlice (ms := ([swapRows 16, flipInput 0, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D4 : Slice true (roots a1) (target a1) (repeatWord 14757226376558555955) 4 :=
  signedSlice (ms := ([swapRows 16, flipInput 0, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 4 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D5 : Slice true (roots a1) (target a1) (repeatWord 18374687579166474495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, flipInput 0, flipInput 1] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Bound : Lower true (roots a1) (target a1) 6 := by
  have ready : Ready a1 a1Domains (asRow a1Pos) (asRow a1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a1D0 (safeCons a1D1 (safeCons a1D2 (safeCons a1D3 (safeCons a1D4 (safeCons a1D5 (safeNil a1))))))
  exact frozen ready a1Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Bound : Lower true (roots a2) (target a2) 3 := by
  have ready : Ready a2 a2Domains (asRow a2Pos) (asRow a2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a2
  exact frozen ready a2Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D0 : Slice true (roots a3) (target a3) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([flipInput 3] ++ fixRows 4 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D1 : Slice true (roots a3) (target a3) (repeatWord 4340410370284600380) 4 :=
  signedSlice (ms := ([swapRows 33, flipInput 2, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D2 : Slice true (roots a3) (target a3) (repeatWord 71777214294589695) 3 :=
  signedSlice (ms := ([swapRows 65, swapRows 67, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 8 0)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D3 : Slice true (roots a3) (target a3) (repeatWord 281470681808895) 3 :=
  signedSlice (ms := ([swapRows 65, swapRows 83, flipInput 1, flipInput 2] ++ fixRows 16 0)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Bound : Lower true (roots a3) (target a3) 6 := by
  have ready : Ready a3 a3Domains (asRow a3Pos) (asRow a3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a3D0 (safeCons a3D1 (safeCons a3D2 (safeCons a3D3 (safeNil a3))))
  exact frozen ready a3Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4D0 : Slice true (roots a4) (target a4) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 50, flipInput 1, flipInput 2] ++ fixRows 0 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Bound : Lower true (roots a4) (target a4) 5 := by
  have ready : Ready a4 a4Domains (asRow a4Pos) (asRow a4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a4D0 (safeNil a4)
  exact frozen ready a4Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 18, 26), (inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D0 : Slice true (roots a5) (target a5) (repeatWord 14757395258967641292) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 0 2)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Bound : Lower true (roots a5) (target a5) 5 := by
  have ready : Ready a5 a5Domains (asRow a5Pos) (asRow a5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a5D0 (safeNil a5)
  exact frozen ready a5Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 56, 58), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D0 : Slice true (roots a6) (target a6) (repeatWord 17361641481138401520) 4 :=
  signedSlice (ms := ([swapRows 84, flipInput 1, flipInput 3] ++ fixRows 0 4)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Bound : Lower true (roots a6) (target a6) 5 := by
  have ready : Ready a6 a6Domains (asRow a6Pos) (asRow a6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a6D0 (safeNil a6)
  exact frozen ready a6Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 6, 14), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Bound : Lower true (roots a7) (target a7) 4 := by
  have ready : Ready a7 a7Domains (asRow a7Pos) (asRow a7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a7
  exact frozen ready a7Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D0 : Slice true (roots a8) (target a8) (repeatWord 1085102592571150095) 6 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D1 : Slice true (roots a8) (target a8) (repeatWord 7378697629483820646) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D2 : Slice true (roots a8) (target a8) (repeatWord 11936128518282651045) 6 :=
  signedSlice (ms := ([swapRows 32] ++ fixRows 0 0 ++ identifyRows 0 2 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D3 : Slice true (roots a8) (target a8) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([] ++ fixRows 1 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D4 : Slice true (roots a8) (target a8) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, flipInput 0] ++ fixRows 2 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D5 : Slice true (roots a8) (target a8) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 84, flipInput 1] ++ fixRows 0 4)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D6 : Slice true (roots a8) (target a8) (repeatWord 18374966859414961920) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 50, swapRows 84, flipInput 0] ++ fixRows 0 8)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D7 : Slice true (roots a8) (target a8) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 50, swapRows 83, swapRows 84, flipInput 0] ++ fixRows 0 16)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D8 : Slice true (roots a8) (target a8) (repeatWord 14714328930390887475) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 49, swapRows 50, swapRows 83, flipInput 0, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D9 : Slice true (roots a8) (target a8) (repeatWord 14757226376558555955) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 49, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 2, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 4 false)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D10 : Slice true (roots a8) (target a8) (repeatWord 18374687579166474495) 5 :=
  signedSlice (ms := ([swapRows 48, swapRows 66, flipInput 0, flipInput 1, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D11 : Slice true (roots a8) (target a8) (repeatWord 71777214294589695) 4 :=
  signedSlice (ms := ([swapRows 67] ++ fixRows 8 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D12 : Slice true (roots a8) (target a8) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D13 : Slice true (roots a8) (target a8) (repeatWord 6124988953138320640) 4 :=
  signedSlice (ms := ([swapRows 50, flipInput 1, flipInput 2] ++ fixRows 1 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D14 : Slice true (roots a8) (target a8) (repeatWord 6148820867675914240) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 67, flipInput 1, flipInput 2] ++ fixRows 1 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D15 : Slice true (roots a8) (target a8) (repeatWord 3472328296227680304) 4 :=
  signedSlice (ms := ([swapRows 16, flipInput 0, flipInput 3] ++ fixRows 2 4)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Bound : Lower true (roots a8) (target a8) 9 := by
  have ready : Ready a8 a8Domains (asRow a8Pos) (asRow a8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a8D0 (safeCons a8D1 (safeCons a8D2 (safeCons a8D3 (safeCons a8D4 (safeCons a8D5 (safeCons a8D6 (safeCons a8D7 (safeCons a8D8 (safeCons a8D9 (safeCons a8D10 (safeCons a8D11 (safeCons a8D12 (safeCons a8D13 (safeCons a8D14 (safeCons a8D15 (safeNil a8))))))))))))))))
  exact frozen ready a8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D0 : Slice true (roots a9) (target a9) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([swapRows 33] ++ fixRows 2 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D1 : Slice true (roots a9) (target a9) (repeatWord 14757395258967641292) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 67, flipInput 2, flipInput 5] ++ fixRows 0 2)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D2 : Slice true (roots a9) (target a9) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D3 : Slice true (roots a9) (target a9) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 66, swapRows 67, flipInput 1, flipInput 5] ++ fixRows 0 4)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D4 : Slice true (roots a9) (target a9) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 50, swapRows 83] ++ fixRows 0 16)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D5 : Slice true (roots a9) (target a9) (repeatWord 18374966855136706560) 4 :=
  signedSlice (ms := ([swapRows 50, flipInput 1, flipInput 2] ++ fixRows 0 40)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D6 : Slice true (roots a9) (target a9) (repeatWord 18446462598732840960) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 67, flipInput 1, flipInput 2] ++ fixRows 0 48)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Bound : Lower true (roots a9) (target a9) 8 := by
  have ready : Ready a9 a9Domains (asRow a9Pos) (asRow a9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a9D0 (safeCons a9D1 (safeCons a9D2 (safeCons a9D3 (safeCons a9D4 (safeCons a9D5 (safeCons a9D6 (safeNil a9)))))))
  exact frozen ready a9Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D0 : Slice true (roots a10) (target a10) (repeatWord 3689517697150995660) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 82, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D1 : Slice true (roots a10) (target a10) (repeatWord 18374687579166474495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D2 : Slice true (roots a10) (target a10) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 49, swapRows 83, flipInput 3, flipInput 4] ++ fixRows 4 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D3 : Slice true (roots a10) (target a10) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 1, flipInput 3, flipInput 5] ++ fixRows 0 4)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D4 : Slice true (roots a10) (target a10) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 50, swapRows 84] ++ fixRows 0 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D5 : Slice true (roots a10) (target a10) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, swapRows 83, flipInput 3, flipInput 4] ++ fixRows 32 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D6 : Slice true (roots a10) (target a10) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 50, flipInput 1, flipInput 2, flipInput 3] ++ fixRows 0 32)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D7 : Slice true (roots a10) (target a10) (repeatWord 57421771435671756) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, swapRows 84, flipInput 2] ++ fixRows 8 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Bound : Lower true (roots a10) (target a10) 8 := by
  have ready : Ready a10 a10Domains (asRow a10Pos) (asRow a10Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a10D0 (safeCons a10D1 (safeCons a10D2 (safeCons a10D3 (safeCons a10D4 (safeCons a10D5 (safeCons a10D6 (safeCons a10D7 (safeNil a10))))))))
  exact frozen ready a10Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 6, 22), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D0 : Slice true (roots a11) (target a11) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 16 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Bound : Lower true (roots a11) (target a11) 6 := by
  have ready : Ready a11 a11Domains (asRow a11Pos) (asRow a11Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a11D0 (safeNil a11)
  exact frozen ready a11Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D0 : Slice true (roots a12) (target a12) (repeatWord 71777214294589695) 3 :=
  signedSlice (ms := ([] ++ fixRows 8 0)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Bound : Lower true (roots a12) (target a12) 5 := by
  have ready : Ready a12 a12Domains (asRow a12Pos) (asRow a12Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a12D0 (safeNil a12)
  exact frozen ready a12Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D0 : Slice true (roots a13) (target a13) (repeatWord 71777214294589695) 6 :=
  signedSlice (ms := ([] ++ fixRows 8 0)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D1 : Slice true (roots a13) (target a13) (repeatWord 6149008514797120170) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 82, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D2 : Slice true (roots a13) (target a13) (repeatWord 17361393124654452495) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D3 : Slice true (roots a13) (target a13) (repeatWord 18446462598732906495) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 84] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D4 : Slice true (roots a13) (target a13) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 83, swapRows 84, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 16 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D5 : Slice true (roots a13) (target a13) (repeatWord 6510615555426900570) 5 :=
  signedSlice (ms := ([flipInput 2, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D6 : Slice true (roots a13) (target a13) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 83, swapRows 84, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D7 : Slice true (roots a13) (target a13) (repeatWord 6148914692668172970) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D8 : Slice true (roots a13) (target a13) (repeatWord 17298308644996116495) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 84, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D9 : Slice true (roots a13) (target a13) (repeatWord 17361641477348724495) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D10 : Slice true (roots a13) (target a13) (repeatWord 18374966855153418495) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 84, flipInput 2, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 3 5 false)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Bound : Lower true (roots a13) (target a13) 8 := by
  have ready : Ready a13 a13Domains (asRow a13Pos) (asRow a13Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a13D0 (safeCons a13D1 (safeCons a13D2 (safeCons a13D3 (safeCons a13D4 (safeCons a13D5 (safeCons a13D6 (safeCons a13D7 (safeCons a13D8 (safeCons a13D9 (safeCons a13D10 (safeNil a13)))))))))))
  exact frozen ready a13Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D0 : Slice true (roots a14) (target a14) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 4 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D1 : Slice true (roots a14) (target a14) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 84, flipInput 2, flipInput 4, flipInput 5] ++ fixRows 8 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D2 : Slice true (roots a14) (target a14) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 83, swapRows 84, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 16 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D3 : Slice true (roots a14) (target a14) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, flipInput 2, flipInput 3, flipInput 4] ++ fixRows 32 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D4 : Slice true (roots a14) (target a14) (repeatWord 6510615555426900570) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 84, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D5 : Slice true (roots a14) (target a14) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D6 : Slice true (roots a14) (target a14) (repeatWord 6149008514797120170) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 67, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D7 : Slice true (roots a14) (target a14) (repeatWord 6148914692668172970) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 67, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a6) (G := (neg (target a6))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a6Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D8 : Slice true (roots a14) (target a14) (repeatWord 252645135) 4 :=
  signedSlice (ms := ([swapRows 16, flipInput 0, flipInput 3] ++ fixRows 36 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D9 : Slice true (roots a14) (target a14) (repeatWord 1095216660735) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 24 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Bound : Lower true (roots a14) (target a14) 8 := by
  have ready : Ready a14 a14Domains (asRow a14Pos) (asRow a14Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a14D0 (safeCons a14D1 (safeCons a14D2 (safeCons a14D3 (safeCons a14D4 (safeCons a14D5 (safeCons a14D6 (safeCons a14D7 (safeCons a14D8 (safeCons a14D9 (safeNil a14))))))))))
  exact frozen ready a14Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D0 : Slice true (roots a15) (target a15) (repeatWord 4340410370284600380) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 83, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D1 : Slice true (roots a15) (target a15) (repeatWord 3732415143318664140) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 82, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D2 : Slice true (roots a15) (target a15) (repeatWord 3689517697150995660) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 82, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D3 : Slice true (roots a15) (target a15) (repeatWord 3689348817318890700) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 81, swapRows 82, flipInput 2, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D4 : Slice true (roots a15) (target a15) (repeatWord 17298308644996116495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D5 : Slice true (roots a15) (target a15) (repeatWord 17361393124654452495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D6 : Slice true (roots a15) (target a15) (repeatWord 17361641477348724495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D7 : Slice true (roots a15) (target a15) (repeatWord 18374687579166474495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D8 : Slice true (roots a15) (target a15) (repeatWord 18374966855153418495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 3 5 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D9 : Slice true (roots a15) (target a15) (repeatWord 18446462598732906495) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 84] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Bound : Lower true (roots a15) (target a15) 8 := by
  have ready : Ready a15 a15Domains (asRow a15Pos) (asRow a15Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a15D0 (safeCons a15D1 (safeCons a15D2 (safeCons a15D3 (safeCons a15D4 (safeCons a15D5 (safeCons a15D6 (safeCons a15D7 (safeCons a15D8 (safeCons a15D9 (safeNil a15))))))))))
  exact frozen ready a15Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D0 : Slice true (roots a16) (target a16) (repeatWord 17361641481138401520) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 4)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Bound : Lower true (roots a16) (target a16) 7 := by
  have ready : Ready a16 a16Domains (asRow a16Pos) (asRow a16Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a16D0 (safeNil a16)
  exact frozen ready a16Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D0 : Slice true (roots a17) (target a17) (repeatWord 17361641481138401520) 6 :=
  signedSlice (ms := ([swapRows 82] ++ fixRows 0 4)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Bound : Lower true (roots a17) (target a17) 7 := by
  have ready : Ready a17 a17Domains (asRow a17Pos) (asRow a17Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a17D0 (safeNil a17)
  exact frozen ready a17Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 34, 38), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D0 : Slice true (roots a18) (target a18) (repeatWord 14757395258967641292) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 83, swapRows 84, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 0 2)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D1 : Slice true (roots a18) (target a18) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 50, flipInput 0, flipInput 2, flipInput 5] ++ fixRows 8 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D2 : Slice true (roots a18) (target a18) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([swapRows 33, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D3 : Slice true (roots a18) (target a18) (repeatWord 17361641481138401520) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 67, swapRows 84, flipInput 0, flipInput 1, flipInput 3, flipInput 5] ++ fixRows 0 4)) (base := roots a7) (G := (neg (target a7))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a7Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D4 : Slice true (roots a18) (target a18) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Bound : Lower true (roots a18) (target a18) 7 := by
  have ready : Ready a18 a18Domains (asRow a18Pos) (asRow a18Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a18D0 (safeCons a18D1 (safeCons a18D2 (safeCons a18D3 (safeCons a18D4 (safeNil a18)))))
  exact frozen ready a18Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D0 : Slice true (roots a19) (target a19) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 82] ++ fixRows 0 4)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19Bound : Lower true (roots a19) (target a19) 6 := by
  have ready : Ready a19 a19Domains (asRow a19Pos) (asRow a19Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a19D0 (safeNil a19)
  exact frozen ready a19Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26), (inputs.getD 2 zero, 34, 38), (inputs.getD 3 zero, 18, 26), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20D0 : Slice true (roots a20) (target a20) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, flipInput 0] ++ fixRows 0 4)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20Bound : Lower true (roots a20) (target a20) 6 := by
  have ready : Ready a20 a20Domains (asRow a20Pos) (asRow a20Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a20D0 (safeNil a20)
  exact frozen ready a20Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 56, 60), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21D0 : Slice true (roots a21) (target a21) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 50, swapRows 84] ++ fixRows 1 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21Bound : Lower true (roots a21) (target a21) 6 := by
  have ready : Ready a21 a21Domains (asRow a21Pos) (asRow a21Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a21D0 (safeNil a21)
  exact frozen ready a21Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 34, 38), (inputs.getD 3 zero, 2, 10), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D0 : Slice true (roots a22) (target a22) (repeatWord 17361641481138401520) 9 :=
  signedSlice (ms := ([swapRows 82] ++ fixRows 0 4)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D1 : Slice true (roots a22) (target a22) (repeatWord 18446744069414584320) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D2 : Slice true (roots a22) (target a22) (repeatWord 6510615555426900570) 8 :=
  signedSlice (ms := ([swapRows 82] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D3 : Slice true (roots a22) (target a22) (repeatWord 6172840429334713770) 8 :=
  signedSlice (ms := ([swapRows 67] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D4 : Slice true (roots a22) (target a22) (repeatWord 6149008514797120170) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D5 : Slice true (roots a22) (target a22) (repeatWord 6148914692668172970) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D6 : Slice true (roots a22) (target a22) (repeatWord 3732415143318664140) 8 :=
  signedSlice (ms := ([swapRows 67] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D7 : Slice true (roots a22) (target a22) (repeatWord 3689517697150995660) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D8 : Slice true (roots a22) (target a22) (repeatWord 18374687579166474495) 8 :=
  signedSlice (ms := ([swapRows 64, swapRows 67, flipInput 0] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D9 : Slice true (roots a22) (target a22) (repeatWord 14757395258967641292) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 2)) (base := roots a14) (G := (target a14)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a14Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D10 : Slice true (roots a22) (target a22) (repeatWord 11068046444225730969) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 false)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D11 : Slice true (roots a22) (target a22) (repeatWord 1085102592571150095) 7 :=
  signedSlice (ms := ([swapRows 82] ++ fixRows 4 0)) (base := roots a16) (G := (target a16)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a16Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D12 : Slice true (roots a22) (target a22) (repeatWord 4294967295) 7 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a16) (G := (target a16)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a16Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D13 : Slice true (roots a22) (target a22) (repeatWord 7378697629483820646) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D14 : Slice true (roots a22) (target a22) (repeatWord 71777214294589695) 7 :=
  signedSlice (ms := ([swapRows 67] ++ fixRows 8 0)) (base := roots a18) (G := (target a18)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a18Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D15 : Slice true (roots a22) (target a22) (repeatWord 281470681808895) 7 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a18) (G := (target a18)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a18Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D16 : Slice true (roots a22) (target a22) (repeatWord 6148914691236517205) 6 :=
  signedSlice (ms := ([] ++ fixRows 1 0)) (base := roots a19) (G := (target a19)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a19Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D17 : Slice true (roots a22) (target a22) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([] ++ fixRows 2 0)) (base := roots a20) (G := (target a20)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a20Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D18 : Slice true (roots a22) (target a22) (repeatWord 18374966859414961920) 6 :=
  signedSlice (ms := ([swapRows 67] ++ fixRows 0 8)) (base := roots a21) (G := (target a21)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a21Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D19 : Slice true (roots a22) (target a22) (repeatWord 18446462603027742720) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 16)) (base := roots a21) (G := (target a21)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a21Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D20 : Slice true (roots a22) (target a22) (repeatWord 6124988953138320640) 5 :=
  signedSlice (ms := ([swapRows 50, swapRows 83, swapRows 84] ++ fixRows 1 8)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D21 : Slice true (roots a22) (target a22) (repeatWord 6148820867675914240) 5 :=
  signedSlice (ms := ([swapRows 50, swapRows 84] ++ fixRows 1 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D22 : Slice true (roots a22) (target a22) (repeatWord 57421771435671756) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 84, flipInput 2, flipInput 4, flipInput 5] ++ fixRows 8 2)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D23 : Slice true (roots a22) (target a22) (repeatWord 225176545447116) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 83, swapRows 84, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 16 2)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D24 : Slice true (roots a22) (target a22) (repeatWord 1095216660735) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 50, flipInput 0, flipInput 2, flipInput 5] ++ fixRows 24 0)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D25 : Slice true (roots a22) (target a22) (repeatWord 876173328588) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 24 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22Bound : Lower true (roots a22) (target a22) 11 := by
  have ready : Ready a22 a22Domains (asRow a22Pos) (asRow a22Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a22D0 (safeCons a22D1 (safeCons a22D2 (safeCons a22D3 (safeCons a22D4 (safeCons a22D5 (safeCons a22D6 (safeCons a22D7 (safeCons a22D8 (safeCons a22D9 (safeCons a22D10 (safeCons a22D11 (safeCons a22D12 (safeCons a22D13 (safeCons a22D14 (safeCons a22D15 (safeCons a22D16 (safeCons a22D17 (safeCons a22D18 (safeCons a22D19 (safeCons a22D20 (safeCons a22D21 (safeCons a22D22 (safeCons a22D23 (safeCons a22D24 (safeCons a22D25 (safeNil a22))))))))))))))))))))))))))
  exact frozen ready a22Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots := roots a22
def fullWord := target a22
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4004162176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40780.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩, ⟨.and,[1,6]⟩, ⟨.or,[1,6]⟩, ⟨.and,[5,8]⟩, ⟨.and,[2,9]⟩, ⟨.or,[7,10]⟩, ⟨.or,[3,4]⟩, ⟨.or,[2,5]⟩, ⟨.and,[1,13]⟩, ⟨.or,[12,14]⟩, ⟨.and,[0,15]⟩, ⟨.or,[11,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4004162176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4004162176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40780
open PEqualNP.Outside.L_meta_40780 in
theorem PEqualNP.Outside.L_meta_40780 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4004162176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4004162176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := solve a22Bound

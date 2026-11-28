import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43508.Model
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



def freeWordSigned (roots : List Sig) (w : Sig) := freeWord roots w || freeWord roots (neg w)

private theorem freeWordSigned_ok {roots w} (h : freeWordSigned roots w = true) :
    Available true (roots.map observe) (observe w) := by
  simp only [freeWordSigned, Bool.or_eq_true] at h
  rcases h with yes | no
  · exact freeWord_ok yes
  · have av : Available true (roots.map observe) (observe (neg w)) := freeWord_ok no
    simpa only [obs_neg, inv_inv'] using (avail_inv rfl av)

def checkMapDual (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == neg G && raw.all (fun a => freeWordSigned base (movedWord ms a))

theorem sliceDual {ms raw T base G L d} (ok : checkMapDual ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower true base G L) :
    Slice true raw T d L := by
  simp only [checkMapDual, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, moved_eq_rename] at ok
  have obs : restrictRows (movedRow ms) (observe T) = observe (neg G) :=
    (observe_rename _ _).symm.trans (congrArg observe ok.1)
  have hp : proper (neg G) := proper_neg (a := neg G) (by rwa [neg_neg'])
  refine ⟨movedRow ms, base, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [←bit_moved, all, bit_one]
  · intro a ha
    rw [←observe_rename]
    exact freeWordSigned_ok (ok.2 a ha)
  · rw [obs]
    exact observe_proper hp
  · rw [obs]
    intro p bank reach available
    exact hL p bank reach (by simpa only [obs_neg, inv_inv'] using (avail_inv rfl available))

def checkMapSigned (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWordSigned base (movedWord ms a))

theorem sliceSigned {ms raw T base G L d} (ok : checkMapSigned ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower true base G L) :
    Slice true raw T d L := by
  simp only [checkMapSigned, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, moved_eq_rename] at ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe ok.1)
  refine ⟨movedRow ms, base, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [←bit_moved, all, bit_one]
  · intro a ha
    rw [←observe_rename]
    exact freeWordSigned_ok (ok.2 a ha)
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


def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 6).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 64 d)

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

end PEqualNP.Outside.L_meta_43508.Model

namespace PEqualNP.Outside.L_meta_43508
open PEqualNP.Outside.L_meta_43508.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat) × Nat × List (Sig × Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.1
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def cutCount (g : Atlas) := g.2.2.2.2.2.2.2.1
def cuts (g : Atlas) := g.2.2.2.2.2.2.2.2
def sliceDomain (g : Atlas) (j : Nat) : Sig := ((cuts g).getD j (one,0)).1
def sliceBound (g : Atlas) (j : Nat) : Nat := ((cuts g).getD j (one,0)).2

def projectChoices (raw : List Sig) (v bits : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    if bits == 0 then [] else
      let a := raw.getD (v &&& 15) zero
      let b := raw.getD ((v >>> 4) &&& 15) zero
      let choice := ((v >>> 8) &&& 3, a, b)
      let later := projectChoices (raw ++ [choiceVal choice]) (v >>> 10) (bits >>> 1) n
      if bits &&& 1 == 1 then choice :: later else later

def deadTest (g : Atlas) (ws : List Sig) (k i hint : Nat) : Bool :=
  let j := hint % 65536 - 1
  let d := sliceDomain g j
  let cs := projectChoices (roots g) (record g k i) (hint >>> 16) (top g-k)
  (makePool true d (roots g) cs).any (fun pool => poolCut true d (sliceBound g j) k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 64, swapRows 83]

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && target g == 0xfeeaece0fae8c0c0 then ws.map (movedWord mirrorSteps.reverse) else ws

private theorem mirrorInvariant : autoOK 0xfeeaece0fae8c0c0 mirrorSteps = true := by decide +kernel

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next eq =>
    simp only [Bool.and_eq_true, beq_iff_eq] at eq
    apply rotate_excluded h
    rw [eq.2]
    exact mirrorInvariant
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then decide (h % 65536 - 1 < cutCount g) && deadTest g vs k i h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 128 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      (tip g k i % 65536 - 1 < cutCount g) → Slice true (roots g) (target g) (sliceDomain g (tip g k i % 65536 - 1)) (sliceBound g (tip g k i % 65536 - 1))

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
      have test := h.2.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn h.2.1) _ he h.1.1 hc

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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_43508

namespace PEqualNP.Outside.L_meta_43508
open PEqualNP.Outside.L_meta_43508.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row




def minor2x6K2 : Nat → Nat
  | 0 => 0x13
  | _ => 0

def minor2x6N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def minor2x6R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt minor2x6K2 (i*2) 2
  | _ => 0

def minor2x6H (_k _i : Nat) : Nat := 0

def minor2x6I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt minor2x6K2 (3+((h/1+packedAt minor2x6K2 (2+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor2x6Pos : Nat → Bits
  | 0 => 0x33333333333333333333333333333333
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | _ => 0

def minor2x6Neg : Nat → Bits
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | _ => 0

def minor2x6Atlas : Atlas := ⟨2, rawDecor 3 minor2x6Pos minor2x6Neg, 0x6666666666666666, minor2x6N, minor2x6R, minor2x6H, minor2x6I, 0, []⟩

def minor3xe8K3 : Nat → Nat
  | 0 => 0x87
  | _ => 0

def minor3xe8N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def minor3xe8R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3xe8K3 (i*3) 3
  | _ => 0

def minor3xe8H (_k _i : Nat) : Nat := 0

def minor3xe8I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3xe8K3 (4+((h/1+packedAt minor3xe8K3 (3+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor3xe8Pos : Nat → Bits
  | 0 => 0xcf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf
  | 1 => 0xf3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3
  | 2 => 0x3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf3c
  | _ => 0

def minor3xe8Neg : Nat → Bits
  | 0 => 0x45145145145145145145145145145145
  | 1 => 0x92492492492492492492492492492492
  | 2 => 0x28a28a28a28a28a28a28a28a28a28a28
  | _ => 0

def minor3xe8Atlas : Atlas := ⟨3, rawDecor 7 minor3xe8Pos minor3xe8Neg, 0xe8e8e8e8e8e8e8e8, minor3xe8N, minor3xe8R, minor3xe8H, minor3xe8I, 0, []⟩

def minor3x6K3 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def minor3x6N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def minor3x6R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3x6K3 (i*3) 3
  | _ => 0

def minor3x6H (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3x6K3 (3+i*1) 1
  | _ => 0

def minor3x6I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3x6K3 (5+((h/1+packedAt minor3x6K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor3x6Pos : Nat → Bits
  | 0 => 0xc71c71c71c71c71c71c71c71c71c71c7
  | 1 => 0x38e38e38e38e38e38e38e38e38e38e38
  | 2 => 0x0
  | _ => 0

def minor3x6Neg : Nat → Bits
  | 0 => 0x96596596596596596596596596596596
  | 1 => 0xb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2
  | 2 => 0x24924924924924924924924924924924
  | _ => 0

def minor3x6Atlas : Atlas := ⟨3, rawDecor 7 minor3x6Pos minor3x6Neg, 0x606060606060606, minor3x6N, minor3x6R, minor3x6H, minor3x6I, 1, [(0xf0f0f0f0f0f0f0f, 3)]⟩

def minor3xe6K3 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def minor3xe6N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def minor3xe6R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3xe6K3 (i*3) 3
  | _ => 0

def minor3xe6H (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3xe6K3 (3+i*1) 1
  | _ => 0

def minor3xe6I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt minor3xe6K3 (5+((h/1+packedAt minor3xe6K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor3xe6Pos : Nat → Bits
  | 0 => 0xe9d3a74e9d3a74e9d3a74e9d3a74e9d3
  | 1 => 0x366cd9b366cd9b366cd9b366cd9b366c
  | 2 => 0x3870e1c3870e1c3870e1c3870e1c3870
  | _ => 0

def minor3xe6Neg : Nat → Bits
  | 0 => 0xa54a952a54a952a54a952a54a952a54a
  | 1 => 0xa54a952a54a952a54a952a54a952a54a
  | 2 => 0x183060c183060c183060c183060c1830
  | _ => 0

def minor3xe6Atlas : Atlas := ⟨3, rawDecor 7 minor3xe6Pos minor3xe6Neg, 0xe6e6e6e6e6e6e6e6, minor3xe6N, minor3xe6R, minor3xe6H, minor3xe6I, 1, [(0xf0f0f0f0f0f0f0f, 3)]⟩

def minor3x16K1 : Nat → Nat
  | 0 => 0x284b20544852044280a690a40886010d2148110
  | _ => 0

def minor3x16K2 : Nat → Nat
  | 0 => 0x1cc20054322149528a01ad7588c4348520c43148520a84048520944348510c43248510b04048510984348110c83248110b04148110e12148110
  | _ => 0

def minor3x16K3 : Nat → Nat
  | 0 => 0x254e1899c502c4910200419185500a5099223500cea850a0b283c6941750a141050a110d5038214503d4280ea0da83ea140230482a15020501a9800810415654f64a45d5c468b2eabe6490df31487b90a43b88521e84290ec21487210a437cc121bc6090dc30487790243dc4121be64905f31482f18a4170c520de42906d21482f98241ec8120dc40907820483610241a08120f420905f32442f1922174c910b864885f31443b10a21d48510be60887a20443c90221ec4110ec20887810443a08221c04110
  | _ => 0

def minor3x16K4 : Nat → Nat
  | 0 => 0x86156c6242661d8a6008c1b04c04006171b2fc87e21f487c21fc83e20f483c20fc43e10f443c10
  | _ => 0

def minor3x16K5 : Nat → Nat
  | 0 => 0x87
  | _ => 0

def minor3x16N (k : Nat) : Nat :=
  match k with
  | 1 => 3
  | 2 => 10
  | 3 => 40
  | 4 => 12
  | 5 => 1
  | _ => 0

def minor3x16R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt minor3x16K1 (i*47) 47
  | 2 => packedAt minor3x16K2 (i*36) 36
  | 3 => packedAt minor3x16K3 (i*25) 25
  | 4 => packedAt minor3x16K4 (i*14) 14
  | 5 => packedAt minor3x16K5 (i*3) 3
  | _ => 0

def minor3x16H (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt minor3x16K1 (141+i*2) 2
  | 2 => packedAt minor3x16K2 (360+i*2) 2
  | 3 => packedAt minor3x16K3 (1000+i*2) 2
  | 4 => packedAt minor3x16K4 (168+i*2) 2
  | _ => 0

def minor3x16I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt minor3x16K1 (149+((h/1+packedAt minor3x16K1 (147+(h % 1)*2) 2) % 3)*3) 3
  | 2 => packedAt minor3x16K2 (388+((h/2+packedAt minor3x16K2 (380+(h % 2)*4) 4) % 14)*5) 5
  | 3 => packedAt minor3x16K3 (1140+((h/10+packedAt minor3x16K3 (1080+(h % 10)*6) 6) % 62)*7) 7
  | 4 => packedAt minor3x16K4 (207+((h/3+packedAt minor3x16K4 (192+(h % 3)*5) 5) % 21)*5) 5
  | 5 => packedAt minor3x16K5 (4+((h/1+packedAt minor3x16K5 (3+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor3x16Pos : Nat → Bits
  | 0 => 0xc0e070381c0e070381c0e070381c0e07
  | 1 => 0x70381c0e070381c0e070381c0e07038
  | 2 => 0x381c0e070381c0e070381c0e070381c0
  | _ => 0

def minor3x16Neg : Nat → Bits
  | 0 => 0x92c964b2592c964b2592c964b2592c96
  | 1 => 0xa6532994ca6532994ca6532994ca6532
  | 2 => 0x349a4d269349a4d269349a4d269349a4
  | _ => 0

def minor3x16Atlas : Atlas := ⟨5, rawDecor 7 minor3x16Pos minor3x16Neg, 0x1616161616161616, minor3x16N, minor3x16R, minor3x16H, minor3x16I, 3, [(0xf0f0f0f0f0f0f0f, 3), (0x3333333333333333, 3), (0x5555555555555555, 3)]⟩

def minor4xfee8K2 : Nat → Nat
  | 0 => 0x3188030c95b1836318451c416158c1500965d7a91195324c521a1191324c521c1151324c52192195324c120a2191324c120c2151324c12094195314c110a4191314c110c4151314c110981952148110a81912148110c81512148110
  | _ => 0

def minor4xfee8K3 : Nat → Nat
  | 0 => 0x4929450c09b032bd4865c14b8d009152134253113cad6202c3939b3e2c12d0628818108caa20e0460f60718306074230605454951551983810c049884b2504a37032637094020498942584988e2a26498e3109324c6a8a2992633b5050d219c2828690cb1513248718869924364514c9219a2a26290e510d31486c8a498a43c5324c5218e2a2649863109324c2b0a0992611c544c530ca20a629856141314c26ea2a1a41345150d20962a264906310d32482d0a0992412c5448520d220a42905a1412148270a89824198434c120b42926090724c9304825ea4a1a212c5250d108fa9a84884714d4244268a898a2194434c510b828262884d15121443488490a217050485109c2a260886610d30442e0a298221d1314c1109c2a240886a10920442e0a290221e12148110
  | _ => 0

def minor4xfee8K4 : Nat → Nat
  | 0 => 0x289e012992208783182906b82abb2c88919bbb000534a384a721b69d9916332b951c81a63b32a684302e3aa2bb37a40eab0dbb27969c133b111f8f9e8ca235bb0e0d351b212eb8a3103b198c3b24bb3b1ab09d072c3b02b1b2020594bb17bb13bb3b143b0f063a10ad39008a1709a80aadb395b72a03b9b10b252f12b62018891a3425af880b9f0c9540c007c14387c8801281c08082074100070384c04900010980c1408928921b28485109104b24b1216082904c26921226424406c82612640414806d05028928082104d861c1038dbbf434cafd0932ef324cb78c932ec324cb70c932cc324cafd0532be414caf10532df314cbbc8532bf404caf90132bc404cb7cc132ef204cafd0d31bf424c6f90931bc424c77cc931dd324c6fd0531f7314c778c531f4314c770c531d4314c7d88531bf404c6f90131bc404c77cc131f7104c6fd0d21be43486f50d21bc43486fd0921ee32487b4c921bf41487d8c521f531487dc8521ee21487d08521ec21487908521bf40486f90121bc40487bc8121f710486fd0d30bf424c2f90930bc424c37cc930dd324c2fd0530be414c2f10530df314c374c530bf404c3ecc130de304c3e0c130dc304c360c130fa204c3e84130bf43482f90d20bd43482f10d20bf42483b8c920ed32482fd0520be41482f10520ef21483b48520bf40483e8c120f930483ec8120ee20483e08120ec20483a08120fa10482fd0d10be43442f50d10bc43442fd0910be42442f50910bc42442fd0510f631443d4c510f621443d48510bf40443e8c110f930443e88110f920443ec4110f610443e04110f410443c04110
  | _ => 0

def minor4xfee8K5 : Nat → Nat
  | 0 => 0xc1e32ec12c3000ec2a6a2c3070683099020ac16130c02624530b280420030002812c14c2301502703fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0

def minor4xfee8K6 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def minor4xfee8N (k : Nat) : Nat :=
  match k with
  | 2 => 12
  | 3 => 48
  | 4 => 118
  | 5 => 24
  | 6 => 1
  | _ => 0

def minor4xfee8R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfee8K2 (i*48) 48
  | 3 => packedAt minor4xfee8K3 (i*37) 37
  | 4 => packedAt minor4xfee8K4 (i*26) 26
  | 5 => packedAt minor4xfee8K5 (i*15) 15
  | 6 => packedAt minor4xfee8K6 (i*4) 4
  | _ => 0

def minor4xfee8H (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfee8K2 (576+i*2) 2
  | 3 => packedAt minor4xfee8K3 (1776+i*3) 3
  | 4 => packedAt minor4xfee8K4 (3068+i*3) 3
  | 5 => packedAt minor4xfee8K5 (360+i*3) 3
  | _ => 0

def minor4xfee8I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfee8K2 (615+((h/3+packedAt minor4xfee8K2 (600+(h % 3)*5) 5) % 23)*5) 5
  | 3 => packedAt minor4xfee8K3 (1992+((h/12+packedAt minor4xfee8K3 (1920+(h % 12)*6) 6) % 56)*7) 7
  | 4 => packedAt minor4xfee8K4 (3654+((h/29+packedAt minor4xfee8K4 (3422+(h % 29)*8) 8) % 135)*8) 8
  | 5 => packedAt minor4xfee8K5 (468+((h/6+packedAt minor4xfee8K5 (432+(h % 6)*6) 6) % 36)*6) 6
  | 6 => packedAt minor4xfee8K6 (5+((h/1+packedAt minor4xfee8K6 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfee8Pos : Nat → Bits
  | 0 => 0xcf0cf0cf0cf0cf0cf0cf0cf0cf0cf0cf
  | 1 => 0x33333333333333333333333333333333
  | 2 => 0x3cc3cc3cc3cc3cc3cc3cc3cc3cc3cc3c
  | 3 => 0xc0fc0fc0fc0fc0fc0fc0fc0fc0fc0fc0
  | _ => 0

def minor4xfee8Neg : Nat → Bits
  | 0 => 0x45045045045045045045045045045045
  | 1 => 0x12112112112112112112112112112112
  | 2 => 0x28428428428428428428428428428428
  | 3 => 0x80a80a80a80a80a80a80a80a80a80a80
  | _ => 0

def minor4xfee8Atlas : Atlas := ⟨6, rawDecor 15 minor4xfee8Pos minor4xfee8Neg, 0xfee8fee8fee8fee8, minor4xfee8N, minor4xfee8R, minor4xfee8H, minor4xfee8I, 4, [(0xff00ff00ff00ff, 4), (0xf0f0f0f0f0f0f0f, 4), (0x3333333333333333, 4), (0x5555555555555555, 4)]⟩

def minor4xfe80K3 : Nat → Nat
  | 0 => 0x10da6db06b3948421e920083c44010
  | _ => 0

def minor4xfe80K4 : Nat → Nat
  | 0 => 0xc1e32ec12c3000ec2a6a2c3070683099020ac16130c02624530b28042003000009012d8001bb40900fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0

def minor4xfe80K5 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def minor4xfe80N (k : Nat) : Nat :=
  match k with
  | 3 => 3
  | 4 => 24
  | 5 => 1
  | _ => 0

def minor4xfe80R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfe80K3 (i*26) 26
  | 4 => packedAt minor4xfe80K4 (i*15) 15
  | 5 => packedAt minor4xfe80K5 (i*4) 4
  | _ => 0

def minor4xfe80H (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfe80K3 (78+i*3) 3
  | 4 => packedAt minor4xfe80K4 (360+i*3) 3
  | _ => 0

def minor4xfe80I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfe80K3 (91+((h/1+packedAt minor4xfe80K3 (87+(h % 1)*4) 4) % 9)*3) 3
  | 4 => packedAt minor4xfe80K4 (468+((h/6+packedAt minor4xfe80K4 (432+(h % 6)*6) 6) % 36)*6) 6
  | 5 => packedAt minor4xfe80K5 (5+((h/1+packedAt minor4xfe80K5 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfe80Pos : Nat → Bits
  | 0 => 0x3f447e88fd11fa23f447e88fd11fa23f
  | 1 => 0xc7878f0f1e1e3c3c7878f0f1e1e3c3c7
  | 2 => 0x7f80ff01fe03fc07f80ff01fe03fc07
  | 3 => 0xf8fff1ffe3ffc7ff8fff1ffe3ffc7ff8
  | _ => 0

def minor4xfe80Neg : Nat → Bits
  | 0 => 0x134426884d109a2134426884d109a213
  | 1 => 0x85850b0a16142c285850b0a16142c285
  | 2 => 0x6d00da01b4036806d00da01b4036806
  | 3 => 0x20224044808901120224044808901120
  | _ => 0

def minor4xfe80Atlas : Atlas := ⟨5, rawDecor 15 minor4xfe80Pos minor4xfe80Neg, 0xfe80fe80fe80fe80, minor4xfe80N, minor4xfe80R, minor4xfe80H, minor4xfe80I, 6, [(0xff00ff00ff00ff0, 4), (0x33cc33cc33cc33cc, 4), (0x55aa55aa55aa55aa, 4), (0x9999999999999999, 4), (0xa5a5a5a5a5a5a5a5, 4), (0xc3c3c3c3c3c3c3c3, 4)]⟩

def minor4xfec0K4 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def minor4xfec0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def minor4xfec0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xfec0K4 (i*4) 4
  | _ => 0

def minor4xfec0H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xfec0K4 (4+i*1) 1
  | _ => 0

def minor4xfec0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xfec0K4 (6+((h/1+packedAt minor4xfec0K4 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfec0Pos : Nat → Bits
  | 0 => 0x3c93c93c93c93c93c93c93c93c93c93c
  | 1 => 0xcf1cf1cf1cf1cf1cf1cf1cf1cf1cf1cf
  | 2 => 0xfe0fe0fe0fe0fe0fe0fe0fe0fe0fe0f
  | 3 => 0xf0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0
  | _ => 0

def minor4xfec0Neg : Nat → Bits
  | 0 => 0x1c91c91c91c91c91c91c91c91c91c91c
  | 1 => 0x45145145145145145145145145145145
  | 2 => 0xaa0aa0aa0aa0aa0aa0aa0aa0aa0aa0a
  | 3 => 0xa04a04a04a04a04a04a04a04a04a04a0
  | _ => 0

def minor4xfec0Atlas : Atlas := ⟨4, rawDecor 15 minor4xfec0Pos minor4xfec0Neg, 0xfec0fec0fec0fec0, minor4xfec0N, minor4xfec0R, minor4xfec0H, minor4xfec0I, 1, [(0x5555555555555555, 4)]⟩

def minor4xffe8K4 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def minor4xffe8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def minor4xffe8R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xffe8K4 (i*4) 4
  | _ => 0

def minor4xffe8H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xffe8K4 (4+i*1) 1
  | _ => 0

def minor4xffe8I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xffe8K4 (6+((h/1+packedAt minor4xffe8K4 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xffe8Pos : Nat → Bits
  | 0 => 0x8f23c8f23c8f23c8f23c8f23c8f23c8f
  | 1 => 0x334cd334cd334cd334cd334cd334cd33
  | 2 => 0x3c8f23c8f23c8f23c8f23c8f23c8f23c
  | 3 => 0xc0f03c0f03c0f03c0f03c0f03c0f03c0
  | _ => 0

def minor4xffe8Neg : Nat → Bits
  | 0 => 0x85214852148521485214852148521485
  | 1 => 0x12449124491244912449124491244912
  | 2 => 0x288a2288a2288a2288a2288a2288a228
  | 3 => 0x0
  | _ => 0

def minor4xffe8Atlas : Atlas := ⟨4, rawDecor 15 minor4xffe8Pos minor4xffe8Neg, 0xffe8ffe8ffe8ffe8, minor4xffe8N, minor4xffe8R, minor4xffe8H, minor4xffe8I, 1, [(0xff00ff00ff00ff, 4)]⟩

def minor4xfee0K4 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def minor4xfee0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def minor4xfee0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xfee0K4 (i*4) 4
  | _ => 0

def minor4xfee0H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xfee0K4 (4+i*1) 1
  | _ => 0

def minor4xfee0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt minor4xfee0K4 (6+((h/1+packedAt minor4xfee0K4 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfee0Pos : Nat → Bits
  | 0 => 0x73273273273273273273273273273273
  | 1 => 0x9c39c39c39c39c39c39c39c39c39c39c
  | 2 => 0x1fc1fc1fc1fc1fc1fc1fc1fc1fc1fc1f
  | 3 => 0xe0fe0fe0fe0fe0fe0fe0fe0fe0fe0fe0
  | _ => 0

def minor4xfee0Neg : Nat → Bits
  | 0 => 0x31231231231231231231231231231231
  | 1 => 0x94294294294294294294294294294294
  | 2 => 0xa40a40a40a40a40a40a40a40a40a40a
  | 3 => 0x40940940940940940940940940940940
  | _ => 0

def minor4xfee0Atlas : Atlas := ⟨4, rawDecor 15 minor4xfee0Pos minor4xfee0Neg, 0xfee0fee0fee0fee0, minor4xfee0N, minor4xfee0R, minor4xfee0H, minor4xfee0I, 1, [(0x3333333333333333, 4)]⟩

def minor4xfee4K2 : Nat → Nat
  | 0 => 0x82c6a498221535348110
  | _ => 0

def minor4xfee4K3 : Nat → Nat
  | 0 => 0xf498ec7bc806944853c2f73c6f5aa3042852c42400330c932b6418c2d50630af424c2b10930b641882d506209f43482710d20f340442dd0110f230443c4c110f220443c48110
  | _ => 0

def minor4xfee4K4 : Nat → Nat
  | 0 => 0x348b4d34934d0048e41e9b4d20b340ae20c6b4d06a34d1cd16d30caa504d0a634d3406a005000944249249804a0524907f997e32fa65f0cbf98fe31fa63f0c7f90fe21fa43f087f987e30fa61f0c3f907e20fa41f083f887710fc21f443a887c10
  | _ => 0

def minor4xfee4K5 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def minor4xfee4N (k : Nat) : Nat :=
  match k with
  | 2 => 2
  | 3 => 15
  | 4 => 26
  | 5 => 1
  | _ => 0

def minor4xfee4R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfee4K2 (i*37) 37
  | 3 => packedAt minor4xfee4K3 (i*26) 26
  | 4 => packedAt minor4xfee4K4 (i*15) 15
  | 5 => packedAt minor4xfee4K5 (i*4) 4
  | _ => 0

def minor4xfee4H (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfee4K3 (390+i*3) 3
  | 4 => packedAt minor4xfee4K4 (390+i*3) 3
  | _ => 0

def minor4xfee4I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfee4K2 (75+((h/1+packedAt minor4xfee4K2 (74+(h % 1)*1) 1) % 2)*3) 3
  | 3 => packedAt minor4xfee4K3 (450+((h/3+packedAt minor4xfee4K3 (435+(h % 3)*5) 5) % 22)*5) 5
  | 4 => packedAt minor4xfee4K4 (504+((h/6+packedAt minor4xfee4K4 (468+(h % 6)*6) 6) % 45)*6) 6
  | 5 => packedAt minor4xfee4K5 (5+((h/1+packedAt minor4xfee4K5 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfee4Pos : Nat → Bits
  | 0 => 0x279c279c279c279c279c279c279c279c
  | 1 => 0x38e338e338e338e338e338e338e338e3
  | 2 => 0xc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fc
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | _ => 0

def minor4xfee4Neg : Nat → Bits
  | 0 => 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
  | 1 => 0x28a228a228a228a228a228a228a228a2
  | 2 => 0x40504050405040504050405040504050
  | 3 => 0x94009400940094009400940094009400
  | _ => 0

def minor4xfee4Atlas : Atlas := ⟨5, rawDecor 15 minor4xfee4Pos minor4xfee4Neg, 0xfee4fee4fee4fee4, minor4xfee4N, minor4xfee4R, minor4xfee4H, minor4xfee4I, 5, [(0x3333333333333333, 4), (0x33cc33cc33cc33cc, 4), (0x3c3c3c3c3c3c3c3c, 4), (0x3c003c003c003c, 3), (0x30c030c030c030c, 3)]⟩

def minor4xfed0K3 : Nat → Nat
  | 0 => 0x2280fd087910
  | _ => 0

def minor4xfed0K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def minor4xfed0N (k : Nat) : Nat :=
  match k with
  | 3 => 2
  | 4 => 1
  | _ => 0

def minor4xfed0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfed0K3 (i*15) 15
  | 4 => packedAt minor4xfed0K4 (i*4) 4
  | _ => 0

def minor4xfed0H (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfed0K3 (30+i*1) 1
  | _ => 0

def minor4xfed0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfed0K3 (34+((h/1+packedAt minor4xfed0K3 (32+(h % 1)*2) 2) % 4)*3) 3
  | 4 => packedAt minor4xfed0K4 (5+((h/1+packedAt minor4xfed0K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfed0Pos : Nat → Bits
  | 0 => 0x78a78a78a78a78a78a78a78a78a78a78
  | 1 => 0x9c39c39c39c39c39c39c39c39c39c39c
  | 2 => 0x1fc1fc1fc1fc1fc1fc1fc1fc1fc1fc1f
  | 3 => 0xe0fe0fe0fe0fe0fe0fe0fe0fe0fe0fe0
  | _ => 0

def minor4xfed0Neg : Nat → Bits
  | 0 => 0x3aa3aa3aa3aa3aa3aa3aa3aa3aa3aa3a
  | 1 => 0x8c28c28c28c28c28c28c28c28c28c28c
  | 2 => 0x12812812812812812812812812812812
  | 3 => 0x40540540540540540540540540540540
  | _ => 0

def minor4xfed0Atlas : Atlas := ⟨4, rawDecor 15 minor4xfed0Pos minor4xfed0Neg, 0xfed0fed0fed0fed0, minor4xfed0N, minor4xfed0R, minor4xfed0H, minor4xfed0I, 1, [(0x330033003300330, 3)]⟩

def minor4xfe40K3 : Nat → Nat
  | 0 => 0x1ca84aa6a088903123a401868aaa00941aaaaa59e00107d090952dd0532b4414caed0132b8404cad90432b5410cae90032b9400cabd0931ac424c6ed0131b8404c6b90831ad420c6e90031b9400c6e90321b940c86e90221b940887948421
  | _ => 0

def minor4xfe40K4 : Nat → Nat
  | 0 => 0x2344a0cb89a4038294e38e063846025ac6b6b9089ea30338738a84247001403000fffffe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41bc83f107d20da41f083f887710fc21f443a887c10
  | _ => 0

def minor4xfe40K5 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def minor4xfe40N (k : Nat) : Nat :=
  match k with
  | 3 => 21
  | 4 => 28
  | 5 => 1
  | _ => 0

def minor4xfe40R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfe40K3 (i*26) 26
  | 4 => packedAt minor4xfe40K4 (i*15) 15
  | 5 => packedAt minor4xfe40K5 (i*4) 4
  | _ => 0

def minor4xfe40H (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfe40K3 (546+i*1) 1
  | 4 => packedAt minor4xfe40K4 (420+i*1) 1
  | _ => 0

def minor4xfe40I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfe40K3 (592+((h/5+packedAt minor4xfe40K3 (567+(h % 5)*5) 5) % 27)*6) 6
  | 4 => packedAt minor4xfe40K4 (490+((h/7+packedAt minor4xfe40K4 (448+(h % 7)*6) 6) % 35)*6) 6
  | 5 => packedAt minor4xfe40K5 (5+((h/1+packedAt minor4xfe40K5 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfe40Pos : Nat → Bits
  | 0 => 0x78623c311e188f0c478623c311e188f0
  | 1 => 0x87c3c3e1e1f0f0f8787c3c3e1e1f0f0f
  | 2 => 0x7fc03fe01ff00ff807fc03fe01ff00f
  | 3 => 0xf87ffc3ffe1fff0fff87ffc3ffe1fff0
  | _ => 0

def minor4xfe40Neg : Nat → Bits
  | 0 => 0x3c621e310f18878c43c621e310f18878
  | 1 => 0x15428aa14550a2a8515428aa14550a2a
  | 2 => 0x26681334099a04cd026681334099a04c
  | 3 => 0x40112008900448022401120089004480
  | _ => 0

def minor4xfe40Atlas : Atlas := ⟨5, rawDecor 15 minor4xfe40Pos minor4xfe40Neg, 0xfe40fe40fe40fe40, minor4xfe40N, minor4xfe40R, minor4xfe40H, minor4xfe40I, 1, [(0x5555555555555555, 4)]⟩

def minor4xfe60K2 : Nat → Nat
  | 0 => 0x439859721c8110
  | _ => 0

def minor4xfe60K3 : Nat → Nat
  | 0 => 0x228c9185ce43807739a51396c102068132425b625aa990e412f5250d109629286884d15131443288698a2170504c5109b2a642885c9432144270a89822198434c110b828a60884e95320442e4a390221e321c8110
  | _ => 0

def minor4xfe60K4 : Nat → Nat
  | 0 => 0x1017034056d709570cd70c5350cb8b5711d71651971249884dc482971605120189ce479707d708d4c80902d706970645571705970152d455d3c74e171082510a4700d51701c09705d5400e9711488c1710420b060a83d28384cec6c1130f971703168d8c8d040a0fd40f0f4bd70ac4570d57149395890602000888228540010874083000c0140610603000080014000400060000800040006000100008000e000a000000020001000060006000080018000200030003000140007000180008000c000600050001800100000000400028000c0002000500010001800000003000180004000200040000800040009000500020001800020006000080010000c00050001800000006000000028001200030001000200010000a0004000200000000200000000800140000000500000000c0006000000000000c000600040000000000008000300020000c00060003bf434c6fd0931bd424c6f10931bf414c7dcc531de314c7d0c531dc314c7d88531f5214c6fd0131be404c6f10131f7104c6fd0f21be43c86f50f21bc43c86f90b21ee32c87b4cb21bd41c87dcc721f431c87d88721ee21c87d48721ec21c86f90321bd40c86f10321ed20c87dc4321bf434c2fd0930bd424c2f10930bf414c2f90530bc414c2fd0130fb304c378c130f8304c370c130fa204c3e48130fa104c2fd0f20be43c82f50f20bc43c82f90b20ee32c83b4cb20be41c82f50720bc41c83bc8720ed21c82f50320fb30c83e0c320fa20c83b88320f920c83b08320fa10c82fd0d10be43442f50d10bc43442fd0910be42442f50910bc42442fd0510f631443d4c510f721443d08510bf40443e8c110f930443ec8110f820443ec4110f610443e04110f410443c04110
  | _ => 0

def minor4xfe60K5 : Nat → Nat
  | 0 => 0xc1e32ec12c3000ec2a6a2c3070683099020ac16130c02624530b280420030003a92c10eb30112c703fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0

def minor4xfe60K6 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def minor4xfe60N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | 3 => 14
  | 4 => 92
  | 5 => 24
  | 6 => 1
  | _ => 0

def minor4xfe60R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfe60K2 (i*48) 48
  | 3 => packedAt minor4xfe60K3 (i*37) 37
  | 4 => packedAt minor4xfe60K4 (i*26) 26
  | 5 => packedAt minor4xfe60K5 (i*15) 15
  | 6 => packedAt minor4xfe60K6 (i*4) 4
  | _ => 0

def minor4xfe60H (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfe60K2 (48+i*2) 2
  | 3 => packedAt minor4xfe60K3 (518+i*3) 3
  | 4 => packedAt minor4xfe60K4 (2392+i*17) 17
  | 5 => packedAt minor4xfe60K5 (360+i*3) 3
  | _ => 0

def minor4xfe60I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfe60K2 (51+((h/1+packedAt minor4xfe60K2 (50+(h % 1)*1) 1) % 2)*2) 2
  | 3 => packedAt minor4xfe60K3 (575+((h/3+packedAt minor4xfe60K3 (560+(h % 3)*5) 5) % 20)*5) 5
  | 4 => packedAt minor4xfe60K4 (4117+((h/23+packedAt minor4xfe60K4 (3956+(h % 23)*7) 7) % 117)*8) 8
  | 5 => packedAt minor4xfe60K5 (468+((h/6+packedAt minor4xfe60K5 (432+(h % 6)*6) 6) % 36)*6) 6
  | 6 => packedAt minor4xfe60K6 (5+((h/1+packedAt minor4xfe60K6 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfe60Pos : Nat → Bits
  | 0 => 0xe470f91c3e470f91c3e470f91c3e470f
  | 1 => 0x278f09e3c278f09e3c278f09e3c278f0
  | 2 => 0xf80ffe03ff80ffe03ff80ffe03ff80ff
  | 3 => 0x3ff00ffc03ff00ffc03ff00ffc03ff00
  | _ => 0

def minor4xfe60Neg : Nat → Bits
  | 0 => 0xa538a94e2a538a94e2a538a94e2a538a
  | 1 => 0x25aa896aa25aa896aa25aa896aa25aa8
  | 2 => 0x280cca033280cca033280cca033280cc
  | 3 => 0x12400490012400490012400490012400
  | _ => 0

def minor4xfe60Atlas : Atlas := ⟨6, rawDecor 15 minor4xfe60Pos minor4xfe60Neg, 0xfe60fe60fe60fe60, minor4xfe60N, minor4xfe60R, minor4xfe60H, minor4xfe60I, 6, [(0xff00ff00ff00ff, 4), (0xff00ff00ff00ff0, 4), (0x3333333333333333, 4), (0x5555555555555555, 4), (0xf0f0f0f0f0f0f0f0, 4), (0xf000f000f000f0, 3)]⟩

def minor4xfe64K2 : Nat → Nat
  | 0 => 0x408b0d8d50c851098997214c110
  | _ => 0

def minor4xfe64K3 : Nat → Nat
  | 0 => 0x1f4265700268cd252aaca095e88e2f5e08f2f2e30eaf5e453015434c0516bd38448bd69b0e201a9208160a50bc70f2c4832f180bc05230c59410600040000c00018000000008000600032000300028000080008001600018001000018001600010000000034000300008000a00000001600000001600018001600010001600008000600008000a00000000a0002800000000000060001800000000000020000800000000cb948404c65aa4202632e52903218fa9a8190c714d40c8658a4a0643a82050321c621a8790e950543c869ea6a06434c5350321d42028190c7d51318c38a4298c61a641c8630d2a0e43184b950424c25aa221261aa5010930d4a808498630c0424c25ea5a0a612e54c8530962a642986310a304c34e42a0e412d5250420d390a82104bd494384258a4a1c2139548c210b928c61084d151314426ca990a217250c8510d32a642886955321443c4a190a21e150c8510f1a06428869d0321443a26318221e3218c1109c2a260886610d30443c64298221365484110
  | _ => 0

def minor4xfe64K4 : Nat → Nat
  | 0 => 0x6000284015584038019819c800e8eb100020e880100000007028280030000004000e0002000400004000200030000800040007000700000000000020003000200004001400010001c00040014000780008000c0006000300028000c0000000000038001c0006000b8000800020002000380008000c000700010005800000000000b8000c0004000600030001800160002000580008000c000a000380008000c00060003000440004000a00050002800160003000100018000c0002000200048001c00140001000180000000600010000000000010000100008000400030007800380004001200070003800080000000a0000000000006000300000002000020001000000004000300078003800180002000900008001c001200070001800000006000b00038001c000c00060003000280002000a00008001a000300010001800000006000b000380018000c000600038001c00080001000000004000a000b00038002c0006000300018000c0000000000018000c0006000000008001000020007000300014001600030001800000000000300000000c000600030000000000006000000018000efd0d31bf424c6f50931bc424c6fd0531f7314c778c531f4314c770c531f6214c7d48531bf404c6f10131dc304c7dc4131bf43c86f90f21bd43c86f10f21be42c87bccb21ee32c87b4cb21ec32c86f50721f621c87b88721f521c87b08721be40c86f50321ee20c87b48321f710c87bd0f21ee43c87b50f21ec43c86b50721ef31c87b8c721ed31c87b0c721ef40c87b90321ed40c87b10321ef30c87b0c321ef10c879c4321ec10c87bd0d21ee43487b50d21ec43487bd0521e741486bd0521ef31487b8c521e631487b4c521e531487b0c521ef40487b90121ed40487b10121ef30487b0c121ef10487b04121bd438c2fd0a30be428c2f50a30de328c370ca30be418c2f50630bc418c37cc630dd318c3bc8630ed218c2f90230fb308c37cc230f8308c3e88230f9208c2fd0d30ef424c2fd0930af424c2f50930ec424c2f10930ac424c2fd0530be414c2f10530ef214c3b48530bf404c3ecc130de304c3e0c130dc304c3e88130f9204c2fd0f20be43c82f50f20bc43c82f90b20ee32c83b4cb20be41c82f50720bc41c83bc8720ed21c82f50320fa20c83b88320f920c82fd0c20be43082f50c20bc43082f90820ef32083b0c820be41082f50420bc41083bc8420ed21082f90020ef20083e88020f920083b48020bf43842f90e10bd43842f10e10bf42842f90a10bd42842f10a10bd41843bc8610ed21842f90210fa30843e4c210fb10843dc4210f810842fd0d10be43442f50d10bc43442fd0910be42442f50910bc42442fd0510f631443d4c510f721443bc8510e721443b48510f421442fd0110fa30443e4c110fb10443d84110f810443d04110
  | 1 => 0x9ab93e98cd679362d972a142988f61906a7806344c85c2ab93e09972a5139d572b94e12440745c8396a2a5c99d06425c89030a048868a65f02a2c2c584c2a518504225ca43315ac0c21f4a2bc5e7820ae4b8b2491c476823310d507a289147a281fa39721416a18526a3b07062220d8b13ab9258e566720402d209323951727f47ab004a200aace67e0484572b95ca8d729a43a3478692eae4425e172e460375cae5720044131729b5a29d726d0eae44a380f290903e1901cc83a5c848ac362aac512aa5ca7cca5a07938dc7009ae514b95c2e42080021bc8c5b532e52ab95c9015a812cadc46b9052e48877251a06ab9570192c5727ae4c00c0013980f0880020631000a00161392870
  | _ => 0

def minor4xfe64K5 : Nat → Nat
  | 0 => 0x3488ccb44b46803b4b9c9aa41e1a45b4d082b4804d34098a14d30b010802400069c44c0400dc0c40041dc0c00ff997e32fa65f0cbf98fe31fa63f0c7f90ef21fc43f487690fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0

def minor4xfe64K6 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def minor4xfe64N (k : Nat) : Nat :=
  match k with
  | 2 => 2
  | 3 => 47
  | 4 => 185
  | 5 => 26
  | 6 => 1
  | _ => 0

def minor4xfe64R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfe64K2 (i*48) 48
  | 3 => packedAt minor4xfe64K3 (i*37) 37
  | 4 => packedAt minor4xfe64K4 (i*26) 26
  | 5 => packedAt minor4xfe64K5 (i*15) 15
  | 6 => packedAt minor4xfe64K6 (i*4) 4
  | _ => 0

def minor4xfe64H (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt minor4xfe64K3 (1739+i*18) 18
  | 4 => packedAt minor4xfe64K4 (4810+i*17) 17
  | 5 => packedAt minor4xfe64K5 (390+i*4) 4
  | _ => 0

def minor4xfe64I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt minor4xfe64K2 (98+((h/1+packedAt minor4xfe64K2 (96+(h % 1)*2) 2) % 3)*3) 3
  | 3 => packedAt minor4xfe64K3 (2651+((h/11+packedAt minor4xfe64K3 (2585+(h % 11)*6) 6) % 57)*7) 7
  | 4 => packedAt minor4xfe64K4 (8323+((h/46+packedAt minor4xfe64K4 (7955+(h % 46)*8) 8) % 222)*9) 9
  | 5 => packedAt minor4xfe64K5 (530+((h/6+packedAt minor4xfe64K5 (494+(h % 6)*6) 6) % 36)*6) 6
  | 6 => packedAt minor4xfe64K6 (5+((h/1+packedAt minor4xfe64K6 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfe64Pos : Nat → Bits
  | 0 => 0x8784cf0f099e1e133c3c2678784cf0f0
  | 1 => 0x787cf0f0f9e1e1f3c3c3e78787cf0f0f
  | 2 => 0x7f8700ff0e01fe1c03fc3807f8700ff0
  | 3 => 0x8007ff000ffe001ffc003ff8007ff000
  | _ => 0

def minor4xfe64Neg : Nat → Bits
  | 0 => 0x553456aa68ad54d15aa9a2b553456aa6
  | 1 => 0x542454a848a9509152a122a542454a84
  | 2 => 0x660500cc0a0198140330280660500cc0
  | 3 => 0x42a8008550010aa0021540042a8008
  | _ => 0

def minor4xfe64Atlas : Atlas := ⟨6, rawDecor 15 minor4xfe64Pos minor4xfe64Neg, 0xfe64fe64fe64fe64, minor4xfe64N, minor4xfe64R, minor4xfe64H, minor4xfe64I, 11, [(0xff00ff00ff00ff, 4), (0xff00ff00ff00ff0, 4), (0x3333333333333333, 4), (0x33cc33cc33cc33cc, 4), (0x3c3c3c3c3c3c3c3c, 4), (0xa5a5a5a5a5a5a5a5, 4), (0xf0f0f0f0f0f0f0f0, 4), (0x3c003c003c003c, 3), (0xa500a500a500a5, 3), (0xf000f000f000f0, 3), (0x30c030c030c030c, 3)]⟩

def minor4xfe90K5 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def minor4xfe90N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def minor4xfe90R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt minor4xfe90K5 (i*4) 4
  | _ => 0

def minor4xfe90H (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt minor4xfe90K5 (4+i*1) 1
  | _ => 0

def minor4xfe90I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt minor4xfe90K5 (6+((h/1+packedAt minor4xfe90K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor4xfe90Pos : Nat → Bits
  | 0 => 0x14f853e14f853e14f853e14f853e14f8
  | 1 => 0x27389ce27389ce27389ce27389ce2738
  | 2 => 0xf83fe0ff83fe0ff83fe0ff83fe0ff83f
  | 3 => 0x3fc0ff03fc0ff03fc0ff03fc0ff03fc0
  | _ => 0

def minor4xfe90Neg : Nat → Bits
  | 0 => 0x945a516945a516945a516945a516945a
  | 1 => 0x252c94b252c94b252c94b252c94b252c
  | 2 => 0xb036c0db036c0db036c0db036c0db036
  | 3 => 0xa802a00a802a00a802a00a802a00a80
  | _ => 0

def minor4xfe90Atlas : Atlas := ⟨5, rawDecor 15 minor4xfe90Pos minor4xfe90Neg, 0xfe90fe90fe90fe90, minor4xfe90N, minor4xfe90R, minor4xfe90H, minor4xfe90I, 1, [(0xff00ff00ff00ff0, 6)]⟩

def minor5xfffefc80K4 : Nat → Nat
  | 0 => 0x3033130b2331b3280000a0008800180014000d00029b19542486e46150921ba18142486746550521b918941486f06050521
  | _ => 0

def minor5xfffefc80K5 : Nat → Nat
  | 0 => 0x1410c34f169049950582404a15d1c1d75743818d9757575740c6c7975757574acb574a4c174214488943cd574e9753c517570f97508cd7575757574ed75757454e0f41061252c0164b040c4d080151959753174b8dd116048704d289c694c7d6d00c8a955480885147444645c8d35202cfd3830bd74e42891440830cbc086081c783020990f000410e101838f0002c00100009000400024001200080005000280018000a00058002400100000000700040001a000200010000c00040003000300018000e000900048001c000c000b000400024001000090004800200000000c0006000280014001000050002c001200080008800080004000300010000c00080004000280024001200050002000000014000e0005800200012000800040003000180001000480020001800100000800240010000c0008000300018000c00090001400080005000480024000e0007000280015fd5142bfa9a857e5350afaa6a15f14d42dfa1a85bd4350afea4a17bd0942df21285ec4250b7884a17b8c942f6992857f5150afca2a15f14542f790a85fb5050afea0a15ed4142bf282857d5050bf0a0a15f14142bc28285fa3050bf260a17bc8142f6902857f54506fea6a0df94d41bea9a837c535077e86a0ef50d41bfa92837e52506f8a4a0dfd4541fba0a83be41507e882a0ef10541fb18a83f531507ec42a0fed4141bfa82837b50506fca0a0df54141fc282837c50506f0a0a0fe8c141fc98283f710507ea20a0dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690dfd4921f721243ed42487dc6490fb4c921bfa8a43f641487ea8290fd8c521fa98a43f721487dc4290fd08521f610a43e421486fea090df94121bea82437c50487f46090fe4c121f710243ec20487ec2090fd04121
  | _ => 0

def minor5xfffefc80K6 : Nat → Nat
  | 0 => 0x4c51b4868f1f5450b223041181321c8831a9c49c2aa8e862484b8054a932a4015529503150254a928b1e1040e540582c0280101005444456054444580544446806111144444433332222ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0

def minor5xfffefc80K7 : Nat → Nat
  | 0 => 0x21f
  | _ => 0

def minor5xfffefc80N (k : Nat) : Nat :=
  match k with
  | 4 => 6
  | 5 => 93
  | 6 => 42
  | 7 => 1
  | _ => 0

def minor5xfffefc80R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfffefc80K4 (i*38) 38
  | 5 => packedAt minor5xfffefc80K5 (i*27) 27
  | 6 => packedAt minor5xfffefc80K6 (i*16) 16
  | 7 => packedAt minor5xfffefc80K7 (i*5) 5
  | _ => 0

def minor5xfffefc80H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfffefc80K4 (228+i*17) 17
  | 5 => packedAt minor5xfffefc80K5 (2511+i*17) 17
  | 6 => packedAt minor5xfffefc80K6 (672+i*4) 4
  | _ => 0

def minor5xfffefc80I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfffefc80K4 (334+((h/1+packedAt minor5xfffefc80K4 (330+(h % 1)*4) 4) % 15)*4) 4
  | 5 => packedAt minor5xfffefc80K5 (4253+((h/23+packedAt minor5xfffefc80K5 (4092+(h % 23)*7) 7) % 120)*8) 8
  | 6 => packedAt minor5xfffefc80K6 (900+((h/10+packedAt minor5xfffefc80K6 (840+(h % 10)*6) 6) % 52)*7) 7
  | 7 => packedAt minor5xfffefc80K7 (6+((h/1+packedAt minor5xfffefc80K7 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor5xfffefc80Pos : Nat → Bits
  | 0 => 0x24f667893d99e24f667893d99e24f667
  | 1 => 0x47087f11c21fc47087f11c21fc47087f
  | 2 => 0x780f871e03e1c780f871e03e1c780f87
  | 3 => 0x800ff8e003fe3800ff8e003fe3800ff8
  | 4 => 0xfff000fffc003fff000fffc003fff000
  | _ => 0

def minor5xfffefc80Neg : Nat → Bits
  | 0 => 0x247663891d98e247663891d98e247663
  | 1 => 0x45282d114a0b445282d114a0b445282d
  | 2 => 0x684a861a12a18684a861a12a18684a86
  | 3 => 0x800550a001542800550a001542800550
  | 4 => 0x12800044a000112800044a0001128000
  | _ => 0

def minor5xfffefc80Atlas : Atlas := ⟨7, rawDecor 31 minor5xfffefc80Pos minor5xfffefc80Neg, 0xfffefc80fffefc80, minor5xfffefc80N, minor5xfffefc80R, minor5xfffefc80H, minor5xfffefc80I, 9, [(0x5555aaaa5555aaaa, 7), (0x9999999999999999, 7), (0xa5a5a5a5a5a5a5a5, 7), (0xff00ff00ff00ff, 6), (0xffff0000ffff, 5), (0xf0f0f0f0f0f0f0f, 5), (0xf0ff0f00f0ff0f0, 5), (0x3333333333333333, 5), (0xaaaaaaaaaaaaaaaa, 5)]⟩

def minor5xfffcfa80K4 : Nat → Nat
  | 0 => 0x5900cc1940481561d548d59628058444b5960895964ce3c08a80d9763c554854872e20904079ed815390a786054e429dd875350a3c6550d42e54c54350a7665145429dd85548ca7461552329ed83544ca7761551329d185544ca7b60551329e181544ca5c6550d32e6501434ca6c6550932e350d424ca7a65141329dd95428c6746550a319ed953290278654ca40
  | _ => 0

def minor5xfffcfa80K5 : Nat → Nat
  | 0 => 0xc0011000300010000800040002000700008001000080004000200004000200010000a0006000e00074000c001000088000c00060003000100010000a000200028001c0010001d000b00064000e001700048005c0012fea8a1dfd4d43efa1a87be4350fb886a1ef10d43bfa92877c5250f7e84a1f7cc943bfa8a877e5150efaa2a1df14543ef98a87dd3150efea0a1df94143bea82877c5050f7e80a1ef50143beaa4857e5390afaa7215f14e42bf29485ef4290b7e85217b10a42bfa8c857e5190afaa3215f14642f790c85ed2190afea1215f94242bea84857c5090afea8a15fd4d42bf29a857c5350b7e86a16f50d42bfa9285ef4250b7c84a17b10942de21285f75150afea2a15dd4542bf28a857d5150be8a2a15f14542ba28a85ef2150bda42a15fd4142bf282857d5050af8a0a15fd5232bf2a4657d548caf8a9195f54e32bf29465ee428cbda85197bcca32ef99465ec328cafea3195f94632bea8c657c518cafea1195f94232bea84657c508cbde41197b48232bfaa2657e544cafaa8995f15132bfa9a65de434cbba86995fd4932f721265ed424cbde6499778c932f619265dc324cafea2995f94532bea8a657c514cbf6a0995fd4132bda82657e504cafaa0997e14132be2826578504cbde40997b48132fbaa463f6548c7eaa918fd15231baa9c63f7438c7ec8718fd50e31fa21c63f7528c7eca518fd54a31fa29463f7428c7ec8518fd50a31fa21463f7328c7ec6518fd4ca31fa19463f7508c7eca118fd54231fa28463f7408c7ec8118fd50231fa20463f7308c7ec6118fd4c231fa18463f7208c7ec4118fd48231fa10463f7544c7eca898fd55131fa2a263f7534c7aea698ddd4d31fba1a63f6434c7ac8698fd50d31eaa1a63f4434c7eea498fd94931faa9263f4524c7ee8498fd90931faa1263f4424c7ee6498fd8c931fa99263f4324c7eea098fcd4131fb28263f5504c7e8a098fc14131fba0263f6404c7ea8098fd10131fb98263f6304c7ea6098fd0c131fb90263f6204c7ea4098fd08131bcaa481fb53903f4a7207e54e40fc29c81fb43903f487207e50e40fc21c81fb52903f4a5207e54a40fc29481fb42903f485207e50a40fc21481fb32903f465207e4ca40fc19481fb51903f4a3207e54640fc28c81fb41903f483207e50640fc20c81fb31903f463207c8c640fc98c81f131903f063207ec8640fd10c81f921903f043207ed5140ddaa2817b54503f6a6a07e94d40fca9a81f853503f686a06ed0d40fd21a81f9435037286a07e10d40fda9281fa52503f2a4a07e14940fda1281fa42503f284a07e10940fd99281fa32503f264a07e0c940fda8a81f351503f4a2a07e54540fc28a81f051503f682a07e90540fca0a81f841503f662a07e8c540f918a81f931503e262a07e0c540fd90a81fa21503f242a07e08540
  | 1 => 0x260a50a8f53648c3c8101e846310ba1ac041eca71285d1a43c18c841e4e5030c9418f431c1d0e5083e8e33a8b1368c84143e220310905f32cfd070bb178672010f1a8a0158a3038d40c01f3a0e2034ee3ac3a1b003004de250261491331809451161d0bf2f80f459163cca82a447134a440092264cf19051254b516c9f3300b37c901b460459162710c409162051642478348dd044db2d005168d14049638020008c5285160bc8d1bcef140cd328a60588a4342b238343e42515c321391612c85458e142916458770d42d154b24484145916188330200739cff458f108516018c1120ce3dc124587e3f8763c116458fb354ac440b3218220a0b613c750fd1110c820b0142e0dc04c5c4589a0607045897459163f115391160ec1a360c2054e60789d3b4e9340370a4b9064c34584421c930b86e150bd0d8ae2f0721090b3007d0f50441c000281720c7c1a0451c4af185033b0f82b4d714ca2130382ac1b1010e2789b2a8b734c66124d6160f62c07308c8f244271948b1fc891646749800ac450230c0410028140c08090e8120048220040101930260387110822609804582d02860a60000050802a0681c4411238281e5a1a9c0021c0117c185e18060203b008741427070480031000100008000400030001000080000001000010000c001600040002800100007000b00050001c001000070001400280004000300000000c00040002000100008000a00040005800120017000b00040001c0014000700010000000060003000100000000400020008000080004000d00058002c000800050000000100009000b800580028000e00080003800400004000000010000c0006001000000000c000600030003000100016000400048001c00140007800540028000000020000000080006000300000000c0000000000018004000060003000580010000c000400078002800140007000480000000e0007800540028000900020002400080007000200018000e00040004000200010000900020000000020004000300018000c00070001000240006000300028003c002a0004000380008000c0007000a8003c002a000e000680010001a0004000300020000e0004000300018000c00190002000300018000c00068001000300019000200018000c0006000300030001a000300018000c0006000500078005400080006000380008000e0015000780054001c0004000780018001e000600020001000080004000700038001c000e0002000100008000500030000000020007000180024000600020002800080008000500038002000460016000c8001c002e0009000b800200008000e00020004400
  | _ => 0

def minor5xfffcfa80K6 : Nat → Nat
  | 0 => 0x10b161912a161e58609ac58a80ac38b0a02221d62344aceac343422c183c3205899605005962458b162c580d61736a561f243852c169c82158b162c2ab162c589430200080c005000400023022002300324b2340b03b4b4270a0237a3a7a71111ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40fe40fa40fd40f940fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0

def minor5xfffcfa80K7 : Nat → Nat
  | 0 => 0x21f
  | _ => 0

def minor5xfffcfa80N (k : Nat) : Nat :=
  match k with
  | 4 => 22
  | 5 => 278
  | 6 => 44
  | 7 => 1
  | _ => 0

def minor5xfffcfa80R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfffcfa80K4 (i*38) 38
  | 5 => packedAt minor5xfffcfa80K5 (i*27) 27
  | 6 => packedAt minor5xfffcfa80K6 (i*16) 16
  | 7 => packedAt minor5xfffcfa80K7 (i*5) 5
  | _ => 0

def minor5xfffcfa80H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfffcfa80K4 (836+i*4) 4
  | 5 => packedAt minor5xfffcfa80K5 (7506+i*17) 17
  | 6 => packedAt minor5xfffcfa80K6 (704+i*4) 4
  | _ => 0

def minor5xfffcfa80I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfffcfa80K4 (949+((h/5+packedAt minor5xfffcfa80K4 (924+(h % 5)*5) 5) % 31)*6) 6
  | 5 => packedAt minor5xfffcfa80K5 (12853+((h/69+packedAt minor5xfffcfa80K5 (12232+(h % 69)*9) 9) % 303)*10) 10
  | 6 => packedAt minor5xfffcfa80K6 (957+((h/11+packedAt minor5xfffcfa80K6 (880+(h % 11)*7) 7) % 74)*7) 7
  | 7 => packedAt minor5xfffcfa80K7 (6+((h/1+packedAt minor5xfffcfa80K7 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor5xfffcfa80Pos : Nat → Bits
  | 0 => 0xff463023fd18c08ff463023fd18c08ff
  | 1 => 0xc7883fc31e20ff0c7883fc31e20ff0c7
  | 2 => 0x70fc0fc1c3f03f070fc0fc1c3f03f07
  | 3 => 0xf8f000ffe3c003ff8f000ffe3c003ff8
  | 4 => 0xffff0003fffc000ffff0003fffc000
  | _ => 0

def minor5xfffcfa80Neg : Nat → Bits
  | 0 => 0x5b4630216d18c085b4630216d18c085b
  | 1 => 0xc58817c316205f0c58817c316205f0c5
  | 2 => 0x160a8268582a09a160a8268582a09a16
  | 3 => 0xa09004928240124a09004928240124a0
  | 4 => 0x6528000194a00006528000194a0000
  | _ => 0

def minor5xfffcfa80Atlas : Atlas := ⟨7, rawDecor 31 minor5xfffcfa80Pos minor5xfffcfa80Neg, 0xfffcfa80fffcfa80, minor5xfffcfa80N, minor5xfffcfa80R, minor5xfffcfa80H, minor5xfffcfa80I, 17, [(0x9999999999999999, 7), (0xffff0000ffff, 5), (0xff00ff00ff00ff, 5), (0x3333333333333333, 5), (0x3333cccc3333cccc, 5), (0x33cc33cc33cc33cc, 5), (0x5555555555555555, 5), (0x5555aaaa5555aaaa, 5), (0x55aa55aa55aa55aa, 5), (0xaaaaaaaaaaaaaaaa, 5), (0xcccccccccccccccc, 5), (0x33cc000033cc, 4), (0xc3c30000c3c3, 4), (0x5500aa005500aa, 4), (0xa500a500a500a5, 4), (0x909090909090909, 4), (0x1111111111111111, 4)]⟩

def minor5xfffceaa8K6 : Nat → Nat
  | 0 => 0x43f
  | _ => 0

def minor5xfffceaa8N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def minor5xfffceaa8R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt minor5xfffceaa8K6 (i*5) 5
  | _ => 0

def minor5xfffceaa8H (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt minor5xfffceaa8K6 (5+i*1) 1
  | _ => 0

def minor5xfffceaa8I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt minor5xfffceaa8K6 (7+((h/1+packedAt minor5xfffceaa8K6 (6+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor5xfffceaa8Pos : Nat → Bits
  | 0 => 0xff2241ff2241ff2241ff2241ff2241ff
  | 1 => 0x93447e93447e93447e93447e93447e93
  | 2 => 0x1c878f1c878f1c878f1c878f1c878f1c
  | 3 => 0xe0f80fe0f80fe0f80fe0f80fe0f80fe0
  | 4 => 0xfff000fff000fff000fff000fff000
  | _ => 0

def minor5xfffceaa8Neg : Nat → Bits
  | 0 => 0x25224025224025224025224025224025
  | 1 => 0x92441692441692441692441692441692
  | 2 => 0x18848b18848b18848b18848b18848b18
  | 3 => 0xc0c80dc0c80dc0c80dc0c80dc0c80dc0
  | 4 => 0x336000336000336000336000336000
  | _ => 0

def minor5xfffceaa8Atlas : Atlas := ⟨6, rawDecor 31 minor5xfffceaa8Pos minor5xfffceaa8Neg, 0xfffceaa8fffceaa8, minor5xfffceaa8N, minor5xfffceaa8R, minor5xfffceaa8H, minor5xfffceaa8I, 1, [(0xffff0000ffff, 6)]⟩

def minor5xfff8eca0K4 : Nat → Nat
  | 0 => 0x3013020e002211116346511d2689094444861b441480e448850f445c59e1208aa2407c18d0e8c401104068200024001b000420004000160004c000c000800068000d8001800078001b000300048001000058000d0000c00000000c000000024001b0000400170003400080006800130004000020002c000b9ed8152d0e786054b43cd9905150f356414543d5d0c5150f544314543d5cc85150e776154f429d18553d0b3a6414142ce5905050b6b4214142da1085050b6a32141429d984544ca7561151329e980544ca79601513297195434cad46150d329b195424cae860509329ed81521067860548419d986548867a60952219e58254886776154c409d185531027661952309d586548c27a60952309d986540427a6095010
  | _ => 0

def minor5xfff8eca0K5 : Nat → Nat
  | 0 => 0x60005800680022000e000680034001b0002000c00038001c000d00010000000040019000300064000c000b000d00044001a000d000680038001d00068003000140000000000060000800180003000c8000c001000130008800080036000e0001000080004000280034001a0022000e0005000000000000a000500008002a0002000500004003200010005800680023000480020002c0036000e8003400180014000a00050002afca9a1df54f43ef21e87be43d0f7887a1df94b43bea96877c52d0efea3a1df94743bea8e87bf41d0f7a83a1f78c743ee18e877f50d0efca1a1df54343bfaa2877f5350fbe86a1ef90d43ee21a87bc4350efea4a1df94943be29287df3250feea2a1dfd4543bba8a877d5150fe8a2a1df14543ba28a87bf4150f7a82a1dfd4143bea82877c5050efca9a15f94f42bea9e857c53d0afaa5a17b90b42df21685bc42d0afea3a15f94742bea8e857f50d0afca1a15f54342dfa0685bd40d0bdc41a17b08342bfaa2857f5350afca6a15f14d42bfa9285ef4250b7c84a17b10942de21285ee3250afea2a15f54542be28a85fb5050afea0a15ed4142bea8285f85050af8a0a15e14142dfa0285bd4050afea8995f95132beaa2657c544cafea6997790d32eea1a657f524cbdc84997b50932f799265de324cbd86499770c932bfa8a657d514caf8a299778c532ee18a65ef214cbda42995fd4132bea82657c504cbbe6099774c132f710265ec204cafaa920dfd4e41bf29c837d53906f8a720df94a41bea94837c52906fca320fdd0641dfa0c83bd41907ec6320fd4c641fa90c837f50906fca120df54241fb084837e54106fea620df94c41bea98837c53106fca420df54841be290837e511077e8220fd90441faa0883bd41107ee6220fd0c441bfa80837e50106faa020dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21bf28c43f641887ea8310fdcc621fa18c43f721887de4310fb48621fa10c437f50886fca110df54221fb88443f510886faa9205f94e40bea9c817c53902fea5205f94a40bea94817c52902fea3205f94640bea8c817e50903f681206fd0240dea0481f930903f441207e48240fd884817e54102fca6205f54c40be298817f52102fca4205f54840be290817f51102fca2205f54440bf28081bf40103f480207e50040dea0081fb20103f040205fd5230bf2a4617d548c2f8a9185f54e30bfa94617e528c2faa5185f14a30bfa8c617e518c2faa3185f94230fd20461f9408c3f6611877cc230ee98461f8308c3f641187e08230fd08461f9108c2fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2087d90410faa0821f731043e862085f94010fd20021f940043f640087e08010fb88021fa10043f220087d44010
  | 1 => 0x3f9a2237f318cab153134d2fe1a3c8aed9503f81ceb183b59c0806abd3e0f1b31546fe1c3cca8996904ccec4248edfccd063f8a6557f3f8a20b5fbf5fc5b543dcb8ad7f321364c4e100a05222b0d041d25a95740a750b9ecdf23191c2cb5b91d30927130998e0439f822033da30b4b660b9cf4dd00928c4ac453b9aa1e389d06efe3798dd0441caf5163d5cbf842e954bd0fafe7893c002f72a40e6db723edfca115181ccaa0c9855cc9190992e0714a157675092d148b3680adb8ec0c3f82c770b90cec02639b0b288510a020d80d0fc82096d09cdc8e783f93a4216be83e1b3fac8f25e71bbd6afe36a4dfc917f13912784f081fc584b2e048223585500ab24159f8f87f379fc9a020d44a2c433f9fcf97f211fcfe7aa3d06ca3834d28687f17428061f2c062d76017c38bc469c80afe5f255fc7c1d3519e663529d02fe19b5878fe01800350480132ab2b81c0e9a012048ebd00858000d0f8480614001482a0d1200c0469040580000088003c03008bc0c070f1743a150001c1224068004c02020d000000900400550002000100008000400020000c000000030004000500023001180088005400080002000d80008000800040002800100008000400000000c0007000300028004400220005000280054000100118008800080004001b00030000c00000003000300018000c000600008006800020009000c0003a001d000e000c80018000c000000018000c000c0007000300018000d000300008000400340007000700038000e0007000c80002001d000e000000000000a0000000180010000000030003000000006000300018000c00020001000900054000800068000800080004001600024000800320006000880014000800140002000040000000100088004000200010000a000460002000b000d8003800220010000a80010002a000400008000000020010000800040002200118002400100016001b00070001c0000000000078003c000600150001800040002001a0008c00120008000100008000400020009000b8003a001d000e00070000800000002000380018003000
  | _ => 0

def minor5xfff8eca0K6 : Nat → Nat
  | 0 => 0x2922850a05952c38d201a950803c3d4064c5040208494272e4419b44254013e1ce0c264119d50614190a3515c81800a8945010040180618c04882202562430021701c020042365c6745c0ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0

def minor5xfff8eca0K7 : Nat → Nat
  | 0 => 0x21f
  | _ => 0

def minor5xfff8eca0N (k : Nat) : Nat :=
  match k with
  | 4 => 34
  | 5 => 254
  | 6 => 40
  | 7 => 1
  | _ => 0

def minor5xfff8eca0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfff8eca0K4 (i*38) 38
  | 5 => packedAt minor5xfff8eca0K5 (i*27) 27
  | 6 => packedAt minor5xfff8eca0K6 (i*16) 16
  | 7 => packedAt minor5xfff8eca0K7 (i*5) 5
  | _ => 0

def minor5xfff8eca0H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfff8eca0K4 (1292+i*18) 18
  | 5 => packedAt minor5xfff8eca0K5 (6858+i*17) 17
  | 6 => packedAt minor5xfff8eca0K6 (640+i*5) 5
  | _ => 0

def minor5xfff8eca0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt minor5xfff8eca0K4 (1952+((h/8+packedAt minor5xfff8eca0K4 (1904+(h % 8)*6) 6) % 43)*7) 7
  | 5 => packedAt minor5xfff8eca0K5 (11743+((h/63+packedAt minor5xfff8eca0K5 (11176+(h % 63)*9) 9) % 287)*9) 9
  | 6 => packedAt minor5xfff8eca0K6 (900+((h/10+packedAt minor5xfff8eca0K6 (840+(h % 10)*6) 6) % 48)*7) 7
  | 7 => packedAt minor5xfff8eca0K7 (6+((h/1+packedAt minor5xfff8eca0K7 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor5xfff8eca0Pos : Nat → Bits
  | 0 => 0xe1fcc087cf87f3021f3e1fcc087cf87f
  | 1 => 0xffc10307f3ff040c1fcffc10307f3ff0
  | 2 => 0x1fe03f83c07f80fe0f01fe03f83c07f
  | 3 => 0xfe03fc003ff80ff000ffe03fc003ff80
  | 4 => 0x3ffffc0000fffff00003ffffc0000
  | _ => 0

def minor5xfff8eca0Neg : Nat → Bits
  | 0 => 0xc0e4d083470393420d1c0e4d08347039
  | 1 => 0x7791032591de440c9647791032591de4
  | 2 => 0x51a013038146804c0e051a013038146
  | 3 => 0x880258002e20096000b880258002e200
  | 4 => 0x1021a2c60040868b1801021a2c600408
  | _ => 0

def minor5xfff8eca0Atlas : Atlas := ⟨7, rawDecor 31 minor5xfff8eca0Pos minor5xfff8eca0Neg, 0xfff8eca0fff8eca0, minor5xfff8eca0N, minor5xfff8eca0R, minor5xfff8eca0H, minor5xfff8eca0I, 27, [(0x3c3c3c3c3c3c3c3c, 6), (0x55aa55aa55aa55aa, 6), (0xf00ff00ff00ff00f, 6), (0xff00ff00ff00ff, 5), (0xffff0000ffff00, 5), (0xf0f0f0f0f0f0f0f, 5), (0xf0ff0f00f0ff0f0, 5), (0x33cc33cc33cc33cc, 5), (0x5a5a5a5a5a5a5a5a, 5), (0x6666666666666666, 5), (0x9999999999999999, 5), (0xaa55aa55aa55aa55, 5), (0xaaaa5555aaaa5555, 5), (0xaaaaaaaaaaaaaaaa, 5), (0xc3c3c3c3c3c3c3c3, 5), (0xcccc3333cccc3333, 5), (0xcccccccccccccccc, 5), (0x3c003c003c003c, 4), (0x99009900990099, 4), (0xcc003300cc0033, 4), (0xcc00cc00cc00cc, 4), (0x50a050a050a050a, 4), (0x909090909090909, 4), (0xa0a05050a0a0505, 4), (0xa0a0a0a0a0a0a0a, 4), (0x2211221122112211, 4), (0x4141414141414141, 4)]⟩

def minor5xfff8cc80K5 : Nat → Nat
  | 0 => 0xb125c7d12e0ab958d2e6938336b8f135ab8c210e904ae5c50aae40987ae1c7061954b082310a40a81694e9108283020038b08d06114c09d01249b6d2492fff2496dbb7649249b6e49b7ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fd20fc20ff10fb10fe10fd10fc10f810
  | _ => 0

def minor5xfff8cc80K6 : Nat → Nat
  | 0 => 0x21f
  | _ => 0

def minor5xfff8cc80N (k : Nat) : Nat :=
  match k with
  | 5 => 46
  | 6 => 1
  | _ => 0

def minor5xfff8cc80R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt minor5xfff8cc80K5 (i*16) 16
  | 6 => packedAt minor5xfff8cc80K6 (i*5) 5
  | _ => 0

def minor5xfff8cc80H (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt minor5xfff8cc80K5 (736+i*3) 3
  | _ => 0

def minor5xfff8cc80I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt minor5xfff8cc80K5 (940+((h/11+packedAt minor5xfff8cc80K5 (874+(h % 11)*6) 6) % 55)*7) 7
  | 6 => packedAt minor5xfff8cc80K6 (6+((h/1+packedAt minor5xfff8cc80K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor5xfff8cc80Pos : Nat → Bits
  | 0 => 0x619e67986799e619e67986799e619e67
  | 1 => 0x861fff2187ffc861fff2187ffc861fff
  | 2 => 0x7e387c1f8e1f07e387c1f8e1f07e387
  | 3 => 0xf803f8fe00fe3f803f8fe00fe3f803f8
  | 4 => 0xfffc00ffff003fffc00ffff003fffc00
  | _ => 0

def minor5xfff8cc80Neg : Nat → Bits
  | 0 => 0x618e63986398e618e63986398e618e63
  | 1 => 0x8614ad21852b48614ad21852b48614ad
  | 2 => 0x2a386c0a8e1b02a386c0a8e1b02a386
  | 3 => 0x280350ca00d43280350ca00d43280350
  | 4 => 0xd558003556000d558003556000d55800
  | _ => 0

def minor5xfff8cc80Atlas : Atlas := ⟨6, rawDecor 31 minor5xfff8cc80Pos minor5xfff8cc80Neg, 0xfff8cc80fff8cc80, minor5xfff8cc80N, minor5xfff8cc80R, minor5xfff8cc80H, minor5xfff8cc80I, 7, [(0x33cc33cc33cc33cc, 6), (0xff00ff00ff00ff, 5), (0xf0f0f0f0f0f0f0f, 5), (0x9999999999999999, 5), (0xaaaa5555aaaa5555, 5), (0xaaaaaaaaaaaaaaaa, 5), (0xcccccccccccccccc, 5)]⟩

def minor5xfffcfa00K5 : Nat → Nat
  | 0 => 0x43f
  | _ => 0

def minor5xfffcfa00N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def minor5xfffcfa00R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt minor5xfffcfa00K5 (i*5) 5
  | _ => 0

def minor5xfffcfa00H (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt minor5xfffcfa00K5 (5+i*1) 1
  | _ => 0

def minor5xfffcfa00I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt minor5xfffcfa00K5 (7+((h/1+packedAt minor5xfffcfa00K5 (6+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def minor5xfffcfa00Pos : Nat → Bits
  | 0 => 0x4f4b324f4b324f4b324f4b324f4b324f
  | 1 => 0x8c8c3f8c8c3f8c8c3f8c8c3f8c8c3f8c
  | 2 => 0xf00fc3f00fc3f00fc3f00fc3f00fc3f0
  | 3 => 0xfff003fff003fff003fff003fff003ff
  | 4 => 0xfffc00fffc00fffc00fffc00fffc00
  | _ => 0

def minor5xfffcfa00Neg : Nat → Bits
  | 0 => 0x454b32454b32454b32454b32454b3245
  | 1 => 0x8c8c178c8c178c8c178c8c178c8c178c
  | 2 => 0xd00d42d00d42d00d42d00d42d00d42d0
  | 3 => 0x2a90012a90012a90012a90012a90012a
  | 4 => 0x62a80062a80062a80062a80062a800
  | _ => 0

def minor5xfffcfa00Atlas : Atlas := ⟨5, rawDecor 31 minor5xfffcfa00Pos minor5xfffcfa00Neg, 0xfffcfa00fffcfa00, minor5xfffcfa00N, minor5xfffcfa00R, minor5xfffcfa00H, minor5xfffcfa00I, 1, [(0x3333333333333333, 5)]⟩

def mainK5 : Nat → Nat
  | 0 => 0x2080014000e9c92eb12c2908818e4875896148440
  | _ => 0

def mainK6 : Nat → Nat
  | 0 => 0xf21dc9611033b48772584408ff80dc9611023fa0372584408fd80dc9611023f20372584408fe87dd9211027e20376484408ff83dd9211023fa0f76484408fd83dd9211023f20f76484408ff82dd9211023fa0b76484408fd82dd9211023f20b76484408ff81dd9211023fa0776484408fd81dd9211023f20776484408ff80dd9211023fa0376484408fd80dd9211023f2037648440cfa10dd9211033e44376484408ff865d92110277e0d76484409dc835d9211027e20176484409ec8758921102bbe196248440cec7658921103b99856248440de870589211033be1d6248440cec8758921102bb21d62484408ec87589211033bdcd6248440ced7358921103b9e056248440aee8158921103b92056248440aec8158921103b9dc56248440cef7158921103bae016248440ee88058921103badc16248440cee70589211033b1c16248440ee910589211027d21d6148440af786585211033d1d96148440ee66258521103b95896148440df070585211033de1d6148440cf48758521102bd21d61484408f487585211033ddcd6148440cf57358521103b9e096148440af68258521103b92096148440af48258521103b9dc96148440cf77258521103bcdc16148440cf670585211033d1c161484409fa871c121102be6187048440cfa761c1211033e5d87048440dbb741c1211036e1d07048440ee9621c121103bc58470484408ff87991210c23fa1e64484308fd87991210c23f21e6448430cdf73991210c3371ce64484308ff835c4648823fa0d71192208fd835c4648823f20d71192208ff825c4648823fa097119220cf7815c4648833d8c57119220cf5315c4648833d8857119220cf5215c4648823fe0171192208fe805c4648823f60171192208fc805c4648833d8417119220cf4105c4648823f61e7558420c7f759d561082bd60675584208fe871d5610831f9d47558420c7d751d561082bda047558420af5811d5610839d54475584208ff835c8648423fa0d72192108fd835c8648423f20d7219210cef825c8648423fe097219210cee325c8648433b4c972192108ff815c8648423fa0572192108fd815c8648423f2057219210cef215c8648433b48572192108ff805c8648423fa0172192108fd805c8648423f2017219210cee205c8648433b0817219210cfb865c8408427ee1972102109f9865c8408433e21972102109fa845c8408436e21172102109f8845c8408426e2117210210deb825c8408427ee097210210deb625c8408433e9897210210de8625c8408433e1897210210dea525c8408437a5497210210deb425c8408436e9097210210de8425c8408436e1097210210dea325c8408437a4c972102109fa815c8408427e2057210210df1615c8408433e5857210210dbb415c8408436e5057210210deb215c8408437a4857210210
  | 1 => 0x4dd9211423fa1376484508fd84dd9211423f21376484508ff83dd9211423fa0f76484508fd83dd9211423f20f76484508ff82dd9211423fa0b76484508fd82dd9211423f20b7648450c7f52dd9211431f54b76484508ff81dd9211423fa0776484508fd81dd9211423f20776484508fe80dd9211423f2037648450cfb40dd9211433e1037648450c7f855d9211423fe1576484508fe855d9211423f6157648450c7c855d9211423f215764845087c855d9211423fe1176484508fe845d9211423f61176484508fc845d9211423fe0d76484508fe835d9211423f60d76484508fc835d9211433be0976484508ff825d9211433de0576484508ff815d9211423fa0176484508fc805d9211433de1d6148450cf48758521142bd21d61484508f487585211439de156148450e7485585211439ddd56148450cf675585211439d1d56148450cf475585211431d1d56148450cf774585211433d5d16148450cf673585211433d1cd6148450e7653585211439d14d6148450ee78258521142bda096148450ee48258521142bd2096148450ee772585211433ddc96148450e7752585211439d5496148450cf670585211433d1c16148450ef34058521143bc10161484508ff865c8531023fa197214c408fc865c8531033b9897214c409fb805c8531027e2017214c40d78505c8531023f61b71588408fc86dc5621033d98771588409fb80dc5621027e20371588408fe871cd621032f1d07358840cde731cd62103375cc7358840aee821cd62102bb6087358840ecd321cd621033e1c073588408ff8714d621023fa1c53588408fd8714d621023f21c5358840cdf7314d62103371cc5358840aee8214d62102bb6085358840cf87014d621023fe0f71588408fe83dc5621023f60f71588408fc83dc5621023f60b7158840cf581dc5621033dcc77158840cf431dc5621033d8877158840cf521dc5621023fe0371588408fe80dc5621023f60371588408fc80dc5621023fe1576cc8408fe855db321023f61576cc8408fc855db321023fe1176cc8408fe845db321023f61176cc8408fc845db321023fe0d76cc8408fe835db321023f60d76cc8408fc835db3210337d0d76cc840cbe435db321033710d76cc840cbc435db321023fe0976cc8408fd825db321033b8c976cc840ced325db321023fe0576cc8408fe815db321023f60576cc8408fc815db3210337cc576cc840cdd315db321023fe0176cc8408fe805db321023f60176cc8408fc805db321023f61b72584408fc86dc9611033b98b72584409fa80dc9611027e60372584408fc87589611033bdc96258440cec7258961102bde056258440af48158961102be2016258440ee82058961103bc84162584408ff83dc9611023fa0f72584408fd83dc9611023f20f7258440ced82dc9611023f6077258440ce
  | 2 => 0xe0001c000280044000000009000128000c00008000920010c000880013000200002000240002600010000ec00108001b0004600098001400038003a000720001c00020000720006000e60002800040000e000100003b00020001b800498001300020002c00007000080001c00020001800040000600010000140000e000100002000100001800040000740012800260005a000800010000250004a000800088000100030000044001e800200001c000200007000090002a00040003400048000120004000e48001800302000480014000480009000080001c0002000070001b4000a80015000200003800040000e00010001200014000200007000080001c000100003000054000a800100002a0004000080000e000100003800068001600010003040010800380005200040000c0004d0002000120002680010000200005400128002000390000540008000110003a0005800070002e0001c0003800070000900030000400026000e0000000012000240004800030000740012800200040000070007000019000220005800070000e00010000280014000480016c000a000a4001c8003f0001400034000b0000a800080001c000200007000080001d80010000200012c000b8002300020002c00007000080001c0003800070000800066000c000840003000086000c400080001b0006000080001c0002000070001200027800270004c00040000b000100002c0005800080000e000100003800070000e000120030000268002d0005000030000400008000100012000240004a0003000128000f800370006a000ac000e8002b0003e0009c00100001000028000300007000160002c00058000b1fe1a7598d21c7e869d6634871f61a7598d21c7c869d6634871fd927598d21c7e649d6634871f5927598d21c7c649d6634871fd8e7598d21c7e639d6634871f58e7598d21c7c639d6634871fd8a7598d21c7f619d6634875dc867598d21d6e219d6634875d0867598d21d6c219d6634871fd827598d21c7e609d6634871f5827598d21c7c609d6634863f61a7498d21cbe649d2634872f5927498d21cdf639d2634873718e7498d21cf4865c7324867d21971cc9218f4865c7324873d99571cc921cf4655c73248775d8d71cc921cf6635c7324877518d71cc921cf4635c7324873518d71cc921de7825c7324867da0971cc921de4825c7324867d20971cc921de7625c7324873dd8971cc9218ff869d2604863f61a74981218fc869d2604872f9927498121cbd649d2604873ed827498121cf8609d2604863f61c6518121c7e75194604871f5d46518121afa8019460486be60065181218ff869d0604863fa1a7418121cbf649d0604863f61c6418121afa8019060486be60064181218fe87dd921142bd20776484508fe85dd9211423f21776484508ff8
  | 3 => 0x3143e26a551bd423ee9331ae74ce99e075c3a980de2f10c968b1f738df16d1a58c8c539434aa30b12c005c5c86a83892cb18c48413e4f53b023a2217cbf3cdd20f9a84422b506240e341893ed335293143831ddb08967892c94d6244955554973770bd030600dbd03462474ae98931d89285538e3491a6862de903009bd0ec20c5350d36ad8948228fc414e1b18174c339b638901b3b3e02ae240d052bfc16dcdf2bdbbe4b18d51c50f9d3c654ca8157482404c898e190a50b80714a582b1c77c01d1ddcb710d58905589330f3cc87956b4bb711ba791395f47526b4238c9968409000f0e6af287831e8d407e33138f01931192b67078830f4cace2029c8b63429c4febcbb8ed51122c291e57a87d42abd009cd7941c8e30cba36b9f52356682aa6b378558baa84f47e502ce932a75e6d64dc73a1cc4e248523c33ca4cbcaf8104736b3301bfce2a9ee3290a8a509848135cd221d68d35e4db9f49ec94434d9190009a624f0b7e5d45975e25895c9022b09750d27324a02357fe1a08d941a88b0902f718ae8904b8959ebbcc0711180a14b221984d8ca3b05a51b9a3c5332e6244bd18a34c6105f43bc415f99d24381895675dd36b89d95bd31136250ed9160624ad522fd496df444223b68edde1b84e56c3d2a4a28d94d383c75f442085d47ca2c7c27ed28738916009cfe010d80080c3800494288051a83300814024080820706c430dc21834080aa038cc0621a0196060810258f4828de6e8b60085629a0808800000048000a048223208e13800041ea300162002e2a05e08a721d82206096080061600a00038090207c8000110e768006b8e43281c048142783e2406e0786e01800080c61d804238046a8042c00801000010000384a068f401814520fe0202c0401a040d60100403002000320200602894008f200000050020004200044078780006e0008a000280c0080e00800802240185c0220000a28014020600b0280803b40011800350004a0009c0014800a700052002940013000150004a00098000b000160003c00058000b00017000120025c000480091000400014c0016800200007c0002400040000e0008c001140011000110007a00080001d0001000024000400009000120002000024000680008000a6000b400040004900010001040018000490001a0002400058002900010001240004000400002000020000400028000a0000a00028000200007000080001c0001000030000540009000460006a00040000a800100002c0003800070000a0011c000c000180000e0001c00020000400008000500014000140005000040000e00010000380016000320005a800160001c000200020000400003000064000b0000e0006c000c80023000300008a000b400168003d0007c000c80020001200003000320000c800110002400118001b000
  | 4 => 0x4118949f893b361a3e98dc007928390908446815b68736252b4fb098b049e24125a9891511cc852d2f10097d390265ae242fb98bd3118962566a32b3e24d7940132ece526ccfe1956304036245bcb1880437a5851c13a3cd645c0a8694b2c1dd043e0f89114e9616cf1796e51f19e016edbcb35a7065131593ed4ab964a073a460d842cd20fb87c8363deb70c98d3b473e2f8f58e945dac7b0b9298829527c612ea3f058cdd60f240e570a000988cb3743aa493bbeb429b0c33845947e095141a06d511cb58c136801324d8cca2ac1d0818955785434c0a64b702cf752ccd09870294482d58909588aa7892e11511d5cb17892fc750310ae24f49d07809d06c1d661fc51066a243e7b9093ab456d9b557018e447d659806e050c8298a6de1760dc0cd4b1b47ace03b5b0b48b876e3e0b005befe0103f8052a92244b64b93551ac9ac3808f2931826130c1484d3e8ee82a18b0b7bcf064220232b235afb2d87d4e5b4a936d3ddfd841dd7d93cd75048040b6c44a3054c210f65b0d917c20e20e0e85ed0cc87280700507ae0cd0b9c1f2f3d9695f91d5faef61c70845732a98953f57cfcd6d510dcde561bef355a913ac9d
  | _ => 0

def mainK7 : Nat → Nat
  | 0 => 0x2ff38e85085fd71d0a10bf8e3a1421bf58742843dea0e85087fb70d0a10bfee1a14217edc342842ff38685085fd70d0a10ff0e1a14217f1c3428437f30685087fb40d0a10ff241a1421fec4342843fb88685087f510d0a10ff021a1421fe5d8408437cbb081085f976102109f2ec20421fedd440843fd3a881087f97510210ff0ea20421fed9440843fd32881086fa6510210ff2ca20421fe194408437c32881087fa7410210f74e8204217e9d040843fdb2081086fb6410210ff4c820421ee99040843fcb2081087b96410210df2c820421fed5040843fd2a081087f95410210ff0a820421fedcc40843fd39881087f97310210ff0e620421fed8c40843fd31881087f96310210ff0c620421fed4c40843fd29881087f95310210ff0a620421fed0c40843fd21881087ba4310210ff28620421fe10c40843dc21881087fb7210210ff4e420421fe5c840842fcb9081087f87210210ff6c420421fe988408437d31081087f96210210ff0c420421be18840843fda9081087fa5210210ff2a420421fe14840843fda1081087fa4210210f748420421fe50840843fc21081087b84210210ff66420421fe8c840843fc99081087f83210210ff6e220421fe9c440843f938881085fa7110210ff2e220421fc5c440843fc38881085f87110210ff2c220421fc584408437cb0881087fb5110210ff4a220421fe54440843fc28881087fb4110210f768220421fe90440843fca0881087b94110210ff08220421fecc440843fd18881087f93110210ff06220421fec8440843fd10881087f92110210ff04220421fe5da208437cbb441085f976882109f2ed10421fedd620843fd3ac41087f97588210ff0eb10421fed9620843fd32c41087f96588210ff0cb10421fedd220843fd3a441085fa7488210ff2e910421fe1d220842fc3a441087fb6488210ff4c910421fe59220843fc32441087fb5488210ff4a910421fe55220843fc2a441087fb7388210ff4e710421fe5ce20843fc39c41087fb6388210ff4c710421fe58e20843fc31c41087fb5388210ff4a710421fe54e20843fc29c41087fb4388210ff48710421fe50e20843fc21c41087f97288210fd2e5104217e5ca20843fd31441087ea6288210df4c510421fe58a20843f4b1441087f86288210df0c510421fed4a20843fd29441087f95288210ff0a510421fed0a20843fd21441087f94288210ff08510421fecca20843fd19441087f93288210ff06510421fedc620843fd38c41087f27188210bf4e310421fe5c620843f8b8c41087f87188210bf0e310421fe58620843f8b0c41086f96188210ff6a310421fe94620843fca8c41087f85188210ff68310421fe90620843fca0c41087f84188210ff66310421fe8c620843fc98c41087f83188210ff64310421fe88620843fc90c41087f82188210
  | 1 => 0xdf821b1421bfdd5628427fbaac5086fe7558a10dfaeab14213f5d5628437e3aac5084fc7558a10dfee8b14213fdd1628437f3a2c5086fd7458a109fae8b1421bf1d1628427e3a2c5086ff5458a10dfca8b1421bf551628437e2a2c5086ff7358a109fee6b1421bf9cd628427f39ac5086fd7358a109fae6b1421bf1cd628427e39ac5086ff5358a10dfca6b1421bf54d628437e29ac5086ff4358a10dfc86b1421bf50d628437e21ac5086ff7258a10ddee4b14213fdc9628437f292c5086fd5258a10df8a4b1421bf909628437ea12c5086fc4258a10dfe64b1421bf8c9628437e992c5086fc3258a10dfee2b14213fdc5628427f38ac5086fd7158a109fae2b14213f1c5628437fa8ac5086fe5158a10dfaa2b1421bf145628437fa0ac5086fe4158a10dfa82b1421bf105628437f98ac5086fe3158a10dfa62b1421bf0c5628437f90ac5086ef2158a10dfc42b1421bf485628437690ac5086fc2158a109fee0b1421bf9c1628427f382c5084fd7058a10df8e0b14213f1c1628437fa82c5086fe5058a10dfaa0b1421bf141628437fa02c5086fe4058a10dfa80b1421bf101628437f982c5086fe3058a10dfa60b1421bf0c1628437f902c5086fe2058a10ddc40b1421bf481628437e102c5086ec2058a10dfe20b1421bf841628437e882c5086fc1058a10dfeeda94217fddb528427fbb6a5086fe76d4a10bfceda94213f9db528437ebb6a5085fd76d4a109faeda9421bf1db52842fe3b6a5084fc76d4a10bfceba9421dfd97528437fb2ea50867f65d4a10dfccba9421bf59752843be32ea5086fc65d4a10cf8cba94217fdd352842ff3a6a5085fd74d4a10dfec9a9421bf993528437eb26a5086fc64d4a10efea9a9421df55352842ffb9ea5085fe73d4a10bfae7a94217f1cf528437fb1ea5086fe63d4a10dfac7a9421bf18f52842feb96a5086ff62d4a10dfcc5a9421bf58b528437e316a5087ee52d4a10efca5a9421fb54b52843be296a5085ff71d4a10bfce3a94217f5c752842fe38ea5086fd61d4a10efea3a9421df54752842ffb86a5085fe70d4a10bfae1a94217f1c3528437f306a50877e50d4a10ef8a1a9421fed0352843fc906a5087fb10d4a10fee21a9421fd44352843fc086a5086ff76d0a10bfeeda14213fddb428437f3b685085fe76d0a109fceda1421bf5db42842febb685084fd76d0a10df8eda14217f1db428427e3b685085ff75d0a10bfceba14217f5d742842fe3ae85086ff65d0a10dfccba1421bf597428437e32e85085fe74d0a10dfec9a1421bf993428437eb2685086fc64d0a10bfee7a14217f9cf42842feb9e85085fc73d0a10dfec7a1421bf98f428437eb1e85086fc63d0a10bfae5a1421bfd8b428437f31685086fd62d0a10df8c5a1421fb90b42843df21685087ed42d0a10f7885a14217fdc74284
  | 2 => 0x437f21cc9086fd4399210df88732421bfdca648437f394c9084fe7299210dfae5324213f5ca648437e394c9084fc7299210dfca532421bf54a648437e294c9086fe4299210dfa8532421bf10a648437f994c9086fe3299210dfa6532421bf0ca648437fb8cc9084ff71992109fce332421bf5c6648427eb8cc9084fc7199210dfea332421bf946648437ea8cc9086fc5199210dfe8332421afd06648437f20cc9086fd4199210d7a8332421bf106648437f98cc9086fe3199210dfa6332421bf0c6648437f90cc9086fe2199210dfa4332421bf086648427fb84c9086fe70992109fce1324213f5c2648437e384c9084fc7099210dfea132421bf942648437ea84c9086fc5099210dfe8132421bf902648435f204c9086fd4099210df88132421af102648437f984c9086fe3099210dfa6132421bf0c2648437f904c9086fe2099210dfa4132421bf082648437f884c9086fe1099210dfa2132421bf042648437fb98c9084ff7319210dfce6324213f9cc648437eb98c9084fd7319210df8e6324213f1cc648437f298c9086fd5319210df8a632421bfdc8648437f390c9084fe7219210dfae4324213f5c8648437e390c9084fc7219210dfc6432421bf4c8648437e190c9086fd7119210deae2324213f5c4648437f988c9086fe3119210dfa6232421bf0c4648437f908c9086fe2119210dfa4232421bf084648437f380c9086fa70192109fce032421bfd40648437f280c9086fd5019210df8a032421bf900648437ea00c9086fc4019210dfe6032421bf8c0648437e980c9086fc3019210dfe4032421bf480648437e100c9086ff1019210dfc2032421bf440648437e080c9086ff75d8a109feebb1421bf9d7628427f3aec5086fd75d8a109faebb1421bf1d7628437fba6c5084ff74d8a10dfce9b14213f9d3628437eba6c5084fd74d8a10df8e9b1421bfd53628437f2a6c5086fd54d8a10df8a9b1421bfdcf628427fb9ec5086fe73d8a109fce7b1421bf5cf628427eb9ec5086fc73d8a109f8e7b1421bfd4f628437f29ec5086fd53d8a10df8a7b1421bfd0f628437f21ec5086fd43d8a10df887b14213f5cb628437f296c5086fd52d8a10df8a5b1421bf90b628437ea16c5086fc42d8a10dfe65b1421bf8cb628437e996c5086fc32d8a10dfae3b1421bd5c7628427eb8ec5086ff51d8a10dfca3b1421bf547628437e28ec5086fe41d8a10dfa83b1421bf107628437f98ec5086fe31d8a10dfa63b1421bf0c7628437f90ec5086fe21d8a10dfa43b1421bf087628437f386c5086fa70d8a109fce1b1421bfd43628437f286c5086fd50d8a10df8a1b1421bfd03628437f206c5086fd40d8a10df881b1421bfcc3628437f186c5086fd30d8a10df861b1421bfc83628437f106c5086fd20d8a10df841b1421bfc43628437f086c5086fd10d8a1
  | 3 => 0x20dfcc029841df94053083be280a6107fb4014c20ff08029841fbc8053083fd100a6107f92014c20fda4029841bfdd5610827fbaac2106fe7558420dfaeab08413f5d5610837e3aac2104fc7558420dfee8b08413fdd1610837f3a2c2104fe7458420dfae8b08413f5d1610837e3a2c2104fc7458420dfea8b0841bf951610837eaa2c2106fc5458420dfee6b08413fdcd610837f39ac2104fe7358420dfae6b08413f5cd610837e39ac2104fc7358420dfea6b0841bf94d610837ea9ac2106fc5358420dfe86b0841bf90d610837ea1ac2106fc4358420dfce4b08413f9c9610827eb92c2106fc72584209f8e4b0841bfd49610837f292c2106fd5258420df8a4b0841bfd09610837f212c2106fd4258420df884b0841bfcc9610837f192c2106fd3258420df864b0841bfdc5610837bb8ac2104ff7158420dfca2b0841bd945610837ea8ac2106f55158420df8a2b0841bfd05610837f20ac2106f64158420dfa82b0841bd505610837e20ac2106ff3158420dfc62b0841bf4c5610837e18ac2106ff2158420dee42b0841bf885610837e90ac2106fc2158420de842b0841bf9c1610827eb82c2106fc7058420dfea0b0841bf941610837ea82c2106fc5058420dfe80b0841bed01610837f202c2106fd4058420df880b0841be101610837f982c2106fe3058420dfa60b0841bf0c1610837f902c2106fe2058420df440b0841bf481610837c902c2106fc2058420dfe20b0841bf841610837b082c2106fd1058420df820b0841bd041610837fbb6a2105ff76d44209feeda8841bf9db51082ff3b6a2104fe76d4420dfaeda88417f5db510827ebb6a2106fc76d4420bf8eda88413f1db51082ff3aea2106ff65d4420efccba8841bf997510833f32ea21077d65d4420dfacba88419f597510837e32ea2105ff74d4420bfce9a88417f5d351082fe3a6a2106ff64d4420dfcc9a8841bf593510837e326a2105ff73d4420bfce7a88417f5cf51082fe39ea2106ff63d4420fbcc7a8841bf98f510836f31ea2107dd63d4420dfac7a8841b758f510837e31ea21077e53d4420ef8a7a88417fdcb51082ff396a2105fd72d4420bf8e5a8841bf98b51083bfa96a21077d52d4420bfae3a8841bfd87510837f30ea2106fd61d4420df8c3a8841fd94751083bf28ea2107f551d4420ef8a3a88417fdc351082ff386a2105fd70d4420bf8e1a8841bf98351083fda06a2107f840d4420fde41a8841fe88351083fc906a2107ed20d4420dfeeb324213fdd6648437f3acc9084fe7599210dfaeb324213f5d6648437e3acc9084fc75992109fce932421bfd52648437f2a4c9086fd5499210df8a932421bfdce648427fb9cc9086fe73992109fce732421bf5ce648427eb9cc9086fc73992109f8e732421bfd4e648437f29cc9086fd5399210df8a732421bfd0e648
  | 4 => 0x882ff398a7106ff6314e20dfcc629c41bf58c538837e318a71077f5314e20fbca629c41f754c53883bea98a7107df4314e20fb88629c417fdc853882ff390a7105fd7214e20bf8e429c41bf58853882ff388a7105fd7114e20bf8e229c41bf984538837eb08a7106fc6114e20efaa229c41f7cc453883ee988a7105ff7014e20bfce029c417f5c053882fe380a7106fe6014e20efca029c41df14053883fd900a7107ef2014e20fda4029c41fe440538837fbb6a3105ff76d46209feeda8c41bf9db51882ff3b6a3104fe76d4620dfaeda8c417f5db518827ebb6a3106fc76d4620bf8eda8c417f9d7518837fb2ea3106fe65d4620dfacba8c41bf19751882ffba6a3105fe74d4620bfae9a8c41bfd93518837f326a3106fd64d4620df8c9a8c417fdcf51882ff39ea3105fd73d4620bf8e7a8c41bfd8f518837f31ea3106fd63d4620df8c7a8c41df94f51883be29ea3105ff72d4620bfce5a8c417f5cb51882fe396a3106fd62d4620efea5a8c41df54b51882feb8ea3106fe61d4620dfac3a8c41bf18751883fb28ea31077e51d4620feaa3a8c41df14751882ffb86a3105fe70d4620bfae1a8c417f1c3518837f306a3107fb20d4620fde41a8c41fb48351883fc886a3106df7598c20dbceb31841b75d6630836e3acc6106df7498c20dbce931841b75d2630836e3a4c6106df5498c20dbca931841b7552630836e2a4c6106df7298c20dbce531841b75ca630836e394c6106df5298c20dbca531841b754a630836e294c6106df4298c20dbc8531841b750a630836e214c6106df7198c20dbce331841b75c6630836e38cc6106de5198c20dbaa331841b7146630836fa0cc6106de4198c20dba8331841b7106630836f90cc6106de2198c20dba4331841b7086630836fb84c6106de7098c20dbae131841b71c2630836fa84c6106de5098c20dbaa131841b7142630836fa04c6106de4098c20dba8131841b7102630836f904c6106de2098c20dba4131841b7082630836f884c6106de1098c20dba2131841b7042630837fbb0a6105ff7614c209feec29841bf9d853082ff3b0a6104fe7614c20dfaec298417f5d8530827ebb0a6106fc7614c20bf8ec298413f1d853082ff3a8a6106ff6514c20dfcca29841bf594530837e328a6105ff7414c20bfce8298417f5d053082fe3a0a6106ff6414c20dfcc829841bf590530837e320a6105fe7314c20dfec629841f798c530837f318a6106de6314c20fbac629841bf58c530836eb18a6106fc6314c20efea629841f794c53083eea98a61077d5314c20fbe8629841f710c53082ffb90a6105fe7214c20bfae4298417f1c8530837f310a6105fe7114c20bfae2298417f1c4530837fb08a6106fe6114c20df8c229841df54453083ef988a6107dd3114c20bfee0298417f9c053082feb80a6105fc7014c
  | 5 => 0x430dfaa6b0861bf14d610c37fa1ac2186fe4358430dfa86b0861bf10d610c37fb92c2184ff7258430dfce4b08613f9c9610c37eb92c2186fc72584309f8e4b0861bfd49610c37f292c2186fd5258430df8a4b0861bfd09610c37f212c2186fd4258430df884b0861bfcc9610c37f192c2186fd3258430df864b0861bfdc5610c37bb8ac2184ff7158430dfea2b0861bf945610c37ea8ac2186fc5158430dfe82b0861bf905610c37b20ac2186fd4158430dea82b0861bf105610c37f98ac2186f73158430dfc62b0861bf4c5610c37e18ac2186f43158430dfe42b0861bf885610c37e10ac2186fe70584309fce0b0861bf1c1610c27e382c2186ff5058430dfca0b0861bf541610c37e282c2186ff4058430dfc80b0861bf501610c37e202c2186ff3058430dfc60b0861bf4c1610c37e182c2186ff2058430dfc40b0861bf481610c37e102c2186ff1058430dfc20b0861bd841610c37e882c2186fc1058430de820b0861bfdd9210c2ffbb242184ff7648430dfcec908617f9d9210c37ebb242185fd76484309faec90861bf1d9210c2fe3b242184fc7648430bfeea908617f9d5210c2febaa42185fc7548430dfeca90861bf995210c37eb2a42186fc6548430bfee8908617f5d1210c2fe3a242186ff6448430dfcc890861bf591210c37e32242187df7348430bfee69086177dcd210c2ff39a42185fd7348430fb8e6908617f1cd210c2ee39a42186fe6348430bfee490861bfd89210c37f31242186fd6248430df8c4908617fdc5210c37fb0a42186fe6148430dfac290861bf185210c3fb90a42187ee2148430fe84290861fb085210c2ffb8242185fd7048430bf8e090861bf981210c3ef98242187fa3048430ff26090861f74c1210c37fb98c9104ff7319220dfce6324413f9cc648837eb98c9104fd7319220df8e6324413f1cc648837f298c9106fd5319220dfae432441bb5c8648827eb90c9106ff3219220dfc6432441bf4c8648837e190c9106ff7119220dfce2324413f9c4648837eb88c9104fd7119220df8e2324413f1c4648837f188c9106fd3119220df86232441bfc84648837f108c9106fd2119220df84232441bf9c0648837d380c9104fe7019220dfea032441bf940648837ea80c9106fc5019220dfc8032441bf500648837e200c9106ff3019220dfc6032441bf4c0648837e180c9106ff2019220df64032441bf880648837e900c9106fc2019220df04032441bfc40648837e880c9106f91019220df82032441bfdd853882ffbb0a7104ff7614e20dfcec29c417f9d8538827f3b0a7106fd7614e20bfaec29c413f5d8538837e3b0a7105fc7614e209f8ec29c417f9d4538837fb28a7106fe6514e20dfaca29c41bf19453882ffba0a7105fe7414e20bfae829c417f1d0538837fb20a7106fe6414e20dfac829c41bf19053
  | 6 => 0x40c37e39cc8184fc7399030dfea732061bf94e640c37ea9cc8186fc5399030dfe8732061bf90e640c35f21cc8186fd4399030df88732061af10e640c37fb94c8186fe72990309fce532061bf5ca640c27eb94c8186fc72990309f8e532061bfd4a640c37f294c8186fd5299030df8a532061bfd0a640c37f214c8186fd4299030df88532061bfcca640c37f194c8186fd3299030df86532061bfdc6640c37f38cc8184fe7199030dfae3320613f5c6640c37e38cc8184fc7199030dfea332061bf946640c37ea8cc8186fc5199030dfe8332061bf906640c37ea0cc8186fc4199030dfe6332061bf8c6640c37e98cc8186fc3199030dfe4332061bf886640c37e10cc8186fe70990309fce132061bf1c2640c27e384c8186ff5099030dfca132061bf542640c37e284c8186ff4099030dfc8132061af902640c37ea04c8186fc4099030d788132061bfcc2640c37f184c8186fd3099030df86132061bfc82640c37f104c8186fd2099030df84132061bfc42640c37f084c8186fd1099030df82132061bfdd5620c27fbaac4186fe75588309fceab1061bf5d5620c27ebaac4186fc75588309f8eab1061bfdd1620c27fba2c4186fe74588309fce8b1061bf5d1620c27eba2c4186fc74588309f8e8b1061bfd51620c37f2a2c4186fd5458830df8a8b10613fdcd620c37f39ac4184fe73588309fae6b1061bf1cd620c27e39ac4186ff5358830dfca6b1061bf54d620c37e29ac4186ff4358830dfc86b1061bf50d620c37e21ac4186ff7258830ddee4b10613fdc9620c37fa92c4186fe5258830dfaa4b1061bf149620c37fa12c4186fe4258830ddc84b1061bf509620c376a12c4186fc4258830dfe64b1061bbcc9620c37f192c4186fd3258830df864b1061bb0c9620c37fb8ac4184ff7158830dfce2b10613f9c5620c37eb8ac4186fc71588309f8e2b1061bfd45620c37f28ac4186fd5158830df8a2b1061bfd05620c37f20ac4186fd4158830df882b1061bfcc5620c37f18ac4186fd3158830df862b1061bfc85620c37f10ac4186fc2158830dfce0b10613f9c1620c37e382c4184fc7058830dfea0b1061bf941620c37ea82c4186fc5058830dfe80b1061bf901620c37ea02c4186fc4058830dfe60b1061b7cc1620c37f182c4186fd3058830dba60b1061bf0c1620c37f902c4186fe2058830ddc40b1061bf481620c37e102c4186ec2058830dfe20b1061bf841620c37e882c4186fc1058830dfeeab08613fdd5610c37f3aac2184fe7558430dfaeab08613f5d5610c37e3aac2184fc7558430dfee8b08613fdd1610c37f3a2c2184fe7458430dfae8b08613f5d1610c37e3a2c2184fc7458430dfea8b0861bf951610c37eaa2c2186fc54584309fee6b0861bf9cd610c27f39ac2184fd7358430df8e6b08613f1cd610c37fa9ac2186fe5358
  | 7 => 0xc840fbe8799081ef90f32103ee21e64207bc43cc840f3887990817f5cb321037f31664206fd62cc840df8c599081ef90b32103de21664207ee32cc840fbc6599081fb4cb32103ee19664205fe71cc840bfae3990817f1c7321037f30e64206fc61cc840f7a8399081f7cc732103ee98e64205ff70cc840ff4e1990817f9c332102fd38664207f970cc840bfae1990817e5c332102fe38664206fe60cc840ff6a199081fe14332103dfa0664207fa40cc840ff28199081ef50332103ef98664207dd30cc840ff64199081fe08332103fc88664205ff76584409feecb08817fdcd61102ff39ac2205fd7358440bf8e6b0881bfd8d611037f31ac2206fd6358440df8c6b08817fdc961102ff392c2205fc7258440dfec4b0881bf989611037eb12c2206fc6258440feec2b0881bf98561103fa30ac2206fc6158440de8c2b0881fd8c561103fa98ac2207f62158440bfee0b0881fe9c161102ff382c2205fd7058440bf8e0b0881fed4161103fc282c2207fa4058440f7a80b0881fec8161103fc102c2207f61058440ff220b0881fd041611037fb9ac2204ff7358440dfce6b08813f9cd611037eb9ac2204fd7358440df8e6b08813f1cd611037f29ac2206fd5358440df8a6b0881bfdc9611027fb92c2206fe72584409fce4b0881bf5c9611037e392c2204fc7258440dfe64b0881bf8c9611037e992c2206fc3258440dfe62b0881bf8c5611037b18ac2206fd3158440dea62b0881bf0c5611037f90ac2206fe2158440dec42b0881bf085611037f382c2206fc70584409f8e0b0881bfd41611037f282c2206fd5058440df8a0b0881bf901611037ea02c2206fc4058440dfe60b0881bf8c1611037e982c2206fc3058440dfe40b0881bf881611037e902c2206fc2058440dfe20b0881bf841611037b082c2206fd1058440df820b0881bd041611037fbb242205ff76484409feec90881bf9d921102ff3b242206fd7648440bfaec908813f5d9211037e3b242205fc76484409f8ec908817fdcd21102ff39a42205fd7348440bf8e690881bfd8d211037f31a42206fd6348440bfee490881fb989211037f31242206ee6248440fdac490881bf5892110376b1242206fc6248440bfee290881fd985211037f30a42206f66148440feac290881bf585211037ab0a42206fc6148440fee4290881fb88521103fa10a42207ec2148440ff6e0908817fdc121102fdb8242205fd7048440ff0e0908817f1c121102fc38242206fe6048440ff6a090881fe14121103fd20242207bd4048440ff64090881fe08121103fc88242206ff75990309feeb32061bf9d6640c27f3acc8186fd75990309faeb32061bf1d6640c27e3acc8186fe7499030d7ce9320613f9d2640c37faa4c8186fe5499030dfaa932061bf152640c27fb9cc8186fe73990309fce7320613f5ce6
  | 8 => 0x211437e312422877f5248450efaa4908a17fdc5211437fb0a42287f66148450dfcc2908a1bd98521143fab0a42286fd6148450deac2908a1bf18521143bf28a422877c5148450fee42908a1fb88521143fa10a42287ec2148450bfee0908a17f5c121142fe38242286fe6048450efea0908a1fe94121143fca82422877d5048450ff680908a1bfdd853102ffbb0a6204ff7614c40dfcec298817f9d8531027f3b0a6206fd7614c40bfaec298813f5d8531037e3b0a6205fc7614c409f8ec298817f9cc531037fb18a6206fe6314c40dfac629881bf18c53103ef298a62077d5314c40bfce4298817f5c853102fe390a6206fe6214c40bfee2298817f9c453102feb88a6205fc7114c40dfcc229881bf18453103ef988a6207dd3114c40bfee0298817f9c053102feb80a6205fc7014c40dfcc029881fed4053103bf280a6207f85014c40ef8a029881de14053103fd200a6207bd4014c40ff64029881fe44053102ffbb2c4204ff7658840bfee6b10817f5cd62102fe39ac4206ff6358840dfcc6b1081bf58d621037e31ac4207ef6258840dfcc4b1081fb189621037e312c4206ec6258840fdc64b1081fb4c962102ffb8ac4205fe7158840bf8e2b1081bfd85621037f30ac4206fc6158840fde42b10817fdc162102fdb82c4205fe7058840bfae0b1081fe1c162102fe382c4205f87058840ff6a0b1081fe14162103fd202c4207bd4058840ff640b1081fb88162103fc102c4207ec2058840fd040b1081fe441621037fb9ac4204ff7358840dfce6b1081bf5cd621027eb9ac4206fc73588409f8e6b1081bf94d621037ea9ac4206fc53588409fee4b1081bf8c96210377192c4206fd3258840dda64b1081bf0c9621037fb8ac4204ff7158840dfce2b10813f9c5621037eb8ac4206fc71588409f8e2b1081bfcc5621037f18ac4206fd3158840df862b1081bfc85621037790ac4206fe2158840df842b1081bf9c1621027f382c4206fc7058840df0e0b10813f1c1621027c382c4206ff5058840dfca0b1081bf541621037e282c4206fe4058840dfa80b1081bf101621037f982c4206fe3058840dfa60b1081bf0c1621037f902c4206fb2058840dfc40b1081bb881621037e902c4206fc2058840df040b1081bb081621037f882c4206fe1058840dfa20b1081be441621037e082c4206ff76cc840bfeed990813fddb321037f3b664205fe76cc8409fced99081bf5db32102febb664204fd76cc840df8ed990817f1db32102ffbae64205fe75cc840bfaeb990817f1d7321037fb2e64206fe65cc840dfacb99081bf19732102ffba664207be74cc840bfce9990816f9d332103deba664205fd74cc840b7ae9990817f1d3321037f32664205fe73cc840dfec799081f798f321037f31e64206de63cc840fbac799081bf58f321036eb1e64206fc63c
  | 9 => 0x58850dfe84b10a1bf9096214377212c4286fd4258850dda84b10a1bf109621437f992c4286fe3258850dfa64b10a1bf0c9621437fb8ac4284ff7158850dfce2b10a13f9c5621437eb8ac4286fc71588509f8e2b10a1bfd45621437f28ac4286fd5158850df8a2b10a1bfd05621437f20ac4286fd4158850df882b10a1bfcc5621437f18ac4286fd3158850df862b10a1bfc85621437f10ac4286fc2158850dfce0b10a13f9c1621437e382c4284fc7058850dfea0b10a1bf941621437ea82c4286fc5058850dfe80b10a1bf901621437ea02c4286fc4058850dfe60b10a1bf8c1621437e982c4286fc3058850dfe40b10a1bf8816214377102c4286fd2058850df840b10a1bb081621437f882c4286fe1058850dfa20b10a1bf041621437f3aac2284fe7558450df8eab08a19f1d5611427e3aac22847c7558450dfee8b08a13fdd1611437f3a2c2284fe7458450dfae8b08a13f5d1611437e3a2c2284fc7458450dfea8b08a1bf951611437eaa2c2286fc5458450dfee6b08a13fdcd611437f39ac2284fe7358450dfae6b08a13f5cd611437e39ac2284fc7358450dfea6b08a1bf94d611433f29ac2286fd5358450df8a6b08a19f14d611437fa1ac2286fe4358450dfa86b08a1bf10d611437fb92c2284ff7258450dfce4b08a13f9c9611437eb92c2286fc72584509f8e4b08a1bfd49611433fa92c2286fe5258450dfaa4b08a19f549611437e292c2286ff4258450dfc84b08a1bf509611437e212c2286ff3258450dfc64b08a1bf4c9611437e192c2286ff7158450deee2b08a13fdc5611437fa8ac2286f75158450dfca2b08a19f945611437ea8ac2286fc5158450de8a2b08a19f145611433a28ac2286ff4158450dfc82b08a1bd905611437ea0ac2286f54158450df882b08a1bfcc5611437b98ac2286fe3158450dfa62b08a1bf0c5611437a18ac2286ff2158450dfc42b08a1bd885611437e10ac2286fe70584509fce0b08a1bf1c1611427e382c2286ff5058450dfca0b08a1bf541611437e282c2286ff4058450df680b08a1bf901611437ea02c2286fc4058450df080b08a1bfcc1611437f182c2286fd3058450df860b08a1bfc81611437f102c2286fd2058450df840b08a1bfc41611437f082c2286f61058450dfa20b08a1bf041611437a082c2286ff7648450bfeec908a13fdd9211437f3b242285fe7648450dfaec908a17f5d9211427ebb242286fc7648450bf8ec908a13f1d921143bfbaa42285ff7548450afeea908a17f9d521142febaa422877c7548450bf8ea908a15f1d5211437f32a42285ff7448450bfae8908a17f1d1211437fb2242286fe6448450dfac8908a17fdcd21142ff39a42285fd7348450bf8e6908a1bfd8d211437f31a42286fd6348450efca6908a1df14d21142ffb9242286ff6248450dfcc4908a1bf589
  | 10 => 0x332486feb866490eff60cc921dfac199243f7cc332487ee9866490dfd7698121bfeeb302437f9d660486febacc090eff6598121dfccb30243bf596604877e32cc090dff7498121bfce9302437f5d2604877fb24c090efe6498121dfac9302437fdce60486ff39cc090dfd7398121dfec730243bf98e604877eb1cc090efc6398121fdae530243fd5c660486feb8cc090df57198121fee4330243fb88660487fa10cc090fec2198121ff6c130243bfd82604877db04c090efd6098121bfcec302433f9d860486ffba8c090dfe7518121bfaea30243bfd94604877f328c090efd6518121df8ca302437fdd060486ff3a0c090dfd7418121dfec830243bf990604877eb20c090efc6418121bfee6302437f9cc60486feb98c090eff6318121dfcc630243bf58c604877e318c090dff7218121bfce4302437f5c860486fe390c090dff7118121bfce2302437f1c460487fb908c090fee2118121fe84230243fb084604877fb00c090ffa6018121ff2c030243bf580604877cb00c090ffb4018121ff44030243fe48060487fd080c090ff91018121dfeea302433fdd4604877f3a8c090cfe7518121dfaea302433f5d4604877e3a8c090eff74181219fee830243bf9d0604867f3a0c090efd74181219fae830243bf1d0604877faa0c090efe5418121dfaa830243bfdcc604867fb98c090efe73181219fce630243bf5cc604867eb98c090efc7318121dfea630243bf94c604877ea98c090efc5318121dfe8630243bf90c604877ea18c090eff7218121dfae4302433f5c8604867e390c090eff5218121dfca430243bf548604877e290c090eff4218121dfc8430243bf508604877e210c090eff3218121dfc6430243bf4c8604877e190c090eff71181219fae230243bfd44604877f288c090efd5118121df8a230243bfd04604877f208c090efd4118121df88230243bfcc4604877f188c090efd3118121df86230243bfc84604877f108c090efd2118121df84230243bfd40604877f280c090efd5018121dfe8030243bed00604877f200c090efd4018121dfe6030243bf8c0604877e980c090eff2018121dfc4030243be880604877e900c090ef92018121df84030243bfc40604877f080c090efa1018121dfa2030243be440604877e080c090efe75588509fceab10a1bf1d5621427e3aac4286ff74588509fee8b10a1bf9d1621427f3a2c4286fd74588509fae8b10a1bf1d1621427e3a2c4286ff5458850dfca8b10a1bf551621437e2a2c4286ff73588509fee6b10a1bf9cd621427f39ac4286fd73588509fae6b10a1bf1cd621427e39ac4286ff5358850dfca6b10a1bf54d621437e29ac4286ff4358850dfc86b10a1bf50d621437e21ac4286ff7258850ddee4b10a13fdc9621437fa92c4286ef5258850dfca4b10a1bf549621437e292c4286ec52
  | 11 => 0x314f21dfac629e43bf18c53c87ef298a790f7d5314f21bfee429e43fb9c853c86ff390a790dee7214f21fdae429e437f5c853c86f6b90a790dfc7214f21dfcc429e437fdc453c86ff388a790dfd7114f21bf8e229e43bf58453c87ef988a790fdd3114f21fec4229e43fb88453c87f6108a790dff7014f21bfce029e437f5c053c86fe380a790eff6014f21dfcc029e43bf58053c87bf280a790f7c5014f21bfeeb31a43df9d663486ff3acc690d7e7598d21efaeb31a437f5d663486bebacc690eff6598d21dfccb31a43bf59663486ffba4c690dfe7498d21bfae931a43bfd92634877eb24c690dfe7398d21fbec731a43bfd8e634876fb1cc690efd6398d21fdae531a437f5ca63486f6b94c690eff6298d21feae331a43bfd8663487fb90cc690fee2198d21fe84331a43fb08663486ffb84c690dfe7098d21bfae131a43bfd82634877eb04c690dfe7618d219fcec31a437fdd463486ff3a8c690dfd7518d21dfeca31a43bf994634877eb28c690efc6518d21bfee831a437f9d063486feba0c690eff6418d21dfac831a43bfd8c63487ef318c690efe6318d21dbcc631a43f758c634877eb18c690edd6318d21fbca631a43f754c63487efa18c690dfe7218d21bfae431a43bfd8863487ee990c690dff7118d21bfce231a437f5c463486fe388c690eff6118d21fbe6231a43f74c463487fb908c690fee2118d21fe84231a43fb08463486ffb80c690dfe7018d21bfae031a43bfd80634877eb00c690fde3018d21dfeec29a437fdd8534867fbb0a690efe7614d21bfcec29a433f9d8534877ebb0a690dfd7614d219faec29a43bf1d853486fe3b0a690cfc7614d21bfce629a43bfd8c534877f318a690efd6314d21df8c629a43f794c53487bea98a690fee7214d21bfce429a437b9c853487f6b90a690dfd7214d21bdae429a437f1c8534877fb10a690dff7114d21bfce229a437f5c453486fe388a690eff6114d21fbe6229a43f74c453487fb908a690fee2114d21fe84229a43fb08453486ffb80a690dfe7014d21bfae029a43bfd80534877eb00a690f7e5014d219feed99243bf9db32486ff3b66490cfe76cc921bfaed992433f5db324877e3b66490cfc76cc921bfeeb992437f9d732486febae6490dfc75cc921dfecb99243bf997324877eb2e6490efc65cc921bfee9992437f9d332486feba66490eff64cc921dfac9992437f9cf32487efb1e6490eff63cc921dbec799243bf98f324877eb1e6490fdc63cc921df8c799243b718f32487efa1e6490dfd72cc921dfec599243fb8cb32487ef1966490fed32cc921fb865992437fdc732487fb38e6490dfe71cc921bece399243fd5c732486feb8e6490df571cc921bf8e399243bfd8732487ef98e6490fdd31cc921fee4399243fb88732487fa10e6490fec21cc921bfee1992437f9c
  | 12 => 0x81610cb7e102c2196ff1058432dfc20b0865bf441610cb7e082c2196ff75993319feeb32663bf9d664cc67f3acc998efd75993319faeb32663bf1d664cc67e3acc998efe7499331d7ce932663bfd5264cc77f2a4c998efd5499331df8a932663bf9ce64cc67f39cc998efc73993319f8e732663bfd4e64cc76fa9cc998efe5399331dfaa732663bf14e64cc76e29cc998eff4399331dfc8732663af90e64cc77ea1cc998efc4399331d788732663bfdca64cc77f394c998cfe7299331dfae5326633f5ca64cc77e394c998eff5299331dfca532663bf54a64cc77e294c998efe4299331dfa8532663bfcca64cc76f994c998efe3299331dfa6532663b74ca64cc77e194c998eff7199331dfae3326633f5c664cc77fa8cc998efe5199331dfaa332663bf14664cc77fa0cc998ebf4199331dfc8332663bf50664cc75ea0cc998efc4199331dfe6332663bf8c664cc76f18cc998efd3199331df86332663b70c664cc77f90cc998efe2199331dfa4332663bf08664cc77fb84c998cff7099331dfce1326633f9c264cc77eb84c998cfd7099331df8e1326633f1c264cc77fa84c998efe5099331dfaa132663bf14264cc77fa04c998efe4099331dfa8132663bf10264cc77f984c998efe3099331dfa6132663bf0c264cc77f904c998efe2099331dfa4132663bf08264cc77f884c998efe1099331dfa2132663bf04264cc77fbaac598cff7558b31dfceab16633f9d562cc77ebaac598cfd7558b31df8eab16633f1d562cc77fba2c598cff7458b31dfce8b1663bf5d162cc67eba2c598efc7458b319f8e8b1663bfd5162cc77f2a2c598efd5458b31df8a8b1663bf9cd62cc77e39ac598cfc7358b31dfea6b1663bf94d62cc77ea9ac598efc5358b31dfe86b1663bf90d62cc77ea1ac598efc4358b31dfee4b1663bbdc962cc77fa92c598efe5258b31dfaa4b1663bf14962cc77f212c598efd4258b31dfe64b1663bbcc962cc77f192c598efd3258b31df864b1663bb0c962cc77fb8ac598cff7158b31dfae2b1663bfd4562cc77f28ac598efd5158b31df8a2b1663bfd0562cc77f20ac598efd4158b31df882b1663bfcc562cc77f18ac598efd3158b31df862b1663bfc8562cc77790ac598efe2158b31df842b1663bfdc162cc67fb82c598efe7058b319fce0b1663bf5c162cc67eb82c598efc7058b319f8e0b1663bfd4162cc77f282c598efd5058b31df8a0b1663bfd0162cc77f202c598efd4058b31df880b1663bfcc162cc77f182c598efd3058b31df860b1663bfc8162cc77f102c598efd2058b31df840b1663bfc4162cc77f082c598efd1058b31df820b1663bfdd853c86ffbb0a790cff7614f21dfcec29e437f9d853c867f3b0a790efd7614f21bfaec29e433f5d853c877e3b0a790dfc7614f219f8ec29e437f9cc53c877fb18a790efe6
  | 13 => 0x5058732dfe80b0e65bf90161ccb7ea02c3996ff3058732dfc60b0e65bf4c161ccb7e182c3996ff2058732dfc40b0e65bf48161ccb7e102c3996ff1058732dfc20b0e65bf44161ccb7e082c3996ff75983329feeb30665bf9d660cca7f3acc1996fd75983329faeb30665bf1d660cca7e3acc1996ff74983329fee930665bf9d260cca7f3a4c1996fd74983329fae930665bf1d260ccb7faa4c1996fe5498332dfaa930665bf15260cca7fb9cc1996fe73983329fce730665379ce60cca7eb9cc1996fc73983329f8e730665bfd4e60ccb7f29cc1996fd5398332df8a730665bfd0e60ccb7f21cc1996fd4398332df88730665bfdca60ccb7eb94c1994fd7298332dfea530665bf94a60ccb7ea94c1996fc5298332dfe8530665bf90a60ccb7ea14c1996fc4298332dfe6530665bf8ca60ccb7e994c1996fc3298332dfee3306653fdc660ccb7f38cc1994fe7198332dfae3306653f5c660ccb7e38cc1994fc7198332dfea330665bf94660ccb7ea8cc1996fc5198332dfc8330665bf50660ccb7e20cc1996ff3198332dfc6330665bf4c660ccb7e18cc1996ff2198332dfc4330665bf08660ccb7f384c1996fa7098332dfea130665bf94260ccb7ea84c1996fc5098332dfe8130665bed0260ccb7f204c1996fd4098332dfe6130665becc260ccb6f984c1996fe3098332dfa6130665b74c260ccb7e184c1996f83098332dfe4130665bf88260ccb7d104c1996fd2098332df24130665bf08260ccb7f884c1996fe1098332dfa2130665bf04260ccb7fbaac2194ff7558432dfceab08653f9d5610cb7ebaac2194fd7558432df8eab08653f1d5610cb7fba2c2194ff7458432dfce8b08653f9d1610cb7eba2c2194fd7458432df8e8b08653f1d1610cb7faa2c2196fe5458432dfaa8b0865bf151610cb7f39ac2196fc73584329f8e6b0865bfd4d610cb7f29ac2196fd5358432df8a6b0865bfd0d610cb7f21ac2196fd4358432df886b0865bf9c9610ca7f392c2196fc72584329f8e4b0865bfd49610cb7f292c2196fd5258432df8a4b0865bfd09610cb7f212c2196fd4258432df884b0865bfcc9610cb6f992c2196fe3258432dfa64b0865b74c9610cb7e192c2196ff7158432deee2b08653fdc5610cb7fa8ac2196fe5158432dfaa2b0865bf145610cb7fa0ac2196fe4158432dec82b0865bf505610cb7aa0ac2196fc4158432dfe62b0865bdcc5610cb7f18ac2196fd3158432df862b0865bd0c5610cb7f90ac2196f72158432dfc42b0865bf085610cb7a10ac2196ff70584329fee0b0865bf9c1610ca7f382c2196fd70584329fae0b0865bf1c1610ca7e382c2196ff5058432dfca0b0865bf541610cb7e282c2196ff4058432dfc80b0865bf501610cb7e202c2196ff3058432dfc60b0865bf4c1610cb7e182c2196ff2058432dfc40b0865bf4
  | 14 => 0xd466014f7f28cc029efd5198053df8a3300a7bfd066014f7f20cc029efd4198053df883300a7bfcc66014f7f18cc029efd3198053df863300a7bf8866014f7e10cc029efe7098053df4e1300a73f9c26014f7fa84c029efb5098053dfca1300a7bf5426014f7e284c029ef85098053dfe81300a7bf9026014f7ea04c029eff3098053df661300a7bf8c26014f7e984c029efc3098053df061300a7bfc826014f7e904c029eff1098053dfc21300a7be8426014f7e884c029ef91098053df821300a7bfdd664cca7fbacc9996fe75993329fceb32665bf5d664cca7ebacc9996fc75993329f8eb32665bf9d264ccb5f3a4c9996ff5499332dfca932665bf55264ccb7e2a4c9996fe73993329fce732665bf1ce64cca7e39cc9996ff5399332dfca732665bf54e64ccb7e29cc9996ff4399332dfc8732665af90e64ccb7ea1cc9996fc4399332d788732665bfdca64ccb7eb94c9994fd7299332dfea532665bf94a64ccb7ea94c9996fc5299332dfe8532665afd0a64ccb7f214c9996fd4299332d7a8532665bf10a64ccb7f994c9996fe3299332dfa6532665bf0ca64ccb7fb8cc9996fe71993329fce332665bf5c664cca7eb8cc9996fc71993329f8e332665bfd4664ccb7f28cc9996fd5199332df8a332665bf90664ccb7ea0cc9996fc4199332dfe6332665bf8c664ccb7e98cc9996fc3199332dfe4332665bf88664ccb7e10cc9996ff70993329fee132665bf9c264cca7f384c9996fd70993329fae132665bf1c264ccb7fa84c9996fe5099332dfaa132665bf14264ccb7fa04c9996fe4099332d7c8132665bf50264ccb7f984c9996fe3099332dfa6132665bf0c264ccb7f904c9996fe2099332dfa4132665bf08264ccb7f884c9996fe1099332dfa2132665bf04264ccb7fbaac3994ff7558732dfceab0e653f9d561ccb7ebaac3994fd7558732df8eab0e653f1d561ccb7fba2c3994ff7458732dfce8b0e65bf5d161cca7eba2c3996fc74587329f8e8b0e65bfd5161ccb7f2a2c3996fd5458732df8a8b0e65bf9cd61ccb7e39ac3994fc7358732dfea6b0e65bf94d61ccb7ea9ac3996fc5358732dfe86b0e65bf90d61ccb7ea1ac3996fc4358732dfee4b0e653fdc961cca7f392c3996fd7258732dfea4b0e65bf94961ccb7ea92c3996fc5258732dfe84b0e65bf90961ccb7ea12c3996fc4258732dfe64b0e65bf8c961ccb7e992c3996fc3258732dfee2b0e65bddc561ccb7fa8ac3996f75158732dfca2b0e65bf54561ccb7e28ac3996f45158732dfc82b0e65bf50561ccb7e20ac3996ff3158732dee62b0e65bf8c561ccb7e98ac3996fc3158732de862b0e65bfc8561ccb7f10ac3996f62158732df842b0e65bfdc161cca7fb82c3996fe7058732dfae0b0e653f5c161ccb7e382c3994fc7058732dfea0b0e65bf94161ccb7ea82c3996fc
  | 15 => 0x100002000080003000140005000140005000140005000140005000140005000140005000140005000140005000140005000140004000100005800300013800300013800300013800300013800280012000e6000a0004800138002800138002800138002e000d80028004f80020001380020001380020001380020001380026000d80020006f80026000b8002000180000800020000a0006000480006000480012800180006000e20007800320006000e200078002a0006000e200078002200070001400050001000050001000130001000040000800020000c000500014000500014000500014000500014000500014000500014000500014000500016fe73588539fce6b10a7bf1cd6214e7e39ac429efe5358853dfaa6b10a7bf14d6214f7fb92c429eef72588539fee4b10a7bfcc96214f77992c429efe3258853dfa64b10a7bf0c96214f76192c429eff71588539fee2b10a7bf9c56214e7f38ac429efd7158853df8e2b10a73f1c56214f7f98ac429edf3158853dfc62b10a7bf4c56214f6e98ac429efc3158853dfc42b10a7bf0856214f7fb82c429cff7058853dfce0b10a7bf5c16214e7eb82c429efc70588539f8e0b10a7bfd416214f7f282c429e7e5058853dfaa0b10a7bf1416214f3e282c429efe4058853dfa80b10a7bfcc16214f7f182c429efd3058853df860b10a7bfc816214f7e902c429eff1058853dfc20b10a7bf4416214f7e082c429efe73584539fce6b08a7bf1cd6114e7e39ac229efe5358453dfaa6b08a7bf14d6114f7fb92c229cff7258453dfce4b08a7bf5c96114f7e392c229cfc7258453dfe64b08a7bf8c96114f7e992c229efc3258453dfee2b08a7bddc56114e7fb8ac229eff3158453dee62b08a7bf8c56114f7e98ac229efc3158453de862b08a7bf8856114f7e10ac229eff70584539fee0b08a7bf9c16114f7eb82c229cfd7058453df8e0b08a73f1c16114f7fa82c229efe5058453dfaa0b08a7bf1416114f7f202c229efd4058453dfe60b08a7bf8c16114f7e982c229efc3058453dfe40b08a7bf4816114f7f882c229efe1058453dfa20b08a7bf0416114f7f3acc029cfe7598053df8eb300a73f1d66014f7fba4c029cff7498053dfce9300a73f9d26014f7eba4c029cfd7498053df8e9300a7bfd526014f7f2a4c029efd5498053df8a9300a7bf9ce6014e7f39cc029efc73980539f8e7300a7bfd4e6014f7f29cc029efd5398053df8a7300a7bfd0e6014f7f21cc029efd4398053df887300a7bfdca6014f7f394c029cfe7298053dfae5300a73f5ca6014f7e394c029eff5298053dfca5300a7bf54a6014f7e294c029efe4298053dfa85300a7bfcca6014f7f194c029efd3298053df865300a7bfdc66014e7fb8cc029efe71980539fce3300a7bf5c66014e7eb8cc029efc71980539f8e3300a7bf
  | 16 => 0x30000c00030000c00030000c00030000c00030000e00080002000120003e00080002000120003e000d8002000420004800120001800120000000120001e00098002400390001000130001400050001400050001400050001400050001400020004c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c000380030000c00048001180030000c0004e000a00028001200056000a0002800138002e000d80028002d80020000800048000f80020000800048000f80026000d80020004380026000b800240018000e200078003200068001e000a8001800388001e00088001c00040004c00050001400050001400050001400050001400050001400050001400050001400030001400020004c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c000380030000c0017e000c00030005e00046000a00028005f80028000a0017800158002e000d80028008780020000800178000f80020000800178000f80026000d80020007d80026000b8002400180004800120004a00078003200068001e000a8001800388001e00088001c00020000c00030000800020001400050001400050001400050001400050001400050001400050001400050001400030001400050001000030000c00020000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000800108004000108004000120004a001000108005e00042001000042000680030000c00032000c0003200108003000108002800548002c000a001dc000a0010e000b8002a00088003a00088003c00090003c00090003a000c000e00006000e000068003200068003200070001000050001000050000c00050001000030000800030000c00030000c00030000c00030000c00030000c0004000500054000500030000480012000ea003a000e8001400048001280032001080032001100034001100034001080018000a80028000a8002a00088003a00088003c00090003c00090003a000a000e00006000e000068002a00068002a00070001000050001000050000c00050000800020000c00020000a00150000c00030000c00030000c00030000c000500014000400010000580030001380030001380030001300046000c0004c00100000800020000a000a0002a000a0004a000a80028000a8002a000a8002a000b80020001380020001380020001380020001380026000d80020006f80022000a8002e00088002800180004800120004800000004800120004c000600048001300018006f80036000c000e2000a8002a000a8002a000a000e0007d800260008000e400050001400040001400040004c0004000
  | 17 => 0xc00030000c00030000c00030000c00030000800108004000108004000120004a0010000e0003800042001080010000c80030000c80032000a800a2000b0002a00290002a002880022000e80022000f00024000f00024000e800320010800400007000e000070000a001080032000400012000400012000480012000c8001000030000800030000c00030000c00030000c000380030000f80030000f80028000f80028000f8002e000d80028002b0000c00020001c00020001800060001800060001800060001800060003e00040003e000580016000d80010003b80016000b8001000078001000078001400030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c000300008000f00018000f0001800060001a000f0001800750001800060001a00090001a000c0003400068002800188002a000f0001c003b0002c00068002400070001a00080003c00060002000090001a00088003200088002200088003c00060001c00060001c000280010002480014000700014000480032000e8002000030000800030000c00030000c00030000c003b0000c00070000c000380030000c00006000c00030000000046000a00028003a00056000a00028001e00056000b80036000a000ae00080002400240003e000800020007c0003e0009800360008001f600098002e00090006400020000c00030000800020001800060001800060001800060001800060001800060001800068001000068001200048001200058003200048001200048001200058002a00048001200048001200048001000068001400028001200050000800030000c00030000c00030000c00030000c00030000c0002000ec00030000c00030000c00030000800070000c00030000c00030000c00030000c00030000800110001800110001800060001a00110001800650001800060001a00050001c000680030001100018000c0003400068002a00288002a00110001a00290002c000680022000e80022000f0001c00070003800470001c00090002400068003200110001800070001800070000c00070001a00048001000048001000048001200048003200040000c00020000c00030000c0002800a400030001c00030000e000c00030001400046000c00030001400042000a8002a000a8002a000b80020000800050000f80020000800050000f80026000d80020005780022000b80022000a000500014000180014001b000140001e000d8003400388002a000a800280057800260009000e400020000800050000800030000c00050001400050001400050001400050001400050000c00050001400050001400050001400050001000030000c00020000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00
  | 18 => 0xa8002a000a8002c00030000800020002400020000c000900024000900024000300024000900024000900020001400050000600050005a0005000060011e000d80030002e8002a000a8002a000b0002400090002400080005600040001000140016e000400012002980016000d80012000b80012000b80014000980014000980010002f8001600050000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c000380030000d00098001180030000c000d0001180028000a000d0001580028000a000d000158002e000d8002800460001c00020000c000300008000300024000900024000900024000900024000800038000e0003800348001e000c8001800348001e000b8002e000a8001c00090002200070000a0007000200034000d600040001000358001000040011e0005800360004001e600058002e00050002600050002600048001e00058001400030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000e000c00034002600046000c00030004000046000a00028004000056000a00028004000056000b80036000a0011800050000800030000c00020000c0009000240009000240009000240009000200040001600034000180040000d000060011e000d800300034001ee000b80028003500024000900024000880010000e80012000480012000480012000480012000480016000a8001200050002200050000a00048001200048001200050000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c0002000f4000e001c4000e00038002d00038004100038000e0003a000c80042000c80044000d00044000d0003a000a8002800510002800010002c000f00020000800024000800024000f00020000f0000a0005000380006000d000068001200040001200040001200068001200048001000020000c00030000c00030002400030000e00080002000120003e00080002000120003e000d800200012000480038000e400078002400060004e00040001000120000600040001600058002600050001e0004000e600050000800130000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00070000c00030000c00020003a000e0003a000e000480012800380038000e0000e80038000e80020000c80030000c80032000a00062000a8003c000b000e4000a0015a000800022000800022000880022000c80022000880022000e800380007000e000070000a000400092000500014003900012000c8003a00080000c000200
  | 19 => 0xc00030000c000200004001000004001000040002d00040000100040001000044000c00030000d00030000d00044000c0004400028002a000b0008c000b0008c000a80022000e80022000f00024000f00024000d000420005000400006000c8000700044000c8001200048001000040001400108001000000001200048001200068001200048001000020000c00030000c00030003400030000c00020003a000e0003a000e000480012800380056001d0000e80038000e80020000880020000880022000c8002200060000200070001a000e80010002480014000500012000e8002000030000800030000c00030000c000280034000280044000b0000c00030000a00060001a000880022000f8002000578002000120004a00060004a00060004e00098002000008001200040004e00058001000380000800030000800030002c00020002c00020004c000b0000c00030000a00070000800130000e000800020007380020000800000000f8003600080000000128001e00098002600088001800820000600040001000738001000050009600058002600048001800398001600050000c00030000c000b00008000b0000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000a00070000c00030000c00030000c00020003a000e0003a000e00048001280038005600000000e8003a000c80042000c8003c000d00044000d00040000a8003c000a00054000a00028000b0002c00028001800088003a00080003a000800020000880022000880024000a80022000e800200006000e000068001a000680022000680022000680010002480014000500014000a8003a00080000a000f0000800130000800020000c00030000c00030008c00030002c00030000c00030000c00028001c000280010000480022000e80022000f800200057800200012000020006800180013000e000000004800128001200048001200048001600088001000030002c00020000c00030000800130002c00030000800130000c00030000e00080002400240003e000800020007c0003e000d800200076002000001000e0000600184003800018007d800260009000e200048001200048001600088001200048001200048001400030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c0003000080000000000000000b00012000b0000000068003000048001280022000e80022000f00024000f000220004000e00006000180000000e000000001a00048001000040001000008001000000001200068001200048001400020000800020000800010000800130000c00030008c000b0000c00028001c000380030000c00050001180030000c00050001080028000e8002a0
  | 20 => 0x60001a000e001c800840001c0005000100005000100005000140005000140007000140005000120002001f200030000c000280034000500010000400012000800024000400012000c80042000c8003c000d00044000d00042000a000ea000b0002c000a0001a00080002000090001000088003a00080003a00080001c00040001800068002000070001400040001000048003c0004000000005000140005000100007000140005000120002000e200030000c00038000e00028000a000c80042000d80030002d80030004a8002800008002e000a000b6000a80022000e80026000880096000800198002c000b40004000dc00070001400050001200028000a00028000a00020000a000c80042000d8003000698003000008002800008002e000a001ae000a0000200088003a000980022002580020007c0001200028000a00030001200028000c0007000140005000120002000b200028000a00028000800368000c00048000e000c00030001200046000c00030001380028000a00048001580028000a0004e000b80036000b80020000800048000f8002000080004e0009800360008001be00098002e0009000120002800080002000dc0007800340006000dc00078002c0006000dc00078002400070001200030001400050001400050001400050001400050001400050001400050001400048000c00048000a00028000a00028000a00028000a00028000a00028000a00020004a00028000a00028000a00030001200028000a000300008000300008000380028000a00088001580028000a0008800158002c000d8002c000d80020000900098000f800200008000c8000f80024000d80024000d80026000b80020001600040001000044000d0003200070000a00070003000228001e000b8002e000a8001800328001e0008800180032000ce00040001000338001000050003600050003600040008e00058002e00050009600058002600048001e00058001400030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00030000c00020000c00030000800020000e000a00028002200056000a00028001c00056000b00036000b0003600080002400240003e00080002000460003e000900034000d80024000c0004600098002e0008000580048001200032000180048000c8000700030001100034000d00034000c0008e000b8002800220011e00098002000328001000108001200050003200048001400028001200048001200048001200048001200058002a00048001400248001200048001200048001200048001200050000c00030000c00030000c00030000c00030000c00030000c00030000800230000c00030000c00030000c00030000c00030000c00030
  | 21 => 0x8000a00028000a00028000a00030002200028000800128000a00028000a00028000a00028000e000c00030004600046000c00030004600046000a00028003a00056000a00028003000056000b80036000a000ac00088001200050002400090002400090002400090002400080001800068001200040001800060001800060001800060001800060001800060001800060001a000480010000680012000480012000480012000480012000480016000a8001200050002200048001200048001200040001a00048001200058000800020009000138000800020009000138000e000d8000800258000e000b8000800258000c00098000c00098000800078000800078000a00058000a000580030000c00050001180030000c00050001080028000e8002a000a8002a000b00010000500010000500024000900024000900020000f0001400090002400090002400080005000140001800140016800140011e000d80030002e8002a000b00020000f0002400090002400090001400050001400050001400050001400050001400050001400050001400050001400050001400050001400050001400050001600020000800140004e00020000800140004e00038003600020005e00028002e00028002e000300026000300026000200066000200066000300016000300016000c00034002000046000c00030004600046000a00028006380028000a0017000158002e000d80028004700014000400014000900024000900024000900024000900020000e0003800468001e000c8001a00078002c00090002200070001200070002400050001400050001400050001400050001400050001400050001400050001400050001400050001400058000800020009000138000800020009000138000e000d8000800258000e000b8000800258000c00098000c00098000800258000a00078000c00058000c00040003c00060003c00060001800068003c0006001d400060001800068002400068002000090001a000c8002400070001800060001a000f0001800840001c00050001000050001000050001400050001400050001400048000800328000a000f0000c00390000a000c80042000c8003a001000002000e80032000d80030002d80032000a00002000b8002e000a80022000880022000880022000e00188006300012000f0001400070001400050001200028009200038000e000280020000880032001080036000c0011e000c0011a000a000fa000b8002e000a80022000e80020000e80022000880026000c8002200080001800050001200090001000050001000050001400050001400070001400050001200020019a00038000e000280020000e80038000e800380084001d2000e000b000740003a000e0003a000800022000800022000880032000880038
  | 22 => 0x400088001c00088001c0008001d00085800100004001ce00040001400080003e0005000240009800160005800160002000080073800080002001d000138000c000d0003600030003000118002e00038000c00098000c00098000e000380008007d8000e00050002400088001200050002400088001000480012000480012000480001c00090002400090002200040003a00048001400088001200048001200048001200058000800020009600020000800240004e000300036000300036000b8000e00030002600030002600038000e00028001600028001200028000c000800026000a00028001200056000a0002800138002c000d8002c000c8000a000300024000900024000900022000300024000900024000800048001200018001200130001300034000d00034000d8002e000b0002400090002400080004800138001000040004800258001000050003600050003600040008e00058002e000500026000500026000580016000480008000e8000a00028000a00028000a00030003200028000a00028000a00028000a00028000c00088000a00028000a00020004a00028000a000380030000c00050001180030000c00050001080028000e8002a000a8002a000b00020000700018000700024000900024000900024000900024000900024000900024000800020003b0001e000d0001a000a0005400068002a000b0001c00090001c000900018001580010000400050005b800100004800a6000580036000580012000b8001400098001400098001400078001600058000800020005000138000800020005600038003600020005e00028002a000b8000e00030002600030002600020006600030001e000200066000380016000c00030004600046000c00030004600046000a00028005980028000a0016000158002e000d8002800470001a00048001400090002400090002400090002400090002200048001000050002000470001e000d0001c003b0001e000b0001a00050001c00090001a00040003a00040011a00048001200048001200048001200048001400088001200048001200048001200048001200058000800020009600020000800240004e00038003600020009600038002e00038000c00098000c00098000800258000c00078000a00058000a000580030000c00048001180030000c00048001180028000a00048001580028000a0004e000b80036000a0011800028000a00028000800030001800070002400090002400090002400090002400090002200028000800390001e000d0001800390001e000b0001a00030001c00090001800120004e000400010001200096000400010004780016000d8001600058002e00050002600050002600050001e00058001200020003a00028000a00028000a00028000a00028000a0002
  | 23 => 0xd00e800201001f000805e00302700d403008d020802c118002000000800a01d09800640f60ed00080a00240ff0010000000060031800061200200505040540760090008008000021000400a00302380000d40af01d8dcc4d000306000c4084041046000002800000c009807a186056803403e08400081e4006001000054c002001005801c02000301d003c0da014019002803a00a1528000062022004803c06e0ab012813c13602c00004c40fe00000100fc0c0042000001401200700981400dc11b000804845201e01480480ca0000e1802005400100283a8048132000002c08216719f00c401800301700900d000100080340ba021000001400c09c00c80000a002908204f403e01300480140ba02902680140f600f00d8000058010002020804818e003007004004100700f80520b60018000024047044000c00603d00182ec01201202c00001ac0620798034010001047004c01a00e0ad00e803419d000800c6f4000000800807200003900e0382037000801023c006001000000007800680480f001700283cc00600100b8014034021004808407202f000043407200303a80b0004004020802000e01c006803000c000003807c03015c004806c0f4090012800408c00f04d808401e0210d2003402e00b00901f8002012000000000401d008011008e004000000402e01600780280300b2001019800410d059810413007002b8338010000013800c000000004800003c00d0068a0c0fc02901f804008a00600c81f4004000001001003800701b851826809a07a804c24c0030068000006043001800c01000204001a00b613f00001740182bd04e805832604400780080a200a009801402200200000ec14007900a80a417007a005011000000003b00a40e20080208144010042040003803005700200b4006002002004c00600000181a804a003001803c13000504b800c124003031001001a0590b200080e601d000000000005a005001006e003023019000602d01280780c601f068000402000200b802804005f000002000001305a801401600000180000320f9000025802a03a00000240360c50028008000000002803c00202c01280380040130098580002013001802c000021012016002000100300b40b2027001800430e000000800000600603b008000202a00100f800c00b08503d8056027003016401000400000c8000000008809810205e00706d404601e00200c004a00200000180000080088030000003023810800011600580b402402600002340000df034000002a0000038278038009026800816a0a902c825c004014000005406c00d00783e4196001005806000000c000000401c0020028108002031010001803c00000e805c02402f079001807600500d000000b00024000900024000900024000900020000e00038000f0002
  | 24 => 0x80641953d800080000340060000bd407c00200353d802502a001400806e00b887020a23d013812431201b01a02c82fc00008905902e608f0000da00080bd000001801802a043809432819200f815800006202008440122210428814000200155819c04400b002045808401600100d43840ba288897c04428d0d405280680f001b8bd025c00601e960c11c08f0470f5c0041e6012028002800f33b00a043600734019701c003a00001640300dd2be06782e000000000084580181fe803c02623c00d87c80001d70078038004010262ab2013e0950158d140c81370080070132034039035c3380731f2913c000008000000c07c077052124c15a001000000840e00a06d8958018119008800400c0b94bd006415e1190988584d605ed1e280740a200e0308004050008086004808413a31f00000000b4000805819800a1aa00c03b001c013933c01808200f82ac00018f0c708ac01e02d16881940060010038e5c16214f00e89342f41da02100100081ec09296e40101850001c2c18201008e800401e04c0cd010800201110f001400617c000894476800110b00000f20081f0000000602a1c8000000e00009b82ec004061010092c0220be0d800d40d2070013835c0020550000ec000c03c00000380800cc00b001401815200800d403004538381d801000c047000829407304101b805401e00d8034140362000000016201600080581c2024007800001000027500348d612200101b000009c011001c03e3e60020088a44002004813400613f16d83fc0261a400200a8002020001840c01207103c80200ce01c00601680a40d4072802c00e86202182a8360005196800cb8a0150f883342ba0000058028006005035001400c0e1001001000617502f80000502b3007002c2e400502b8e9002603a00b001c10a01a011077c01a01400080c4030000006800c04e0b201d803865406c02283cc0c800001d00041fe00002481743920aa00680b43fc1160c280f403403501181e405601111d000802801000002241d0061004001445e1a300580d817408408100000ce137177802456801b046802c81e0c0004003801602e0008068392007000002005229900080242f0296007836402a0a704500180d800600380000060d9001000002200804b000c0660ee275018000000f0028dd000e000000008414c00801200540081170008010060119003802853a05600500a003a000004800001001701084fc32200600480000001b5000069400202a00083cc04629401d000000003c000000400600f0d78004578039032808c47e03e05701e40b2003000003003625702a80a001401b004029c04210d03c00480b805f028802040e03401401cc00c02800500e800002a0210020040013001800809c000000011c2c20630ac86b4078019004800800200d03401a0000003
  | 25 => 0x2d34c259a8fca67f456eb3418f2004d592682700f29e0dff97490c4be72bdb34f4802c95c5225c64bbb942bf85628e28a445c059541947937b8f84ccb1d2d86dc99371f689aaa6c9099904f742af872ba86f4cb35a9c14180d566e3f4a796d0ae3d9f8a3c172245874dd9422d82d0190e20d87027154fdf76172667044510aa6861d8c69d2041975e0581b5d17316b8ab431029152a367251a43b553089c04ac7895eceba4b6e020b342808541012a23534591e04ad1453027d2e697664040d9fa1279478a516c8f5a83e91a75c4692cc02ca05eb229701ed73d92c30723bce6a100d73203e578a673815f1439e3302d70fc4c58baeb938b0830030c94959b0a18ccb89854ee2e02cd89c8661ed62f7594792b1732c318cadb917d0a2f794d3b2b92cede9385a6e732408f5220f2c7a0b327910ce30fe779be2dcf0c50cea7ba017c56700c0705472e4036c56c8510498d2807c05748d0fdd170916d16e03bc2d0cb5a1619452b9e3cc4aa4299d61717f4d72bea5c019fb40b6d216a096e7975ae3dadc1490ab6dd01569d100c6d28046fc964469bfb1c016415a2310885811458c6250b58c91c33a085fd0fbf53519aa66644ea164acaf052513011ce50d29f143a475a3e08e72e2c0853beeac0068010bec382003bc400160040090ebc2a805a3af86081dc07a066812c03004f000238403a00f00180000000960cd861c00e18b00280ecb100394058ded0ac34f000bbc81f27ef00201e529609c00d00b81f82a36df80140ea4ed10380c401e1f9007038dde80011090d3c00275201ba97428c00a00301c427e00c13100c835e09904e11980500b500e805406200606c0110c402c72460004018c1c01d1cd4abab6507580340281620000fc84040070a5035e17a0ff484149c6ae5e5012801c3ee007000001c01000100200111c8485000000000446d01d00284ec00309e8200000f2800001e862600082c02f81ca0a932b00e015003a0070018016ec200004e0e6c14b149999000617809c0fcc26002700c806d26000f000005079401200e8d3409a3a707504f43a801c033802408400c003026c0260d802a00143ee69d02a000935c00536d03707bc194017402c0002d40000034f082d862c000001e00b00100004d42fc0012dd008c00100633b40200f6079800086a01200d801c02000001e8bdc1b60a25cf05e80a200d0a781680fa1e20fa8000aaa44c000805c2b80b54a2063402800136f801013c01346f0fedac42ca7800024004022014802007296f74504cc05400301a02f08b63bf061a1f17c202500000041540ee07c001803000902403782940f10001c31130c4900709f405427616800140020a9000802440e000075002c23a043000014c02a8a6045802460a00004180443940063ec800818a0e4020815400009301500100661f91d2941
  | 26 => 0xe43d20db0a984de186f1d125322de886b4ade8f895dea8c63f1bb229543d86732a93692b8836c92546c87e8bb3f0713b0d138a48560a212f349a51cfc22909f75499deea786f95ecc5ea4b37855e963620763cab3b0c5cff70ce98e5b9b117846d8c692193924c339432c5c075e0fadf297ef3d0196162494b6a8d5415ca98d031a76838eafc44418b2c5ad5fcb5c4ded7785e8a6c0b26c8ffe2381bc6e2a3db09ec2c24c82fc1293b7ad6501132057e6db50da87ad1118e69164ae892dada3226bf33a0ba365c38042d6a0091b79f1f89c957f288adb0a97ea307a727f104f78f15033767d0a051710515318a3fc7925483702bd922bedae20d07494da499bea393a8964c900b86723c93c40f1d029a1156df56bc74f0804bb6884c4dbd9eda2d9b252d996b733f235682a5b2063f68ba66c80262ac7101e2dfab3ac54b4b000afaeb13abd591b17d09520daa8e510034a9618a888c44d5b62bfc7e37bc0eba69c54b0924b5ca6ed859024eae88a80f3bee08c430ece7a127cb1df5511ee2b3725d3cf38dc609dcebc6b5741805735c51559230098f0bc81e2e6f569b07ef39488f0b7c242152454a07fa25525cc6e1d756c1ee6ba50453525955240c45487c1a13acb00013087af3d3f317354b2aea34d2181ea17076a495f53f9c1d4755c2b04086e77b11f9a7c490389185161918f0a3c1b50a2d0797a6611eeecee3b249123151176a575d0b95c9c3e113d13fe5e66fcb14d7de35c594a89d9f25df70dab494c465155b8f539ba43c3976a55d44cfb6199c4174a594b1a025385e854b4123e9c1a5c465441fb321c4d9845af626af55706ba0ddfdc5d5834d35f986e8d256f660cda89648524c22255cd2a71e48adba0a684e799ece1b6590b9c40c7de8de2f34aaf23890b61cd18ee496e76c5ac221238a20ab8706c2d58c837b160eeca610d213a14f4ae764ea9059f454ca629eb0d9317823a54b9d4918818b44491f397e99dcc9416cdd6b9f4212148db89144fdc528f98bcec424e5787b5f7a8124906b83de166a8923d63ea475d3fcd452862071fb80ed4129e9c320f1b8c799a4cd73824fd4ad5d6b87330f334e2d41c935f9f9e36eb5f5861b5abbf3c49e12a66a2e24dcd838d333d880c01325704c43e05c4516072a12a01e4aafee21122d12c68ee0af9c85b948194df2d4b9061f42835f5df920a894c0f248001042f0408b612ac29d209fc9ca15cade1e008a2a578c16731979de6eeba504fa488d74877057a6cc0e6cb53dd8e63076d2cb2aef0d0c9b9b506f04af19041339fa9a4bf40c09cf0ec67b60bd2411a2b6f673d1a630cd85f722d13e81311cbc24ad9af39870fa131560861b46ecc1162c923bcddce8358d367d145485f09a41bb2ad40b8cb469dcaccb36239b6813912d4e3b31ad41296261352f3ae205f4d1c754b6404f37
  | 27 => 0xea3228ca6fb801002e891cdeb66d26230c007d39c06e20a587cd8e68dc8886245c18e031132929066ba5cceeb811842429423b26e22ec0f0df02031539dd60d0170a0ea52ee6a2299c3032c1f550589eb21d4d78d966d401c90e7566895347dd1f79aa67c1daaacd3a0b93557236edf7c8a1a1f1970b12d47b0e62ac650cab6ea8c3049029d7d41f94a4381fab0bb3fb7154e487e68cf1cf9fae60e48727c816df709449ed0ccf0ca9981e91b017d4318780d95f3502d397a5159a9e35c38d00fd5d80a125683a01c570ec5456d6316ef910d8a4ef7f5876678732662a23b252946cd75ec72d3fda8a48c381f1eccdbed52030d0e0b7aef41028d2b38599647da955b2a82ba8c04796390373b5bfa414f20a51d213ce3d5d13045775e4e65d5085340c86656a27588ce3ea1591c83515538e318bd5b5bb0cee2320a252f27b0a70e15e4f62c727495c9180fdfb9bbe095737f03e3d504bd95fc879a0f842cf9e5cad430596c85a0697125913b54e8dc60916bed0efc1f480806d45e348ca8867e19a62f0e4840e5650696d2a91e8a7b361f88e724b8cdd85627d853f66ee6831421605c94c4e96ba9b89d320efa88aa2cdeff6fd9a171ec836a04facaa2c8774ff018898e81a04ceb352a608ae0f53a308dc5e6eaf8c3dd516b00d862b15fd9c2eb47991e8a9308330bc8610ad84f0a948e923778ed16cb032bbc0e7091baaf2804128f68e33124b7e350587f12a2850239ba076f1da24ab6a90323907dbd7d1f0a59c0023ed41e66a83f9a059384bd2328351e3a635088f379a28e3655ce04e49719c87f31645e5a84685c53e54c697baf906dc276683b3d4b4d226b45b8cd290814924ce9a9ae3471a59c3236d3e17081c01eb62cc99227046191f432b24bbf1e84f3fdae4542519aff2c44e1fa2beb0d3ca6160b5f1f99940c949c515818dd0b4206a4e825cdc505b6af9d6e7448413db2cf8a20fe34ab9ecbd793f0c5176d17b61aac2d8903148ec022cad0393dc7d21fcde60132e682a1a7b78a0ea26ba6c9ba8ace5dd9808d60aa106303223be8dc39bb04d56a3911403e511430604eb5b62d0e42d94c7f21a1282cb666703f46a0d9cec6eb3dc63d842c5b85a639f9648b1219d8df0732adc0fe24e161cc58965aa740a0ecb3bd0374a819d5022cb06c78a5b5f72a441175551542cb9d5cb4aea3074736627424e9817f97249e42aec6782c656fa2610fd55522356cb9067465dc0184c285a6b908d02907580ab1d512f1f4bf1ac24b086ebc18d75a22058c0bdffa95b7ebb442dfc7bb63e3fabc24ea45a33d3623728d6fea29d294428e37c96a82ccc03ee52a405419a4919a01d70f27440252601ea44f1874a1bf87295122765c6a4b22fa74bd82e0aac11c86aac1704fa9237a68066a7617b7cf89e7423501487c24bb2fec7487dc79eed06374f
  | 28 => 0x8189c38c40036719fd6e930c9b4c2c64f4fb1a3282386fd8a9ddd1221b72cc8996e011c8ca31256ece1e9c144fc1599b91baaec66610950d4b5bc428d541a28d6257e145362c49c2b5ba5967330c05b38129e3d0de4b2856543061394f852833a2dec1e0c50e32310895c4cf617430dde3383251653953fb01fbb2056666c560766533603392271f91ae0b53788b754e51916e44f7bc3e74c6e53d53cd953d93a85b511932e49f43bb3583ce15a1953cf49eaf5b4b429223cac3b6e0371295d4bd25805e31819b4b06df8205c14b7515db64f11226f689caed8e86aaab7d2e6549e9a4baee338620753c89ed6b1b93eead8c598554a61072218b3439ca2e05b797edc0cc6443392f9b0ec808e584614e3a9b5798b79267b72a16e512c813f85276981b390fe8c853060365bb1baf96ca20e68560e04468ebcbaba78beb5fcc5422d9cabcaaeaa6790f6ccd5ee49466e3a23942424a865c112e7ad9c379858c9d80dee588dc45c720936c7b260e0acb71c4b1243547cde80cb904c7c6652b0f5226d9164c2ac37cd2b32a435f1aba2cf7c477826169d209387d9f3719172b362ae20a4e9db9961e71d7d5c70e7ae7e96a02b05de1c0c2ccf064614f94a663e2bbd522766570a0cc6d625d1e41845264b0920997d81c1ad2af47d29638eea180c2015a981a99014c4830ebd67b055e39b23c1b21b4d9b0bf4a27397213821d0295dd660a3f92363592112c28b893808102c592654d8a53dc881472258d5cee8b71096b5acb258375202b00b127892819edd26c524abbc9043c17bd2e812b1760b8c77f27aeb04481b3b1a642c80d63e203e49a356f4d9a62c7fab670895ce5ca84d876bad28c02ec54c5365d846705164d86edeade5903951ef028f866840430d8ed561b483d776d7626d54d681e7217a81722e967a993a912244cd61919bc4526b1e62d11bdf1acdce4970254add8dea6d869da82cbc31847eaf6ec34569deb4be337425a80daa496a8056e4e1d346125939e3a808d4bb746622f10b2a3bbab687255d74a55451890fda81c15a55f740c5abbe2672cad42ee5ff071d4f6bf8de1ef1adf1a87597d138f2aaa5b3fc48a2a4289d41e04aa96b21198b25757e6fc8c7016533836cd0d251cd88219270d6de8f3ba94c4c4140075ba4da24fae6b7d94324ececf12c405b2d22807ae526a8f9eb6137781a208eb2658ace3325180a4488a7ab9903455c4c344c8f34480d4c4c3f56586c1d92f9aae83d2a676cfd4c9b290d1432451f6c912691c6fc6ca7146e926332936a3854570e2120dd36378f87b23500b1934ac04c64c6dbb2823aed3a9cd107f805a4f10b4c0e3911a6f1d8d9f8753e42120b2eb602ebce2ebfc2293e6a49535c55eaf9857c5b2582c336bf6a861540d00294a0e78f5495f68af0a9409a89bd5f152ed3df1165a0797bbe20837
  | 29 => 0x7e8a37d12cba6ec469e981acc53086df3cc03f3649c0d25c218c4363a73ba0092ab7675c4a53c748b3933ff4db83b6191caa9845346314866b0c2ca81e3333478a8b344394ec6a73600121a346aca88b6282293d42038038f52d455f668687851695d55d93f820f172e01ba4cb0d37e29af28702cebc2121aece7453e6530668150a7d3911a61c4a78768189284f0cf932e7c5fb0e411bb888289ce2e22844e6555664922961c387e88e0a781ce9b964d2534be7d3968173eab9a92191db8f763fda2d30f33c9bd9df945bc40cd69cecc846473d1c7401fd7b10eecbfedc6553648d30878d58bcab652971e9a391f8ac51cd88cc2f615791d7fc9ab2f9e88297f9318030b94641d8b94148aa1a8e6f64e2d46c5203ecf7ea7983127ee8cca5cce24b009f413341ba324773035117ad3c1989f6bc2e35e7a167f1458455a720c982f85063e45b16265816f82e6087658204baefb5eb26a07be17474c3d7142f28c84593f0a863daa7955ca56122a43590951ca63184e3a5613adfd3558f9c5d678196f237f37d4dc636ca101ef0b34a4169eaf2fe545f0cfeaf08a823b3ae404a8eda00c60c7588ba5de547af432140a74078ddabfe49c8fc4337443a0a507dd8054125e850957e5803bd1800ce0254ba8499d3ba3a7b3e8f920865e365b51eab3079e8181e7426363788c307a27398164c5fccab8d5eb1351fd0281380f8813843b8e700f8919b584a8c94c7fdc412e8c6865b6636dba79fc5e95d74c4aee0c4c064d9a3731f21faa806b666042d5a36b1d425b0fc06e4b769ccca74a5b56fbe1a1187fe92d5a1c710bc4c7b8a1ea8b59f80d2aaebcc0529bbda403d147997ead1e6724f47730435a3c56610d5cb47a6ed61e228984f641b91dc4c5bd4e252a9145446575d4574c16dad06525158424c6a66bbc18ad210b73082d1e2f487530b750be7d71aa75683b264e6d2051c35e11ead6bc014367f962b3e8add6ee56d7a1fa949534e64638812e5a90bc0b4603916c1b00d789df04ef161dae118e24e75c58dcd0a6b58bb1fc23ad9ab2cab522b3018e5c574b1ca20c5f0babb5748e34ec3da456433ea7d89fc4c8e228d91a3dc8df5b6f019766ca750c35af1d5e851579f7ddb7feb0118071b30be35aa22cd114b626d5572646094cff5640dfc77a18f78cb6f3368698d34b6494ad56831484b35fd1c867440e926daf777ca464f9c05996288a64fd0d45cda6c1a1d0c054f0d035b1f56310a12c9dc672c7a1b08cd9a797a0cd524688bd04e6bc05525bb33d0f655b802769617917cda6ecf97b8291ee50f33adf8c3236020b8c985f495f85989dcfeb3147db1f68944d473aaaf0dd96f855ae8a20ebda4e66305031ee7a2fb33c9454d3592e047b965c39531ac7d6024bc476e5f8b99a83cdd5c55cd57042320b4fc91eb0d75b506575131f47b61e3
  | 30 => 0x235055b5b446b64222e78b5673d59e43820450fc6f5b68cb857f35826176e0b0880f32c03bf165186189b03230590681967882844648e094102b8ae10a305ce5f749307d11eb53f80210810668f0d8a302680d1364284cd98c5b5316ad140bf3a8e9fa2d5648fc9b819c15cc7d6b7dc990ec8410fb501f0a0be9803146a4781dd5fac7dddc60dab5cc4bd43d18a09e46d13d21fbb03b67652c9d08759a0ab3c2499b1e42598270721238904c486f5adbc50b3017c3cd9780d2828f63be1102bc78402303beac78840850b466299442c0e035976f65c5b5af989e0112af643e92a9e095bc6a71b993b4a9cb1124249e24302fdbf0ff48708b7de79345aaf39e25f88f2b97bd3279d4f49cc2822cc8acf5c500e2d2e5fb3395d16774a7b0e84438f9274015d2a2d8d89f4c80158c5d80a59530fb139954d6ed5319bc8e143eb21996e14189ab8398bfd6d3282096cdce8dc4a8c3c502a2ed41246c9a101fe53102590622b50974c7af8f7dbc6c10cf2197d85774fc20a4230449862879cc8f7df04209be4ba612c9bed950be84553e881a37b1b22b5c5361b16fbaf6873a83b25c8758a7088ab1ce3f14c8434a3f03e8e07941ad597e2d6d9797a89cf8d869a96cf5bfcfca019648562a9360b158c9ae5b9969d6959678dd6a251a9232c8b98e4557090968c0c8c5712ad41b4a2be8d134978282c890ea8c9062d2411d5d2f43956fa9fe9010a372d0d6769d08d2cc6181f348054bb501f4df3048a6a02f46e240883f309ad3407b9b305be2c6d205beace5892b7b96aa4529dd92c0cf15384c37a8c7a3f2299cd9ccad28520f510f9a6b832b813e198e19d98298f90093849d937b43ef9795adcbab043a6da4fd19e69c3a39286a9437c1d2cc3552f6a610b9a268ee9ffc13028c58f87f590cfbc67a50dadeabd600e5cc10aa860b9746b8fd721c73704a24ad23b094c4fe2384bd32fbaadae17421509be993006a8d0a10c751058839151b8adf1136e9d63d528b258a6663708d2b196a4e62ce8f8c06b7c82d64b6f23b8b2656aa51fe2d83562cd0af7a072609e072123b50cb1fc424065620bae9e14c57ee5aac6d1ef3950bf55876715f9136ec312cc08364f1d8f7cc59a31a8118d43351060d83e3626d7c0365f4aba5a82a8d661026c6a3c56b5ae88bd64615f174efa469c2145e74770b3fb6f5f704a4340a2f30bac90722e314689e89d1be8ba96a9701c372ffad22ad9013424346841003ac6dd0df93d66196497b84d1444545d47d8ae3ef65759830d4548ebc8f84990e145a055fdc66930df2541760d40f73276846c0ad69d96ba3908bc85e7129290400e9f871fd60abce55c85cc6ec9d0b0d53ecbbf61bcdb6fdb77b022ecac79a24e5c3c6174d7b07d7e287958fc97985d752b8e8f8b43cffb0615acc739f732d0317a0cabc19213c39329451
  | 31 => 0xf5a7af857a208c46aaedc38228715189a8d8cc222c2265a9ca8c23848c0b3ec768960b98bffd5005f4975d429bf4f08996a0c24ad536085e25a196754297b5aa2b5476b451325d04a9bae4db1831c9541a4a538a6174c361633cdba6346f7ba8d9c526b3c8b2984334005cd392cb0b29870c529c684ee2899a3a80f2cf40ccbc38e6a5dfa241655b40cb7717b059ef79a6971d65a6dee9119382aa0af3529b39ce041ad94004c95d222975493a23e55f6122d2c2edf3254a547302285216dc0a597a37d323b7326ca8e9389444a679ab4b99348b1c2afe977671821146722c0494278f63436aa61dfddfa77e21c0955496aa11af98ee71cb2988d9040b5c4881772cc6d46d324ec5664e154a619883c67fd84f6f1909935b244b065a043bd7df0054895ff77ceb8be5d1eff80f5aac2a0ff300ec3b93dd3341cda11e10ca4a403c23b21b05493a501b79cc94ebd04bba29a4d73552d5bd06cd8ca2bf5db9cc44ea153c442e130989295e4d6766e15df5f020a04e6aeca7ce8c092614fa061ac5771832265ab70d594d59050bb45b34890b70ccd1c205d43bab9b6ef8af1bc210c47f9fc588525f7ecb114fd942c8b016215848db86b4a1532a4403de2eadaf687692851dc248612391a98049ad4279f8b7bf360773b122a47cdce6bbfc1406f63bf83b15f948dce0f557400d80d38b53127236891593d9a262171d6f7e8124538d8d0af42b08727165e9c323ac26a8c797f7acfd0c289634f19f197e6f30f580040bd4aa57f8b9f09a1290f15fd536a7afc9f1cf56a295cb38070b0173208205ec47e51d1bb0037ed125eb00199386f0574c70397a96680b68e34404f8daeb74cab01b20a81978a8900798d683349023b37599b9c95de58068e9340cb54b5417792596d7483766d6c70969a58719d6623500091f34c6ee8c3a5e8226077cd14048c432b670de521be6c4feed874925a6d623ab24a528e4cc95b81e5e71cac2f67a1c9795f2e6dabe31827984ef2639c54760d0496d3f8eb7407a17554224a661c66511eab48f6cad2dc6c0a752d31914fedd44c00b5881a20f04491734fe6fd2b4affc7744be13aba191ccbe53f563c3a9470f4f5570bc412b0b52a422bd8af100a8a4930b0398d548e48ea7de2c19504c88b5b72113789bb000805504a61a864dc56c8d9d2ecf0974872ce1768e10431e0763c08ce27e879b048719c665e5db908cc585540a0e95cb42ca16206742b7e9155b1e33b016a3d5adbe01b5d224f453999c288d3c55a55eac6fe0815d488e6a05854a0eea0ba50424410b234e01d54cc991555f3b64b8f0a965f27ddbc283a18fd8cddc8f40be338e2c40d18597be544b113c281497047d31f87c5d030ea5483132b2eb88354232918e1b29d51becfd2fe8961c8b5f97056e502b260f22da2ceb22a1f4c7a5d6a87e129acad8c87a
  | 32 => 0xb86b9e00a7538ecbc8a149c5777868f0911b3510dc9e826917b790ff834381250ebf38b06a4690b90a1f78c9e684db3e49b5427a6d0713950a61c6dffd762c21131a7b61cca81ac09d58ed96fc76ed3ef175426134e52e2d37eeb27c8e23827988f10761504c2c2302f530dd56cc53c7112218b0811dc49c986c19b4970dc1083d3c5d5c64a055f939c3208f312597b9e328405f5ab5b4b940e6909184956ed6f687905892ef47fc58a4f610f2aa782792645239650b1c1a6ca74cc9e043a2f2c71864987d61827c69cf0af09daa204c4cc90c6d66f590607cc8f45409a4dfe9044bbc9929d0eb4041a5812b9ef472817886d2ff0e303e0b3117d03199da5812eb4182b9866d83768c27e6632e3f6aa52da853e398da6095b8e831a1d376a419c2458c25e55c1c26059dcdc196c1cad351c2adba8e0872038d8e93c2edbb5a03562494be75403fda5234ea1263f89073509361340bf231d3b10c3df474858cd5e410133e02593f2451b6c191fafdaa367becbe1cb4fae31a29c818a95e4a0578c8bea864f25b6ba7262e2b0cb75201fe25a4c48019a41697d042af706df00954697865ccc761d8c5a184e223c85c1dc3563bcb94c05e0e074443e0c35f4f92651a031e7c72ed4e9a0f06616aa2f797a9da53a46b3d6b201e6d55791cbdf486f455b09dafc35442a3177931d1f4c1786e71189ec9a5a0102002671d0d130feef9d1f48e64bd069755e3dc5a00b5dade12d881f049ac75194fff46c4998ee09ed59ccb42ef4d9868ea0ea8f529aad0994c089bec2954ce5a79eb0b2b1131ad49f190a92f983e1da2f7adb0e60d903cc5d13082c4a8000db07ce28d411776dde6fce528cd2c3932eb150475ae6e82496d1f0262233a324925d4443536bac554cc2c558e5cac0b19f611a7b3352e424ed98a99d82aa2174e2bc82b0ed0a71c3ccf71a0ad2fb09aee48ad042c2db91b1b61eea353a6693e7ef49bb290ef98c6ce82b261e196f6fdb77f30af24841cbe055485f8013808396f3502d48d11451a2cb9549d832aa2ae30074da0afaa9fa0e013af83c59361d1244512222eb645ac46798d5a1c598d9508da51f2eef59eecc4145a9be1ad0614d6eed15909e8c264b0e000279818c6230e8ada6d26f496ae59470a4749393b526a16615cd5b68cfd8236bec88c72f060d7a51cfc4130b44ef0e2e0d4c94c9b46ad8a6eb73f6d3b5b6199143c368597b549b0d515d7bc66e20e045db002b63c1010c00474a9e98a0219e12c7d6605aac4c649453e86614ac409b471dc501c068650e466f36585d55d19754068d237f317753a987606dfced77140a5d29021fa6ee649ed0109b7748da96c02a9017444ea32cd75123fe1800b68c80d0540a251d053530420e65a482ce11a8441e2abc66c1a62a6be4e30d6ac1f2995b05ee057751d481964c00e1690d2f1e2
  | 33 => 0x804cd4eb9b3dc6add401151c41dcfcf4ad14018630d2c746045ae223a8d02ed6e84a6e36f0a5a308cf39721beedd6a32110316aa42d7a1a427242024f38410d9d2832011b699131109c8cb35d881a54ba3b280d010d3b868d4db4b7964e2c5d06ea7c93fccc873a5b987a853e53d7c0db58b8404c52480275308e2b080fe27dc0ac21f8035250b16b22622a2e553c982f5f85fcb18cbf71d3f210168b460a51e5e1acf30a00bf5ce169838a8f193c6c763fc040c205fdc4066c3255de8a84d5b948865b74c3bf1bd2d04768baf2a3fd7d89aec5a3c1614b6989db3179c34c9a2dde1d02e0766920565e35ef606f5bcdd8cd5c10b8ad2c19c9afc171b6234c202a47058952b05c522dbc4ae7492882981079a9d954e63c329ae0167aac184783f6a2c3e00af78ad6b25174aecf63901cca80dd1794dc5ddea65516879447eec2260758cd7449f4884ca42b25d94c88e5a5bcd744d38046138a8084780db53a7651991644b6286a2fe9b9b3b56786ca0213129eb55854084b5a6954a9a115fea578427be8002cd4aa06a4d3b712aa8fc2fbb154d9a64d2e34756f97669290a3b1ee533e1eb993d520da5114806a3b8c7c409808e8e66a7451cb08fcc7bd8a09e021a16f810955eefece048bfbfa8adb88708663da2aa796b00ca69b6578bb6c84f96c5617492a3fa0d874144a43e6ddc1283a1b3e0894f13417db508dd9c3a81bc3088051999abd206780ea3e2815d18ceb6934336c6eb2ce0305dbf0f0b0f04da9bf234b33bef465e4fefb10ba9c4322350585952c93cef7cbdabdd64493aeb9145c8c96c0a7a318e2da400f57326ddd097b2bde12d15ba8903b880786078086c163870e253c4e6a5424620e386049c1c386bd16f4d22ccf2f115617d86ee58721d0fdc0615a90ae06b69f13a91a1a809612cc547edeee9bd37a98008f5e34599b71add81794f346aac0de523ada699176538b4862bb1d6bdc27535d90ae92226868084830937d61b82e75a7d21a2993dcd74eb6a7ea44b080464905bbc1c90aa4d3081726a4119542133c998103a2dd2a5eb1277348c8bfca8a344ab82d913f2b1037495a29b54b82e1154e8c573b8e54f1ab205eea8fd1b591168cc2ad1c93c913d728bbe91881560d52c0817395c5c0570ca0383fcbdda3636c055767884e5d4d5b1831fd0bb387c2fedb842ef334429d38872c22118143bdf5eddb0add0eb22f68e43fa595f4c63cc8814503a58868aee116abb3d21e4e69c4aca921e0cf91ff446636200a8a5cc02161ddd8a2c453391d23efb450b05a5accde41c482d8ade0066054980ae0eb182d4ee366702a10260e2601edc88059f471438cf2829506206f49bfae700303186b66c9939e624273ca8666c113059aa50ac99bd24e08d5e447456005db394df1cd331d98d66464a185dbd975626621107a284fec41500
  | 34 => 0xd715089a808d561556146a7fb7e9a6f2d96bc80a6870d9c91029f6820f3a56a03a648a5986ab1a86c265eba39e974d38d0343a32a8d6a8c1334c7cb1575306fc03f70b602fe57c08258bd0e275b19f23a4f9c689947cf7ef950aa734e76abce9ffc9009951e90f726610643b4160136a55967aa844bc531e5a30013d5a10c1e42ae1ec0d547e0ae023600363eacd5737b31b2fa657842bbc4db49401ec9130c1c2a117cad0b19c0d1c52e4c1a90bf03478dfe87d23d6d9c5d0d343a60a1986621125499f8c0251ab9668cde243fe8b519ebb841d2f66c6924f97f039c484c48dd867ae4dd63d61b62bbb31e76a23a0903fc655199764450988d171e3bd342e152b279d47fab5530828e219308ae38d8a6be4123958269601ca256cb59977240440a0a0f453b625ef1434b1f30e6981e655c9a50695e60e43e185ee0d65b7c5f8e4e9fe2d6532aee0ade3722480e0c02c3d1338ba7c23e266bf4e58e511079a2896fc19583974b412af52aaf14eb7f9eee86d17021888ea3c878e30ce7ca9c6674a99d22ac8a2900f09716857ac6d1a64842220a052d2008e7cc8fdb8a392c7fcd70dccd522b490c53558090c265165d82b13ca26ec4a30da668b3abacea8067330184722906fd9728842cb635e1129e2a1ac09e062358ea34614bdb4f51e0819525f562185c18b16dd32de82b1b5bbae80852b2d59441782a58af3e5e2f6afa86cced15661fe38649512aaa7822aced5d581fb70313ebe3c62a8e89695c52c61210357e0d33b59a36125392a7aeea810118a1949e8ced5a703da2d25769fc2d33303062b5d612a72939a0d0710545f83757bd2cd9bf3b960a6fa52358b28a1005f1776c4b43897f2e15c6e131692c12bdd5cfd40195632e203882cc2a1d2aa803754e79e4194d4ad12136599dc0f92e7422aa44292e9da4b03c264c38f4f7264ee18d2dc1e80700ad9259ebb90cda37a31138e0a3b0d8a3772ac82337d394038ca03a25052c8839ae0e4d71385d8ca2e90bb4d90331cec871cbdb599d23733a88cc5f6f52b4795f40ee53d0b52e4878f6734bf9da6efb9a90f536c63f0c47571a789c0abce5566282e0b1168ca44980a11f6829bb08f8073bbcc81fb002864b9ec27eed197117a557c4fcb87acdd0c50a8eb25d728ab0a6c32ba349a66b135319dc268148d0a42a9dbed88e1e2f22c7cd626d487e4052dab4e08a62750dff134bebd838e61794b25b9d2bb45ca26e60c62175f3be1cdadb4441779da40ee8e0285c8575988146b3901c701bd835221568c61c44d3a7bddaf4e0332da37765eb30206bb345050d573849d35b0798f14652deab270277762462087dc72003f08e45261ff91a637f379c920b3ecc3990609cf56ecd07b27f58e11ec4a738b38b55aa54dafd1364d16a4f389b71ed60a385bc08ec830f2c6f745f12e45298d40b697
  | 35 => 0x9540c140ea6b3978486675e96e4b1c3a66190dd233c582f7d372a2f145e0e24d6022c4f868c2cd468e71603097c29b3bb10a57a2760b20a9bb3a0ac9271037d603060bf2f2313ea4e719650023fb1c0e522b438c7640dab1c2b35b1e5540510c151c47d8183b8778cc4a07ccdf4943e6618c40178e122553b3acbd862596d809186240637c2ee655556e10f0134de042e409de578fd826cef8dc087b7b0c0a826a368526129b328c6b9589cc9d528d8c698050d142e9b7b979eba1759ab9e41715868865ccd0838aeae60ee2644f0198cec95ad33e7f25a010d4b044932df061d7c857529130609aeba60fe53ac17cfd73508b5663a8f52548faa05b46490dcbd9f40ac506ed80adb997003a483603801524ed5829cd5af3ccccb99243f9a1bbda4fa167823e3df6d0526abaf99b5fac0c348c32ca50cba5ad16062c9b3612771ee2ef74fc3eccdf1262eff8f3b541e1b38ac68e7044494a12ad3e2a6f73592bd66b1bbd81e6b4297e9fb46753e58f4534acec50d1415f16f32fe4bb8d18f539995b1d01491f1be00861a6073b9526ee10eeca631085c9c788a13ca12ee26686180972d069262cec41f120582c552490c366ac86b324e1d7e020035aa4cd255c2440e1f5342b1d9de63b834c1d5543887f374c1b588d7d60e5686c79c4b489f9cc59131a29ac3f81726602bc4cd2a19e27a40d4b66db2048ea0f261adb2722569f566caab63d0acc7b54639aad7d57891e15eaf49d82eb226c39290ad346241ec8e60f78264e18a70b1aa68c7cafbab4d8f5633e85e45244048b32df4115cd8b2183e4264e02270a77cbbc5d5a2500593e2c78f48a31424aa2a62355cc7dc91a7bd4877e12c2ea2a58d7c6bfcc45a1918aba646df771f42eb21c3b628e3b8645005afc504e04464e948a42db5f103ca8faaa21e8b721556282aa143447b76356c1da6cfcb
  | _ => 0

def mainK8 : Nat → Nat
  | 0 => 0x9620bfd9620ff99620bf99620ff59620bf59620ff19620bf19620ffd9220bfd9220ff99220bf99220ff59220bf59220ff19220bf19220ffd5220ff95220ff55220ff15220ffd8e20bfd8e20ff98e20bf98e20ff58e20bf58e20ff18e20bf18e20ffd4e20ff94e20ff54e20ff14e20ffd0e20ff90e20ff50e20ff10e20bf58a20ffd4a20ff94a20ff54a20ff14a20ffd0a20ff90a20ff50a20ffcca20ff8ca20ff4ca20ff0ca20ffd8620ff98620bf98620ff58620bf58620ff18620bf18620ffd4620ff94620ff54620ff14620ff90620ff50620ff10620ffcc620ff8c620ff4c620ff0c620ffc8620ff88620ff48620ff08620bf98220ffd4220ff94220ff54220ff14220ffd0220ff90220ff50220ff10220ffcc220ff8c220ff4c220ff0c220ffc8220fec8220fbc8220ff48220fb48220ffc4220ff44220fe44220ff04220ffd9420bfd9420ff99420bf99420ff59420bf59420ff19420bf19420ffd9020bfd9020ff99020bf99020ff59020bf59020ff19020bf19020ffd5020ff95020ff55020ff15020ffd8c20bfd8c20ff98c20f798c20bf98c20b798c20ff58c20f758c20bf58c20b758c20ff18c20bf18c20ffd4c20ff94c20ff54c20ff14c20ffd0c20ff90c20ff50c20ff10c20bf98820ffd4820ff94820ff54820ff14820ffd0820ff90820ff50820ff10820ffcc820ff8c820ff4c820ff0c820ffd8420ff98420bf98420ff58420bf58420ff18420bf18420ffd4420ff94420ff54420ff14420ff90420ff50420ff10420ffcc420ff8c420ff4c420ff0c420ffc8420ff88420ff48420ff08420bf98020ffd4020ff94020ff54020ff14020ffd0020fed0020ff90020ff50020ff10020fe10020ffcc020ff8c020ff4c020ff0c020ffc8020fbc8020ff88020fe88020ff48020fe48020fb48020ffc4020ff44020ff04020ffd9610bfd9610ff99610bf99610ff59610bf59610ff19610bf19610ffd9210bfd9210ff99210bf99210ff59210bf59210ff19210bf19210ffd5210ff95210ff55210ff15210ffd8e10bfd8e10ff98e10bf98e10ff58e10bf58e10ff18e10bf18e10ffd4e10ff94e10ff54e10ff14e10ffd0e10ff90e10ff50e10ff10e10ffd8a10bfd8a10ff98a10bf98a10ff58a10bf58a10ff18a10bf18a10ffd4a10ff94a10ff54a10ff14a10ffd0a10ff90a10ff50a10ff10a10ffcca10ff8ca10ff4ca10ff0ca10bf58610ffd4610ff94610ff54610ff14610ffd0610ff90610ff50610ff10610ffcc610ff8c610ff4c610ff0c610ffc8610ff88610ff48610ff08610bf98210ffd4210ff94210ff54210ff14210ffd0210fed0210ff90210ff50210ff10210fe10210ffcc210ff8c210ff4c210ff0c210ffc8210ff88210fe88210ff48210fe48210ff08210ffc4210fec4210fdc4210ff44210fd44210ff04210fe04210
  | 1 => 0x1ff90321ff50321ffcc321ff8c321ff4c321ffc8321ff48321ffc4321ff44321ff04321ffd8d21bfd8d21ff98d21bf98d21ff58d21bf58d21ff18d21bf18d21ff94d21ff54d21ff14d21bfd8921ffcc921ff8c921ff4c921ff0c921bfd8521ffcc521ff8c521ff4c521ff0c521ffc8521fdc8521ff88521fb88521ff08521fd08521fb08521ffd8121bfd8121ff98121ff58121bf58121ff18121bf18121ffd4121ff94121ff54121ff90121ff50121ffcc121ff8c121ff4c121ffc8121ff48121ffc4121ff44121ff04121bf99450ffd9050bfd9050ff99050bf99050ff59050bf59050ff19050ffd5050ff95050ff55050ffd8c50bfd8c50ff98c50bf98c50ff58c50bf58c50ff18c50ffd4c50ff94c50df94c50ff54c50ff14c50df14c50ffd0c50ff90c50ff50c50ff10c50ffd8850ff98850bf98850ff58850bf58850ff18850ffd4850dfd4850ff94850ff54850df54850ff14850ff90850ff50850ffcc850ff8c850ff4c850ff0c850ffd8450ff98450bf98450ff58450bf58450ff18450bf18450ffd4450ff94450df94450ff54450ff14450df14450ff90450ff50450ff10450ffcc450ff8c450ff4c450ff0c450ffc8450ff88450ff48450ff08450bf98050ffd4050dfd4050ff94050fe94050ff54050fe54050df54050ffd0050fed0050ff90050ff50050ffcc050ff8c050ff4c050ffc8050ff48050ffc4050ff44050ff04050ffd8c40bfd8c40ff98c40bf98c40ff58c40bf58c40ff18c40ff94c40ff54c40ff14c40ffd8840ff98840bf98840ff58840bf58840ff18840ffcc840ff8c840ff4c840ff0c840ffd8440ff98440bf98440ff58440bf58440ff18440bf18440ffcc440ff8c440ff4c440ff0c440ffc8440ff88440ff48440ff08440bf98040ffd4040fed4040ff94040ff54040ff14040fe14040ff90040fe90040ff50040ef50040ffcc040ff8c040ff4c040ffc8040fec8040ff48040ffc4040ff44040fe44040ff04040ffd9430bfd9430ff99430bf99430ff59430bf59430ff19430bf19430ffd9030bfd9030ff99030bf99030ff59030bf59030ff19030bf19030ffd5030ff95030ff55030ff15030bf98c30ffd4c30ff94c30ff54c30ff14c30ffd0c30ff90c30ff50c30ff10c30ffd8830ff98830bf98830ff58830bf58830ff18830ffd4830ff94830ff54830ff14830ff90830ff50830ffcc830ff8c830ff4c830ff0c830ffd8430ff98430bf98430ff58430bf58430ff18430bf18430ffd4430ff94430ff54430ff14430ff90430ff50430ff10430ffcc430ff8c430ff4c430ff0c430ffc8430ff88430ff48430ff08430bf98030ffd4030ff94030ff54030ff14030ffd0030ff90030ff50030ff10030ffcc030f7cc030ff8c030fe8c030ff4c030fe4c030f74c030ffc8030ff48030ffc4030ff44030ff04030ffd
  | 2 => 0xd4053ff94053df94053ff54053ff90053ff50053ffcc053ff8c053ff4c053ffc8053ff48053ffc4053ff44053ff04053ffd9732bfd9732ff99732bf99732ff59732bf59732ff19732bf19732ffd9332bfd9332ff99332bf99332ff59332bf59332ff19332ffd5332ff95332ff55332bf98f32ffd4f32ff94f32ff54f32ff14f32ffd0f32f7d0f32ff90f32ff50f32bf58b32ffd4b32ff94b32ff54b32ff90b32ff50b32ff8cb32fb8cb32f78cb32ff4cb32fb4cb32ffd8732ff98732bf98732ff58732bf58732ff18732bf18732ff94732ff54732ff14732ff90732ff50732ff10732ff8c732ff4c732f74c732ff0c732ff88732ff08732ffd8332bfd8332ff98332bf98332ff58332bf58332ff18332ffd4332ff94332ff54332ffd0332ff90332ff50332ffcc332f7cc332ff8c332ff4c332f74c332ffc8332ff48332ffc4332ff44332ff04332ffd9432bfd9432ff99432bf99432ff59432bf59432ff19432bf19432ffd9032bfd9032ff99032bf99032ff59032bf59032ff19032ffd5032ff95032ff55032bf98c32ffd4c32ff94c32ff54c32ff14c32ffd0c32ff90c32ff50c32bf98832ffd4832ff94832ff54832ff14832ff90832ff50832ffcc832f7cc832ff8c832fb8c832ff4c832fb4c832f74c832ffd8432ff98432bf98432ff58432bf58432ff18432bf18432ff94432ff54432ff14432ff90432ff50432ff10432ff8c432ff4c432ff0c432ff88432ff08432ffd8032bfd8032ff98032bf98032ff58032bf58032ff18032ffd4032ff94032ff54032ffd0032ff90032ff50032ffcc032ff8c032ff4c032ffc8032ff48032ffc4032ff44032ff04032ffd9731bfd9731ff99731bf99731ff59731bf59731ff19731bf19731ffd9331bfd9331ff99331bf99331ff59331bf59331ff19331ffd5331ff95331ff55331bf98f31ffd4f31f7d4f31ff94f31ff54f31ff14f31f714f31ffd0f31ff90f31ff50f31ffd8b31ff98b31bf98b31ff58b31bf58b31ff18b31ffd4b31ff94b31ff54b31ff14b31ff90b31ff50b31ffccb31f7ccb31ff8cb31ff4cb31f74cb31ff0cb31bf58731ffd4731ff94731ff54731ff14731ff90731ff50731ff10731ff8c731fd8c731f78c731ff4c731fd4c731ff0c731f70c731ff88731ff08731ffd8331bfd8331ff98331bf98331ff58331bf58331ff18331ffd4331ff94331ff54331ffd0331ff90331ff50331ffcc331ff8c331ff4c331ffc8331ff48331ffc4331ff44331ff04331ffd8f21bfd8f21ff98f21bf98f21ff58f21bf58f21ff18f21bf18f21ff94f21ff54f21ff14f21bf98b21ffccb21ff8cb21ff4cb21ff0cb21bf58721ffcc721ff8c721ff4c721ff0c721ff88721fd88721fb88721ff08721fb08721ffd8321bfd8321ff98321bf98321ff58321bf58321ff18321ffd4321ff94321ff5432
  | 3 => 0x240038000300000000000120000800240010003800098001000080000000080010000800250002800240008003900020000400080002000100008000400020001000880004000a000100008000400020001000080004000200010000800040003000600030001c0011000600030001c000f000500028001c0001000500028001c000f000580034001400460001000200010000800040002000100008000400038001c0006000700000001c0047000680030006a000b0005000200010000800040003c0008000400070000400080004002380014001a000500028002c000800090002000240008003500020000400080002000100008000400020001000080004000200010000800040008000100008000400020001000080004000300060003000700011000600030002400110005000280070003900050002800240001000580034001400870004000200070000f0004000200024000f0004800340010000100048002c001000180001000e0000e000c0003000e0000e000a001c0001c0010000600098001000080038001c8001000080001000280034000a0005000580010004a0005000480010000e0004001c80010000400020001000080004000200010000800040002000100008000400020001000080004000200010000800040002000300018000c0010000300030000c0006000300018000c003a000300028000c00070005800340014002a000300018000c0006000700000000c0006000400020000c00070004800340010000100048002c00100018000100018000c0006000300018000c0006000300018000c000600030001c0008000400030000400080004000080014001a000500028002c000800250002800240008000700020001c0008000200010000800040002000100008000400020001000e800040002000100008000400020001000180004000200010000800040003000600030008400110006000300024001100050002800bc0001000500028002400010005800340014008700040002000bc000f0004000200024000f0004800340010007d00048002c0010001800090000000700006002f00000002400060000800340018003800008002c00140038003e800240010003800010001000080004000200010000800040002000100008000400020001000080004000200008000400020001000080004000200010000800040000000100008000400020001000080000000200010000800040002000100008000400020002bf98c53ff94c53f794c53ff54c53df54c53ffd8853ff98853bf98853ff58853bf58853ff18853ff8c853ff4c853ffd8453ff98453bf98453ff58453bf58453ff18453bf18453ff8c453ff4c453f74c453ff0c453ff88453ff08453ffd8053bfd8053ff98053bf98053ff58053bf58053ff18053ff
  | 4 => 0x6000200010000e000700018001c00000007000200010000f000200010001c000100020001400080008000480014000a0005000100008001c0001000100008001e00020006000340006000b0001800080012000300018000c000600030002800300018000e0008800300018000e0007800280014000e0000800280014000f000580034001400060004000200010000800040002000100008000400118000e000c000380028000c00080003000200010000f000200010001c0001000200014000a000d0002800140016000500020002000120005000280014000400020007000040004000200078000c001a000300018002c000600030001000240006000300018000c00060003000200018000c000600080001800180006000300018000c0006001d0001800140007000580034001400080004000200010000800040002000100006000300018000c0006000300018000c0006000300018000c000800030001c0008000400030000400080005000280034000a000500058001400080009000280014000a00020001000180072000200010001c0006000d00018000c001600030001000240006000300018000c00060005000600030001c0011000600030001c000f000500028001c0001000500028001e000b000680028000800080004000200010000800070002000100008000700038000c000e000000038008e000d00060011c0016000a0004000380010000800040002000080004000200010000800040002000100008000400020001000100004000200010000a0002000100038004a000200010003c0006000d00018000c001600030001000240006000300018000c00040004000300018000c000e000300020000c000700068002000000004000300018000c00060002000100008000400020001000080004000200014000400020003000e40004000200038000c001a000300058000c0006000900018000c000600030001000140010000800000003c0010000800000003c001a000800000001000000007000400018000800040002000100008000400030001000080004000200014000400020000800080004000000008000c001a000300058000c0006000900018000c000600030001000100006000a0005000400046000a0005000440014000d0005800200010001000078002000100011000400030001a00080006000440012000b00040005800200010000300040000000100006000400018000c0006000340016000a00238002400100032000880010000800100000800100008000d000280010001a0005000280014001600040012800140012000400198001000020004000100008000400020006000080004000200010000800040002000100008000400020001000080004000300040002000ac000f0004000200026000d00040000
  | 5 => 0xea0f1321da288fec2e16b52158f15580d4b353107a6d3172e4296e5390b6c14803423c8942ae1f030595e0a6c40ddf9cd92cc3a211349a0ea262e6d120b69d7ebc90f167e6fb30c065b0937be041c2c3a3d81ea852d421f6212180fbc328ad1d85908e727ff1db170742f8552593bd7c3be121ae7679a37e39c8a8ee27e88df466d4d4294dcb40f2f63a35e5fdd151ff15a250c68b5f6e9889940e763cfab519b5c20a9850368161ed578189ae0032f590e5c13d7e6e32483b070e3a2f8dc97b9ef48e021825b46ecca3727a644bc8511a4f189874ef6d4c03ff322a06f42b4d96bb1d90723d56e4d5013dae9080a134100756668cd046ee6491d1d5a43a7bb81e2180dde4e6c133d6318ff48c01ed89c7a99161898e3c9c9582b07eb49ae95ea41c7f41484bac732bc03b2646083fb412872b16e91907860aeac14b6e3f77d6a343f2b5af9d027db36b9d4923baf66b41e43591bb148b3c1a94534b40b24df304e2295b3c1bc11213122cd330cf838db73598b420ad0e0438f2eeab6821a959763c6626315254f7083484a52006656010f997fba2606b8335d0f6e01ce4e25d5f884034873098308088030812f84f01a7105f00347f0b6010000a41c60284b80e0060d00604906b8cc348b60282400b267023154188450b2014c10012ae0906900200a000238330240740680007e000778d10c0064148164b21a40001e0020048481c0902683e8000040a40b8ab0fc0fc0985d3a803830a8b1462209800901c0140480f05e2e40a9090dc0957186d036174bc04500e454070565f20000080a00200c400020da034b702e02a020398d00142acda8a60821ac0380301a0400084512c358b200711236cbe9250760d82a80e00e0780c0120162e42f00208c034000220100d80000007a00000002018074020000ae7480185f02017c0b01c0003100086a02206802807048b140709c0fa01000180000170848060201b03a8210e42044480901403450003128018ac0061780a08917205600c0280600c14c040050ba3f0170160fa0080c8000080140182101a0102380b00201c9482a2c400c04804016010000661240e03603806a0480c05400c1a81d0000060181907e0863ac0a80e01006c050090300b4020001525a00b003004154008020240040f81731e01c39006010068031ec0e20185d8120b2018358020b64e03000510a3a00b0670441641100002a05c018051c60001e0082742ec2401500c0040a8000200580a00001606c000040c002c000110180400e0850e801c0081105400021864014000070f10000680e82c0080882305a0601ec0003600c0386300005202c1202e00003c0580000008c0083200014c0080923c0140607f00003c4f0250040682b82d000030000010e81000b00a00023401874000000020000040181000700a0140c800100008
  | 6 => 0xc1916e3cc590bcdd4aa080db63825d46c577d90dc74dc876e55f2216cb0831881f081539d2107b1e19537bb545e523f1e0a712245d352ed0a883b1e6e986ec1eb747a9828a111c2c17b48552214e5005c0ac4013a7e1b5b2192a0d02c7481c48d9ede3892f1aaeb19d384d7050589754c0aa3bd50430764b0b8c520258d5c6ae9850b358663f7e68fcb877619baa4f48c09beb4532bdc8e0cb7c669e52d17670afe39dcfc999f3575ed8b4fbe5e169c241fc0227c257129a75a953db3974c241859f66d1a031a4324bb8c6d9686990c4970164f231bc90f0d3301c0af07e0b9ab282fb2ac0662669ab748d8dc09860c4a1cc8d9c9d17e4d61534b075880352b394549f64443e38a765034d3f26b733eee9f803026d539f6284ee227708ac14b24a6461e8558257124b32e823af24453fabb62c0743cde38439888db4055be3c162d80a1df1b48c2dc632906d6748c42a48c57d291ca2735b1608b64bd6e9666794804d1701c3c32ab6a5b5d994b61ca3f8c9067e9ead93592e199577192eb4f927da54d35879c601aca71ec870010d163abf44e1ebd076c25f2dd6174658b5ec36abb5fe4dd6900710a684b06e35eb6637f8ac1769a3c46c6c5d87a931113907307b47efc1c8809c459d62bac29bb3893a0e0e3cde38f382565514c961da2a6bc1008c14d00832e27049a228c1f29e23278f294b8b37334d6b84434f742e6650d7ec76d592164f30110a16cd9c51b2d288f84565410afed1aa6571b3ecaa2788fa0baa3f1b7ab7e1debf58dec036d99ae3d5a9af6c47ad69cbe015a8302507348e3c0bd9068565ca7706bf97b56a1c1e148e4a1430dec2488b010d81864df7726813434b8f755565f3ccb0e4d0345cad30ad8c2077755ac9ab27c349e12bb5f07551c68f22b8f4a0c463b8d1333d5353b4ce766e78df8f39826ccc9fc4a49ce85dc58c368b3256a8b7ccc5aab69173cc487580795b47beaa2ed3d6e569439a79b1964c2a646391d50bb45df8a4fa3dda006961499549276249811c18a3dc804930550db68324fda753855c85b4dc06dc174aa42e705adf4887761d9cd12a1cf9963cf28ee5dd96f857ceb1295a10597d8d91ceb84e8617a72482db6de1bea33739c0aafa48c524eb0cdd998302c784747871e2711c0982823a99678c4ae5b12b11c3d74e5c7b05580a557723d5fcb3805f8f5bf0507d753f1e0018c896b9b7fb330ce978823b6813a0c99cb494c20d2799758d54f8b96ded903ede5841f40405088732990839f74ac49906bb5e2f3e05bf4c672261a846ddd045264a354c0f41c3834bdf98bbc6c89b8f5637d5bcd2a5c99e56f93380a4b78f63b65555c9b17e892645405285d3e14c360a384d656ae6034055768a219ac69219df16529d04357aef69a94749edc477fc51f062f93277e4f08492c935c905b195b1a69e4588d9
  | 7 => 0xca1491579e01918e4896181ee319fd0e9033c78b24d24006c304042876b1d03678a7cf4ae84fd766497810ef00bb42da2f690688ec9506162ab202a5e75f8e84f94c14b44283d25cdd745ec06cafb1884e9be75c824295e5817b775db86251b5b3a0aca1b8f8b75a008c87b27be4ad0fdc2459de0f7368f21b2cf4c48d4dea7a114a59651bc86618e9fd2fb9a3a8819e86a0f1c0c5f598a3623a5c929a86530d459c4b5d4d2738668f99e500e1dcf2b0593892473a88f60de875d727612db26133685292fbfc30c860fcdf1d489545c6e572796af1427a37a2620ddbc764a8c5a971337cd0220badc27a9c0a49f50a0158a06cca5820c6ac035de13012b991b9ff077a448a6fdc5974d32d5403002d44607346776b6419d5918e5258461c781084c201f598095256f40fa234bfef51e2c187b62609b2ab1571ebcd98ccdb50cf3c785ce046b480d6db3a2e25d5223dc1043918af1eb7bc7a5deaf2a0e866db973e18d0c18d1e3c716959e85e22ab874205a381d2427b2e82a1ef4011f48d05b28b0e0e9dae60f9c03b38f516a661b5839bf2bdb015c1c21602bb28aa4968af051bd9e0160a2af1a7d644dd6d3f65b65f63b7a97e6ce6cdde207111bf18c3b952dac3b7adeaddaa570becc9934ea0d38a72cb2f945dc7934361d1b9b743572e3c40a7827656d269ceb3e20813203c2b174cc78f2ca5542f0629ce5ddc78dd3ee965c678f1c82a4ed72f71e4b0baa8d71ee3c78b83271a793a672afebb1c7b476a6dc667e3f5095e876844a9f8e284aff9bbe3c89d29485b14662b14be116b5e7765779c1ad8955e24597d22f1e8e8892fb91f796f18e6540e3ca19e2b1d41e146303e51f267075acd6d656c6dec328770b8f23951c0aa1a2c104d5084371e8ef90338599871594dbabe2deb785ec6de3d7813694f9bfbbf10a2036c5eb656b5d92f504c30b07e566d68da1c54643127512db22d29fad84932c620239bbbab30fd9ec51d59bdb00251b45ef061c3493128a7d2a46e1e77922c58793b19903d6bce7f9d76e33f25ab5f17ade2c68731a2a4d716c0c25bcdc031cae52bbe1512510933f61f7722a871685921b51d759026258c44563921db78fc05aa6db55eb8a1a6d1e5740d5055a208e0d0b5946a143e344a01b75794a898fcd7910f25179c36841baa8d2db093a941e2507287eed6584f2a963e0d7c504fe0ca339a28a36ce335358c06b1fec5a7969d452c1675d71454d9a7fcded9f454402ff5e91802f822615be1bc65ae1f01c6f15a8a72b84078f34a6caaa6406a85bfb7f421186d37befa20712a7cdab372bdce238f43e7a2f09864373bd90562cd806b3b447cb1d590c041d9a23d49c5f9d35d0554c9c122fa74b8f66724ee037f49d402eead9d080639cc8a9c94fe452dd8d5d54e266303600476dd85366472548c92ee3
  | _ => 0

def mainK9 : Nat → Nat
  | 0 => 0x2a2cb828a6502211888a22c10f52bc66022187511da06851789881943e6e9071589113218471c4460748171ed422316322448911b31864c18d2405cc4046839f3c8c00a107478200640010e6420cd00900510411c4520c2082082bfca7fd53fe29ffccbfc65fd32fe197fcc7fc63fd31fe18ffc87fc43fd21fe10ffd43fca1fd50fe287f903fa81fc40ff987f8c3fa61fc30ff907f883fa41fc20ff887f843fa21fc10
  | _ => 0

def mainK10 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def mainN (k : Nat) : Nat :=
  match k with
  | 5 => 2
  | 6 => 393
  | 7 => 3309
  | 8 => 911
  | 9 => 34
  | 10 => 1
  | _ => 0

def mainR (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt mainK5 (i*61) 61
  | 6 => packedAt mainK6 (i*50) 50
  | 7 => packedAt mainK7 (i*39) 39
  | 8 => packedAt mainK8 (i*28) 28
  | 9 => packedAt mainK9 (i*17) 17
  | 10 => packedAt mainK10 (i*6) 6
  | _ => 0

def mainH (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt mainK5 (122+i*17) 17
  | 6 => packedAt mainK6 (19650+i*19) 19
  | 7 => packedAt mainK7 (129051+i*18) 18
  | 8 => packedAt mainK8 (25508+i*17) 17
  | 9 => packedAt mainK9 (578+i*3) 3
  | _ => 0

def mainI (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt mainK5 (157+((h/1+packedAt mainK5 (156+(h % 1)*1) 1) % 2)*3) 3
  | 6 => packedAt mainK6 (28857+((h/174+packedAt mainK6 (27117+(h % 174)*10) 10) % 737)*10) 10
  | 7 => packedAt mainK7 (209296+((h/1591+packedAt mainK7 (188613+(h % 1591)*13) 13) % 6372)*13) 13
  | 8 => packedAt mainK8 (45802+((h/437+packedAt mainK8 (40995+(h % 437)*11) 11) % 1790)*11) 11
  | 9 => packedAt mainK9 (785+((h/15+packedAt mainK9 (680+(h % 15)*7) 7) % 74)*7) 7
  | 10 => packedAt mainK10 (7+((h/1+packedAt mainK10 (6+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def mainPos : Nat → Bits
  | 0 => 0xd07fc7ffc3c00cfefc23f41ff1fff0f0
  | 1 => 0x2060383ffffc73611ffc08180e0fffff
  | 2 => 0xff803fc0ffff8381e03fffe00ff03fff
  | 3 => 0x3fffc000fc03fc01ffc00ffff0003f00
  | 4 => 0x3fffffff0003fffe00000fffffffc000
  | 5 => 0xc00000000003fffffffff00000000000
  | _ => 0

def mainNeg : Nat → Bits
  | 0 => 0xd125cacbc34004267ca1f44972b2f0d0
  | 1 => 0x28709033546831600de90a1c240cd51a
  | 2 => 0x93812480a9918291a01664e049202a64
  | 3 => 0x3df9c022f022dc01f6c04f7e7008bc08
  | 4 => 0x2e5e3f3c02037bda00000b978fcf0080
  | 5 => 0x3effddb3b800000000000
  | _ => 0

def mainAtlas : Atlas := ⟨10, rawDecor 63 mainPos mainNeg, 0xfeeaece0fae8c0c0, mainN, mainR, mainH, mainI, 67, [(0xaaaaaaaaaaaaaaaa, 8), (0x3333333333333333, 8), (0xf0f0f0f0f0f0f0f, 7), (0xff00ff00ff00ff00, 8), (0xffff0000ffff0000, 8), (0xffffffff00000000, 8), (0xff00ff00ff00ff, 7), (0xffffffff, 7), (0x5555555555555555, 6), (0xffff0000ffff, 6), (0x55550000aaaa00, 7), (0xaaaa0000aaaa00, 7), (0x606606006066060, 7), (0x1111444422228888, 7), (0x1212484812124848, 7), (0x3300330000330033, 7), (0x55550000aaaa0000, 7), (0x8822882288228822, 7), (0xaa00aa0000aa00aa, 7), (0xcccc000033330000, 7), (0xf0f0f0f0000, 6), (0x3c3c3c3c0000, 6), (0xf0f00000f0f00, 6), (0x3030c0c03030c0c, 6), (0x50505050a0a0a0a, 6), (0x50a050a050a050a, 6), (0x606060606060606, 6), (0xa0a0a0a0a0a0a0a, 6), (0xf0f00000f0f0000, 6), (0x1428142814281428, 6), (0x3c00003c3c00003c, 6), (0x6600660066006600, 6), (0x9999999900000000, 6), (0xcc000033cc000033, 6), (0xff00ff, 5), (0x33333333, 5), (0x99999999, 5), (0xaaaaaaaa, 5), (0x555555550000, 5), (0x55aa000055aa, 5), (0xa5a50000a5a5, 5), (0xaaaa0000aaaa, 5), (0xff000000ff00, 5), (0x33003300330033, 5), (0xff000000ff0000, 5), (0xc030c030c030c03, 5), (0x2222222222222222, 5), (0x2222888822228888, 5), (0x3300330033003300, 5), (0x3333333300000000, 5), (0x3c003c003c003c00, 5), (0x4444444411111111, 5), (0x5050050550500505, 5), (0x5555000055550000, 5), (0x5555555500000000, 5), (0xaa00aa00aa00aa00, 5), (0xf000f00000f000f0, 5), (0xff00ff0000000000, 5), (0x33330000, 4), (0xaa000000aa0, 4), (0x660000006600, 4), (0x22002200220022, 4), (0x202040402020404, 4), (0x202080802020808, 4), (0x3000300000300030, 4), (0x3300330000000000, 4), (0x5555000000000000, 4)]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor2x6p2_0 : Interval minor2x6Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor2x6Complete : Complete minor2x6Atlas := by
  intro k hk i hi
  change k ≤ 2 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor2x6p2_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor2x6Pair : properPairs (target minor2x6Atlas) (asRow minor2x6Pos) (asRow minor2x6Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor2x6Lower :
    Lower true (roots minor2x6Atlas) (target minor2x6Atlas) 3 := by
  have ready : Ready minor2x6Atlas (asRow minor2x6Pos) (asRow minor2x6Neg) := by
    refine ⟨minor2x6Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready minor2x6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 0, 2)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3xe8p3_0 : Interval minor3xe8Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor3xe8Complete : Complete minor3xe8Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor3xe8p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3xe8Pair : properPairs (target minor3xe8Atlas) (asRow minor3xe8Pos) (asRow minor3xe8Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3xe8Lower :
    Lower true (roots minor3xe8Atlas) (target minor3xe8Atlas) 4 := by
  have ready : Ready minor3xe8Atlas (asRow minor3xe8Pos) (asRow minor3xe8Neg) := by
    refine ⟨minor3xe8Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready minor3xe8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x6p3_0 : Interval minor3x6Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor3x6Complete : Complete minor3x6Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor3x6p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x6Pair : properPairs (target minor3x6Atlas) (asRow minor3x6Pos) (asRow minor3x6Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x6Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor3x6Atlas) (target minor3x6Atlas) (sliceDomain minor3x6Atlas j.val) (sliceBound minor3x6Atlas j.val)) :
    Lower true (roots minor3x6Atlas) (target minor3x6Atlas) 4 := by
  have ready : Ready minor3x6Atlas (asRow minor3x6Pos) (asRow minor3x6Neg) := by
    refine ⟨minor3x6Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor3x6Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor3x6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x6Slices : ∀ a : Fin 1, Slice true (roots minor3x6Atlas) (target minor3x6Atlas) (sliceDomain minor3x6Atlas a.val) (sliceBound minor3x6Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[(0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3xe6p3_0 : Interval minor3xe6Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor3xe6Complete : Complete minor3xe6Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor3xe6p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3xe6Pair : properPairs (target minor3xe6Atlas) (asRow minor3xe6Pos) (asRow minor3xe6Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3xe6Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor3xe6Atlas) (target minor3xe6Atlas) (sliceDomain minor3xe6Atlas j.val) (sliceBound minor3xe6Atlas j.val)) :
    Lower true (roots minor3xe6Atlas) (target minor3xe6Atlas) 4 := by
  have ready : Ready minor3xe6Atlas (asRow minor3xe6Pos) (asRow minor3xe6Neg) := by
    refine ⟨minor3xe6Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor3xe6Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor3xe6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 3, 7)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3xe6Slices : ∀ a : Fin 1, Slice true (roots minor3xe6Atlas) (target minor3xe6Atlas) (sliceDomain minor3xe6Atlas a.val) (sliceBound minor3xe6Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[(0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16p1_0 : Interval minor3x16Atlas 1 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16p2_0 : Interval minor3x16Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16p3_0 : Interval minor3x16Atlas 3 0 40 := block_range (n:=40) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16p4_0 : Interval minor3x16Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16p5_0 : Interval minor3x16Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor3x16Complete : Complete minor3x16Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor3x16p1_0 i (Nat.zero_le i) hi
  · exact minor3x16p2_0 i (Nat.zero_le i) hi
  · exact minor3x16p3_0 i (Nat.zero_le i) hi
  · exact minor3x16p4_0 i (Nat.zero_le i) hi
  · exact minor3x16p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16Pair : properPairs (target minor3x16Atlas) (asRow minor3x16Pos) (asRow minor3x16Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16Lower (allSlice : ∀ j : Fin 3, Slice true (roots minor3x16Atlas) (target minor3x16Atlas) (sliceDomain minor3x16Atlas j.val) (sliceBound minor3x16Atlas j.val)) :
    Lower true (roots minor3x16Atlas) (target minor3x16Atlas) 6 := by
  have ready : Ready minor3x16Atlas (asRow minor3x16Pos) (asRow minor3x16Neg) := by
    refine ⟨minor3x16Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor3x16Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor3x16Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 0, 4)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor3x16Slices : ∀ a : Fin 3, Slice true (roots minor3x16Atlas) (target minor3x16Atlas) (sliceDomain minor3x16Atlas a.val) (sliceBound minor3x16Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[(0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower
  · exact sliceSigned (ms:=[swapRows 33, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, (0x0, 0xaaaaaaaaaaaaaaaa, 1)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8p2_0 : Interval minor4xfee8Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8p3_0 : Interval minor4xfee8Atlas 3 0 48 := block_range (n:=48) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8p4_0 : Interval minor4xfee8Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8p4_64 : Interval minor4xfee8Atlas 4 64 54 := block_range (n:=54) (by decide +kernel)
theorem minor4xfee8q4_0_118 : Interval minor4xfee8Atlas 4 0 118 := concat minor4xfee8p4_0 minor4xfee8p4_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8p5_0 : Interval minor4xfee8Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8p6_0 : Interval minor4xfee8Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfee8Complete : Complete minor4xfee8Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfee8p2_0 i (Nat.zero_le i) hi
  · exact minor4xfee8p3_0 i (Nat.zero_le i) hi
  · exact minor4xfee8q4_0_118 i (Nat.zero_le i) hi
  · exact minor4xfee8p5_0 i (Nat.zero_le i) hi
  · exact minor4xfee8p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8Pair : properPairs (target minor4xfee8Atlas) (asRow minor4xfee8Pos) (asRow minor4xfee8Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8Lower (allSlice : ∀ j : Fin 4, Slice true (roots minor4xfee8Atlas) (target minor4xfee8Atlas) (sliceDomain minor4xfee8Atlas j.val) (sliceBound minor4xfee8Atlas j.val)) :
    Lower true (roots minor4xfee8Atlas) (target minor4xfee8Atlas) 7 := by
  have ready : Ready minor4xfee8Atlas (asRow minor4xfee8Pos) (asRow minor4xfee8Neg) := by
    refine ⟨minor4xfee8Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfee8Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfee8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee8Slices : ∀ a : Fin 4, Slice true (roots minor4xfee8Atlas) (target minor4xfee8Atlas) (sliceDomain minor4xfee8Atlas a.val) (sliceBound minor4xfee8Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[(0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 50, (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, (0x0, 0xaaaaaaaaaaaaaaaa, 1)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe80p3_0 : Interval minor4xfe80Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe80p4_0 : Interval minor4xfe80Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe80p5_0 : Interval minor4xfe80Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfe80Complete : Complete minor4xfe80Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfe80p3_0 i (Nat.zero_le i) hi
  · exact minor4xfe80p4_0 i (Nat.zero_le i) hi
  · exact minor4xfe80p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe80Pair : properPairs (target minor4xfe80Atlas) (asRow minor4xfe80Pos) (asRow minor4xfe80Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe80Lower (allSlice : ∀ j : Fin 6, Slice true (roots minor4xfe80Atlas) (target minor4xfe80Atlas) (sliceDomain minor4xfe80Atlas j.val) (sliceBound minor4xfe80Atlas j.val)) :
    Lower true (roots minor4xfe80Atlas) (target minor4xfe80Atlas) 6 := by
  have ready : Ready minor4xfe80Atlas (asRow minor4xfe80Pos) (asRow minor4xfe80Neg) := by
    refine ⟨minor4xfe80Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfe80Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfe80Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe80Slices : ∀ a : Fin 6, Slice true (roots minor4xfe80Atlas) (target minor4xfe80Atlas) (sliceDomain minor4xfe80Atlas a.val) (sliceBound minor4xfe80Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceDual (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf000f000f000f, 0xf000f000f000f000, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[(0x3333333333333333, 0xcccccccccccccccc, 2), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x55005500550055, 0xaa00aa00aa00aa00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, (0x2222222222222222, 0x4444444444444444, 2)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 50, (0xa0a0a0a0a0a0a0a, 0x5050505050505050, 4)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 50, (0xc0c0c0c0c0c0c0c, 0x3030303030303030, 4)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfec0p4_0 : Interval minor4xfec0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfec0Complete : Complete minor4xfec0Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfec0p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfec0Pair : properPairs (target minor4xfec0Atlas) (asRow minor4xfec0Pos) (asRow minor4xfec0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfec0Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor4xfec0Atlas) (target minor4xfec0Atlas) (sliceDomain minor4xfec0Atlas j.val) (sliceBound minor4xfec0Atlas j.val)) :
    Lower true (roots minor4xfec0Atlas) (target minor4xfec0Atlas) 5 := by
  have ready : Ready minor4xfec0Atlas (asRow minor4xfec0Pos) (asRow minor4xfec0Neg) := by
    refine ⟨minor4xfec0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfec0Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfec0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfec0Slices : ∀ a : Fin 1, Slice true (roots minor4xfec0Atlas) (target minor4xfec0Atlas) (sliceDomain minor4xfec0Atlas a.val) (sliceBound minor4xfec0Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, (0x0, 0xaaaaaaaaaaaaaaaa, 1)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xffe8p4_0 : Interval minor4xffe8Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xffe8Complete : Complete minor4xffe8Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xffe8p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xffe8Pair : properPairs (target minor4xffe8Atlas) (asRow minor4xffe8Pos) (asRow minor4xffe8Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xffe8Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor4xffe8Atlas) (target minor4xffe8Atlas) (sliceDomain minor4xffe8Atlas j.val) (sliceBound minor4xffe8Atlas j.val)) :
    Lower true (roots minor4xffe8Atlas) (target minor4xffe8Atlas) 5 := by
  have ready : Ready minor4xffe8Atlas (asRow minor4xffe8Pos) (asRow minor4xffe8Neg) := by
    refine ⟨minor4xffe8Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xffe8Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xffe8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 0, 8)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xffe8Slices : ∀ a : Fin 1, Slice true (roots minor4xffe8Atlas) (target minor4xffe8Atlas) (sliceDomain minor4xffe8Atlas a.val) (sliceBound minor4xffe8Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[(0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee0p4_0 : Interval minor4xfee0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfee0Complete : Complete minor4xfee0Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfee0p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee0Pair : properPairs (target minor4xfee0Atlas) (asRow minor4xfee0Pos) (asRow minor4xfee0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee0Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor4xfee0Atlas) (target minor4xfee0Atlas) (sliceDomain minor4xfee0Atlas j.val) (sliceBound minor4xfee0Atlas j.val)) :
    Lower true (roots minor4xfee0Atlas) (target minor4xfee0Atlas) 5 := by
  have ready : Ready minor4xfee0Atlas (asRow minor4xfee0Pos) (asRow minor4xfee0Neg) := by
    refine ⟨minor4xfee0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfee0Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfee0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee0Slices : ∀ a : Fin 1, Slice true (roots minor4xfee0Atlas) (target minor4xfee0Atlas) (sliceDomain minor4xfee0Atlas a.val) (sliceBound minor4xfee0Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee4p2_0 : Interval minor4xfee4Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee4p3_0 : Interval minor4xfee4Atlas 3 0 15 := block_range (n:=15) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee4p4_0 : Interval minor4xfee4Atlas 4 0 26 := block_range (n:=26) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee4p5_0 : Interval minor4xfee4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfee4Complete : Complete minor4xfee4Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfee4p2_0 i (Nat.zero_le i) hi
  · exact minor4xfee4p3_0 i (Nat.zero_le i) hi
  · exact minor4xfee4p4_0 i (Nat.zero_le i) hi
  · exact minor4xfee4p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee4Pair : properPairs (target minor4xfee4Atlas) (asRow minor4xfee4Pos) (asRow minor4xfee4Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee4Lower (allSlice : ∀ j : Fin 5, Slice true (roots minor4xfee4Atlas) (target minor4xfee4Atlas) (sliceDomain minor4xfee4Atlas j.val) (sliceBound minor4xfee4Atlas j.val)) :
    Lower true (roots minor4xfee4Atlas) (target minor4xfee4Atlas) 6 := by
  have ready : Ready minor4xfee4Atlas (asRow minor4xfee4Pos) (asRow minor4xfee4Neg) := by
    refine ⟨minor4xfee4Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfee4Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfee4Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfee4Slices : ∀ a : Fin 5, Slice true (roots minor4xfee4Atlas) (target minor4xfee4Atlas) (sliceDomain minor4xfee4Atlas a.val) (sliceBound minor4xfee4Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceDual (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor3x6Atlas) (G:=target minor3x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3x6Lower minor3x6Slices)
  · exact sliceDual (ms:=[swapRows 50, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4)]) (base:=roots minor3x6Atlas) (G:=target minor3x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3x6Lower minor3x6Slices)
  · exact sliceSigned (ms:=[(0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower
  · exact sliceSigned (ms:=[(0x0, 0xf0f0f0f0f0f0f0f0, 4), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfed0p3_0 : Interval minor4xfed0Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfed0p4_0 : Interval minor4xfed0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfed0Complete : Complete minor4xfed0Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfed0p3_0 i (Nat.zero_le i) hi
  · exact minor4xfed0p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfed0Pair : properPairs (target minor4xfed0Atlas) (asRow minor4xfed0Pos) (asRow minor4xfed0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfed0Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor4xfed0Atlas) (target minor4xfed0Atlas) (sliceDomain minor4xfed0Atlas j.val) (sliceBound minor4xfed0Atlas j.val)) :
    Lower true (roots minor4xfed0Atlas) (target minor4xfed0Atlas) 5 := by
  have ready : Ready minor4xfed0Atlas (asRow minor4xfed0Pos) (asRow minor4xfed0Neg) := by
    refine ⟨minor4xfed0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfed0Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfed0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfed0Slices : ∀ a : Fin 1, Slice true (roots minor4xfed0Atlas) (target minor4xfed0Atlas) (sliceDomain minor4xfed0Atlas a.val) (sliceBound minor4xfed0Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 33, (0x0, 0xcccccccccccccccc, 2), (0xf000f000f000f, 0xf000f000f000f000, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe40p3_0 : Interval minor4xfe40Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe40p4_0 : Interval minor4xfe40Atlas 4 0 28 := block_range (n:=28) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe40p5_0 : Interval minor4xfe40Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfe40Complete : Complete minor4xfe40Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfe40p3_0 i (Nat.zero_le i) hi
  · exact minor4xfe40p4_0 i (Nat.zero_le i) hi
  · exact minor4xfe40p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe40Pair : properPairs (target minor4xfe40Atlas) (asRow minor4xfe40Pos) (asRow minor4xfe40Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe40Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor4xfe40Atlas) (target minor4xfe40Atlas) (sliceDomain minor4xfe40Atlas j.val) (sliceBound minor4xfe40Atlas j.val)) :
    Lower true (roots minor4xfe40Atlas) (target minor4xfe40Atlas) 6 := by
  have ready : Ready minor4xfe40Atlas (asRow minor4xfe40Pos) (asRow minor4xfe40Neg) := by
    refine ⟨minor4xfe40Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfe40Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfe40Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe40Slices : ∀ a : Fin 1, Slice true (roots minor4xfe40Atlas) (target minor4xfe40Atlas) (sliceDomain minor4xfe40Atlas a.val) (sliceBound minor4xfe40Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, (0x0, 0xaaaaaaaaaaaaaaaa, 1)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60p2_0 : Interval minor4xfe60Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60p3_0 : Interval minor4xfe60Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60p4_0 : Interval minor4xfe60Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60p4_64 : Interval minor4xfe60Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem minor4xfe60q4_0_92 : Interval minor4xfe60Atlas 4 0 92 := concat minor4xfe60p4_0 minor4xfe60p4_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60p5_0 : Interval minor4xfe60Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60p6_0 : Interval minor4xfe60Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfe60Complete : Complete minor4xfe60Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfe60p2_0 i (Nat.zero_le i) hi
  · exact minor4xfe60p3_0 i (Nat.zero_le i) hi
  · exact minor4xfe60q4_0_92 i (Nat.zero_le i) hi
  · exact minor4xfe60p5_0 i (Nat.zero_le i) hi
  · exact minor4xfe60p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60Pair : properPairs (target minor4xfe60Atlas) (asRow minor4xfe60Pos) (asRow minor4xfe60Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60Lower (allSlice : ∀ j : Fin 6, Slice true (roots minor4xfe60Atlas) (target minor4xfe60Atlas) (sliceDomain minor4xfe60Atlas j.val) (sliceBound minor4xfe60Atlas j.val)) :
    Lower true (roots minor4xfe60Atlas) (target minor4xfe60Atlas) 7 := by
  have ready : Ready minor4xfe60Atlas (asRow minor4xfe60Pos) (asRow minor4xfe60Neg) := by
    refine ⟨minor4xfe60Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfe60Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfe60Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe60Slices : ∀ a : Fin 6, Slice true (roots minor4xfe60Atlas) (target minor4xfe60Atlas) (sliceDomain minor4xfe60Atlas a.val) (sliceBound minor4xfe60Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[(0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3x6Atlas) (G:=target minor3x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3x6Lower minor3x6Slices)
  · exact sliceSigned (ms:=[(0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xf000f000f000f, 0xf000f000f000f000, 8)]) (base:=roots minor3xe6Atlas) (G:=target minor3xe6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3xe6Lower minor3xe6Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, (0x0, 0xaaaaaaaaaaaaaaaa, 1)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceDual (ms:=[swapRows 50, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0x0, 4)]) (base:=roots minor3x6Atlas) (G:=target minor3x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3x6Lower minor3x6Slices)
  · exact sliceSigned (ms:=[(0xf0f0f0f0f0f0f0f, 0x0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64p2_0 : Interval minor4xfe64Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64p3_0 : Interval minor4xfe64Atlas 3 0 47 := block_range (n:=47) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64p4_0 : Interval minor4xfe64Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64p4_64 : Interval minor4xfe64Atlas 4 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64p4_128 : Interval minor4xfe64Atlas 4 128 57 := block_range (n:=57) (by decide +kernel)
theorem minor4xfe64q4_0_128 : Interval minor4xfe64Atlas 4 0 128 := concat minor4xfe64p4_0 minor4xfe64p4_64
theorem minor4xfe64q4_0_185 : Interval minor4xfe64Atlas 4 0 185 := concat minor4xfe64q4_0_128 minor4xfe64p4_128
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64p5_0 : Interval minor4xfe64Atlas 5 0 26 := block_range (n:=26) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64p6_0 : Interval minor4xfe64Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfe64Complete : Complete minor4xfe64Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfe64p2_0 i (Nat.zero_le i) hi
  · exact minor4xfe64p3_0 i (Nat.zero_le i) hi
  · exact minor4xfe64q4_0_185 i (Nat.zero_le i) hi
  · exact minor4xfe64p5_0 i (Nat.zero_le i) hi
  · exact minor4xfe64p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64Pair : properPairs (target minor4xfe64Atlas) (asRow minor4xfe64Pos) (asRow minor4xfe64Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64Lower (allSlice : ∀ j : Fin 11, Slice true (roots minor4xfe64Atlas) (target minor4xfe64Atlas) (sliceDomain minor4xfe64Atlas j.val) (sliceBound minor4xfe64Atlas j.val)) :
    Lower true (roots minor4xfe64Atlas) (target minor4xfe64Atlas) 7 := by
  have ready : Ready minor4xfe64Atlas (asRow minor4xfe64Pos) (asRow minor4xfe64Neg) := by
    refine ⟨minor4xfe64Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfe64Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfe64Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe64Slices : ∀ a : Fin 11, Slice true (roots minor4xfe64Atlas) (target minor4xfe64Atlas) (sliceDomain minor4xfe64Atlas a.val) (sliceBound minor4xfe64Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceDual (ms:=[(0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe6Atlas) (G:=target minor3xe6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3xe6Lower minor3xe6Slices)
  · exact sliceSigned (ms:=[(0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xf000f000f000f, 0xf000f000f000f000, 8)]) (base:=roots minor3xe6Atlas) (G:=target minor3xe6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3xe6Lower minor3xe6Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor3xe6Atlas) (G:=target minor3xe6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3xe6Lower minor3xe6Slices)
  · exact sliceDual (ms:=[swapRows 50, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4)]) (base:=roots minor3x6Atlas) (G:=target minor3x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3x6Lower minor3x6Slices)
  · exact sliceSigned (ms:=[swapRows 50, (0xa0a0a0a0a0a0a0a, 0x5050505050505050, 4)]) (base:=roots minor3xe6Atlas) (G:=target minor3xe6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3xe6Lower minor3xe6Slices)
  · exact sliceDual (ms:=[swapRows 50, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0x0, 4)]) (base:=roots minor3x6Atlas) (G:=target minor3x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3x6Lower minor3x6Slices)
  · exact sliceSigned (ms:=[(0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower
  · exact sliceSigned (ms:=[(0xa0a0a0a0a0a0a0a, 0x5050505050505050, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower
  · exact sliceSigned (ms:=[(0xf0f0f0f0f0f0f0f, 0x0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower
  · exact sliceSigned (ms:=[(0x0, 0xf0f0f0f0f0f0f0f0, 4), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor2x6Atlas) (G:=target minor2x6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor2x6Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe90p5_0 : Interval minor4xfe90Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor4xfe90Complete : Complete minor4xfe90Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor4xfe90p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe90Pair : properPairs (target minor4xfe90Atlas) (asRow minor4xfe90Pos) (asRow minor4xfe90Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe90Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor4xfe90Atlas) (target minor4xfe90Atlas) (sliceDomain minor4xfe90Atlas j.val) (sliceBound minor4xfe90Atlas j.val)) :
    Lower true (roots minor4xfe90Atlas) (target minor4xfe90Atlas) 6 := by
  have ready : Ready minor4xfe90Atlas (asRow minor4xfe90Pos) (asRow minor4xfe90Neg) := by
    refine ⟨minor4xfe90Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor4xfe90Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor4xfe90Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor4xfe90Slices : ∀ a : Fin 1, Slice true (roots minor4xfe90Atlas) (target minor4xfe90Atlas) (sliceDomain minor4xfe90Atlas a.val) (sliceBound minor4xfe90Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceDual (ms:=[(0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xf000f000f000f, 0xf000f000f000f000, 8)]) (base:=roots minor3x16Atlas) (G:=target minor3x16Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor3x16Lower minor3x16Slices)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80p4_0 : Interval minor5xfffefc80Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80p5_0 : Interval minor5xfffefc80Atlas 5 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80p5_64 : Interval minor5xfffefc80Atlas 5 64 29 := block_range (n:=29) (by decide +kernel)
theorem minor5xfffefc80q5_0_93 : Interval minor5xfffefc80Atlas 5 0 93 := concat minor5xfffefc80p5_0 minor5xfffefc80p5_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80p6_0 : Interval minor5xfffefc80Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80p7_0 : Interval minor5xfffefc80Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor5xfffefc80Complete : Complete minor5xfffefc80Atlas := by
  intro k hk i hi
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor5xfffefc80p4_0 i (Nat.zero_le i) hi
  · exact minor5xfffefc80q5_0_93 i (Nat.zero_le i) hi
  · exact minor5xfffefc80p6_0 i (Nat.zero_le i) hi
  · exact minor5xfffefc80p7_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80Pair : properPairs (target minor5xfffefc80Atlas) (asRow minor5xfffefc80Pos) (asRow minor5xfffefc80Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80Lower (allSlice : ∀ j : Fin 9, Slice true (roots minor5xfffefc80Atlas) (target minor5xfffefc80Atlas) (sliceDomain minor5xfffefc80Atlas j.val) (sliceBound minor5xfffefc80Atlas j.val)) :
    Lower true (roots minor5xfffefc80Atlas) (target minor5xfffefc80Atlas) 8 := by
  have ready : Ready minor5xfffefc80Atlas (asRow minor5xfffefc80Pos) (asRow minor5xfffefc80Neg) := by
    refine ⟨minor5xfffefc80Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor5xfffefc80Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor5xfffefc80Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffefc80Slices : ∀ a : Fin 9, Slice true (roots minor5xfffefc80Atlas) (target minor5xfffefc80Atlas) (sliceDomain minor5xfffefc80Atlas a.val) (sliceBound minor5xfffefc80Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x555500005555, 0xaaaa0000aaaa0000, 16)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, swapRows 65, (0x2222222222222222, 0x4444444444444444, 2)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[swapRows 50, swapRows 66, (0xa0a0a0a0a0a0a0a, 0x5050505050505050, 4)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[swapRows 67, (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)
  · exact sliceDual (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 50, swapRows 66, (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[(0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xf0f00000f0f, 0xf0f00000f0f00000, 16)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, swapRows 65, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, swapRows 64, (0x5555555555555555, 0x0, 1)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p4_0 : Interval minor5xfffcfa80Atlas 4 0 22 := block_range (n:=22) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p5_0 : Interval minor5xfffcfa80Atlas 5 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p5_64 : Interval minor5xfffcfa80Atlas 5 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p5_128 : Interval minor5xfffcfa80Atlas 5 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p5_192 : Interval minor5xfffcfa80Atlas 5 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p5_256 : Interval minor5xfffcfa80Atlas 5 256 22 := block_range (n:=22) (by decide +kernel)
theorem minor5xfffcfa80q5_0_128 : Interval minor5xfffcfa80Atlas 5 0 128 := concat minor5xfffcfa80p5_0 minor5xfffcfa80p5_64
theorem minor5xfffcfa80q5_128_128 : Interval minor5xfffcfa80Atlas 5 128 128 := concat minor5xfffcfa80p5_128 minor5xfffcfa80p5_192
theorem minor5xfffcfa80q5_0_256 : Interval minor5xfffcfa80Atlas 5 0 256 := concat minor5xfffcfa80q5_0_128 minor5xfffcfa80q5_128_128
theorem minor5xfffcfa80q5_0_278 : Interval minor5xfffcfa80Atlas 5 0 278 := concat minor5xfffcfa80q5_0_256 minor5xfffcfa80p5_256
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p6_0 : Interval minor5xfffcfa80Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80p7_0 : Interval minor5xfffcfa80Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor5xfffcfa80Complete : Complete minor5xfffcfa80Atlas := by
  intro k hk i hi
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor5xfffcfa80p4_0 i (Nat.zero_le i) hi
  · exact minor5xfffcfa80q5_0_278 i (Nat.zero_le i) hi
  · exact minor5xfffcfa80p6_0 i (Nat.zero_le i) hi
  · exact minor5xfffcfa80p7_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80Pair : properPairs (target minor5xfffcfa80Atlas) (asRow minor5xfffcfa80Pos) (asRow minor5xfffcfa80Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80Lower (allSlice : ∀ j : Fin 17, Slice true (roots minor5xfffcfa80Atlas) (target minor5xfffcfa80Atlas) (sliceDomain minor5xfffcfa80Atlas j.val) (sliceBound minor5xfffcfa80Atlas j.val)) :
    Lower true (roots minor5xfffcfa80Atlas) (target minor5xfffcfa80Atlas) 8 := by
  have ready : Ready minor5xfffcfa80Atlas (asRow minor5xfffcfa80Pos) (asRow minor5xfffcfa80Neg) := by
    refine ⟨minor5xfffcfa80Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor5xfffcfa80Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor5xfffcfa80Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa80Slices : ∀ a : Fin 17, Slice true (roots minor5xfffcfa80Atlas) (target minor5xfffcfa80Atlas) (sliceDomain minor5xfffcfa80Atlas a.val) (sliceBound minor5xfffcfa80Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, swapRows 65, (0x2222222222222222, 0x4444444444444444, 2)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceDual (ms:=[swapRows 16, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 67, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[(0x3333333333333333, 0xcccccccccccccccc, 2), (0x333300003333, 0xcccc0000cccc0000, 16)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceSigned (ms:=[swapRows 67, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, swapRows 64, (0x0, 0xaaaaaaaaaaaaaaaa, 1)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x555500005555, 0xaaaa0000aaaa0000, 16)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 67, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x55005500550055, 0xaa00aa00aa00aa00, 8)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 64, (0x5555555555555555, 0x0, 1)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, swapRows 65, (0x3333333333333333, 0x0, 2)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[(0x3333333333333333, 0xcccccccccccccccc, 2), (0x33003300330033, 0xcc00cc00cc00cc00, 8), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 50, (0xc0c0c0c0c0c0c0c, 0x3030303030303030, 4), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[(0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x0, 0xff00ff00ff00ff00, 8), (0x555500005555, 0xaaaa0000aaaa0000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 66, (0xa0a0a0a0a0a0a0a, 0x5050505050505050, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 49, swapRows 66, (0x2222222222222222, 0x4444444444444444, 2), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 32, swapRows 49, swapRows 64, (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffceaa8p6_0 : Interval minor5xfffceaa8Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor5xfffceaa8Complete : Complete minor5xfffceaa8Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor5xfffceaa8p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffceaa8Pair : properPairs (target minor5xfffceaa8Atlas) (asRow minor5xfffceaa8Pos) (asRow minor5xfffceaa8Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffceaa8Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor5xfffceaa8Atlas) (target minor5xfffceaa8Atlas) (sliceDomain minor5xfffceaa8Atlas j.val) (sliceBound minor5xfffceaa8Atlas j.val)) :
    Lower true (roots minor5xfffceaa8Atlas) (target minor5xfffceaa8Atlas) 7 := by
  have ready : Ready minor5xfffceaa8Atlas (asRow minor5xfffceaa8Pos) (asRow minor5xfffceaa8Neg) := by
    refine ⟨minor5xfffceaa8Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor5xfffceaa8Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor5xfffceaa8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffceaa8Slices : ∀ a : Fin 1, Slice true (roots minor5xfffceaa8Atlas) (target minor5xfffceaa8Atlas) (sliceDomain minor5xfffceaa8Atlas a.val) (sliceBound minor5xfffceaa8Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0p4_0 : Interval minor5xfff8eca0Atlas 4 0 34 := block_range (n:=34) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0p5_0 : Interval minor5xfff8eca0Atlas 5 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0p5_64 : Interval minor5xfff8eca0Atlas 5 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0p5_128 : Interval minor5xfff8eca0Atlas 5 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0p5_192 : Interval minor5xfff8eca0Atlas 5 192 62 := block_range (n:=62) (by decide +kernel)
theorem minor5xfff8eca0q5_0_128 : Interval minor5xfff8eca0Atlas 5 0 128 := concat minor5xfff8eca0p5_0 minor5xfff8eca0p5_64
theorem minor5xfff8eca0q5_128_126 : Interval minor5xfff8eca0Atlas 5 128 126 := concat minor5xfff8eca0p5_128 minor5xfff8eca0p5_192
theorem minor5xfff8eca0q5_0_254 : Interval minor5xfff8eca0Atlas 5 0 254 := concat minor5xfff8eca0q5_0_128 minor5xfff8eca0q5_128_126
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0p6_0 : Interval minor5xfff8eca0Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0p7_0 : Interval minor5xfff8eca0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor5xfff8eca0Complete : Complete minor5xfff8eca0Atlas := by
  intro k hk i hi
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor5xfff8eca0p4_0 i (Nat.zero_le i) hi
  · exact minor5xfff8eca0q5_0_254 i (Nat.zero_le i) hi
  · exact minor5xfff8eca0p6_0 i (Nat.zero_le i) hi
  · exact minor5xfff8eca0p7_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0Pair : properPairs (target minor5xfff8eca0Atlas) (asRow minor5xfff8eca0Pos) (asRow minor5xfff8eca0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0Lower (allSlice : ∀ j : Fin 27, Slice true (roots minor5xfff8eca0Atlas) (target minor5xfff8eca0Atlas) (sliceDomain minor5xfff8eca0Atlas j.val) (sliceBound minor5xfff8eca0Atlas j.val)) :
    Lower true (roots minor5xfff8eca0Atlas) (target minor5xfff8eca0Atlas) 8 := by
  have ready : Ready minor5xfff8eca0Atlas (asRow minor5xfff8eca0Pos) (asRow minor5xfff8eca0Neg) := by
    refine ⟨minor5xfff8eca0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor5xfff8eca0Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor5xfff8eca0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8eca0Slices : ∀ a : Fin 27, Slice true (roots minor5xfff8eca0Atlas) (target minor5xfff8eca0Atlas) (sliceDomain minor5xfff8eca0Atlas a.val) (sliceBound minor5xfff8eca0Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 32, swapRows 66, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 67, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x55005500550055, 0xaa00aa00aa00aa00, 8)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceSigned (ms:=[swapRows 66, (0xf000f000f000f00, 0xf000f000f000f0, 4)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)
  · exact sliceDual (ms:=[swapRows 16, swapRows 66, swapRows 50, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 48, swapRows 16, swapRows 33, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xff000000ff, 0xff000000ff000000, 16)]) (base:=roots minor4xfed0Atlas) (G:=target minor4xfed0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfed0Lower minor4xfed0Slices)
  · exact sliceDual (ms:=[swapRows 66, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 32, (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xf0f00000f0f, 0xf0f00000f0f00000, 16)]) (base:=roots minor4xfed0Atlas) (G:=target minor4xfed0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfed0Lower minor4xfed0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 67, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 50, swapRows 66, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x505050505050505, 0xa0a0a0a0a0a0a0a0, 4)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 65, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x1111111111111111, 0x8888888888888888, 2)]) (base:=roots minor4xfed0Atlas) (G:=target minor4xfed0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfed0Lower minor4xfed0Slices)
  · exact sliceSigned (ms:=[swapRows 32, swapRows 49, swapRows 65, (0x2222222222222222, 0x4444444444444444, 2)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 64, (0x5500550055005500, 0xaa00aa00aa00aa, 1)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 32, swapRows 48, (0xaaaa0000aaaa, 0x5555000055550000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 66, swapRows 32, (0x5555555555555555, 0x0, 1)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 49, swapRows 66, (0xc0c0c0c0c0c0c0c, 0x3030303030303030, 4)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 48, swapRows 16, (0xcccc0000cccc, 0x3333000033330000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x3333333333333333, 0x0, 2)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 66, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x2222222222222222, 0x4444444444444444, 2), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[(0x0, 0xff00ff00ff00ff00, 8), (0xcccc0000cccc, 0x3333000033330000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x3333333333333333, 0x0, 2), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 66, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0x55005500550055, 0xaa00aa00aa00aa00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 49, swapRows 66, (0x2222222222222222, 0x4444444444444444, 2), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 50, (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0xaaaa0000aaaa, 0x5555000055550000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 66, (0x5555555555555555, 0x0, 1), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x0, 0xcccccccccccccccc, 2), (0xaa00aa00aa00aa, 0x5500550055005500, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 66, (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0xc0c0c0c0c0c0c0c, 0x3030303030303030, 4)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8cc80p5_0 : Interval minor5xfff8cc80Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8cc80p6_0 : Interval minor5xfff8cc80Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor5xfff8cc80Complete : Complete minor5xfff8cc80Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor5xfff8cc80p5_0 i (Nat.zero_le i) hi
  · exact minor5xfff8cc80p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8cc80Pair : properPairs (target minor5xfff8cc80Atlas) (asRow minor5xfff8cc80Pos) (asRow minor5xfff8cc80Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8cc80Lower (allSlice : ∀ j : Fin 7, Slice true (roots minor5xfff8cc80Atlas) (target minor5xfff8cc80Atlas) (sliceDomain minor5xfff8cc80Atlas j.val) (sliceBound minor5xfff8cc80Atlas j.val)) :
    Lower true (roots minor5xfff8cc80Atlas) (target minor5xfff8cc80Atlas) 7 := by
  have ready : Ready minor5xfff8cc80Atlas (asRow minor5xfff8cc80Pos) (asRow minor5xfff8cc80Neg) := by
    refine ⟨minor5xfff8cc80Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor5xfff8cc80Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor5xfff8cc80Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 2, 10), (inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfff8cc80Slices : ∀ a : Fin 7, Slice true (roots minor5xfff8cc80Atlas) (target minor5xfff8cc80Atlas) (sliceDomain minor5xfff8cc80Atlas a.val) (sliceBound minor5xfff8cc80Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 16, swapRows 67, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x33003300330033, 0xcc00cc00cc00cc00, 8)]) (base:=roots minor4xfe40Atlas) (G:=target minor4xfe40Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe40Lower minor4xfe40Slices)
  · exact sliceDual (ms:=[swapRows 67, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceDual (ms:=[swapRows 66, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 32, swapRows 49, swapRows 65, (0x2222222222222222, 0x4444444444444444, 2)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceSigned (ms:=[swapRows 32, swapRows 48, (0xaaaa0000aaaa, 0x5555000055550000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 32, swapRows 49, swapRows 16, swapRows 64, (0x5555555555555555, 0x0, 1)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x3333333333333333, 0x0, 2)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa00p5_0 : Interval minor5xfffcfa00Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem minor5xfffcfa00Complete : Complete minor5xfffcfa00Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact minor5xfffcfa00p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa00Pair : properPairs (target minor5xfffcfa00Atlas) (asRow minor5xfffcfa00Pos) (asRow minor5xfffcfa00Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa00Lower (allSlice : ∀ j : Fin 1, Slice true (roots minor5xfffcfa00Atlas) (target minor5xfffcfa00Atlas) (sliceDomain minor5xfffcfa00Atlas j.val) (sliceBound minor5xfffcfa00Atlas j.val)) :
    Lower true (roots minor5xfffcfa00Atlas) (target minor5xfffcfa00Atlas) 6 := by
  have ready : Ready minor5xfffcfa00Atlas (asRow minor5xfffcfa00Pos) (asRow minor5xfffcfa00Neg) := by
    refine ⟨minor5xfffcfa00Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip minor5xfffcfa00Atlas k i % 65536 - 1, ht⟩
  exact frozen ready minor5xfffcfa00Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 16, 18), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem minor5xfffcfa00Slices : ∀ a : Fin 1, Slice true (roots minor5xfffcfa00Atlas) (target minor5xfffcfa00Atlas) (sliceDomain minor5xfffcfa00Atlas a.val) (sliceBound minor5xfffcfa00Atlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp5_0 : Interval mainAtlas 5 0 2 := block_range (n:=2) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_0 : Interval mainAtlas 6 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_64 : Interval mainAtlas 6 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_128 : Interval mainAtlas 6 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_192 : Interval mainAtlas 6 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_256 : Interval mainAtlas 6 256 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_320 : Interval mainAtlas 6 320 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_384 : Interval mainAtlas 6 384 9 := block_range (n:=9) (by decide +kernel)
theorem mainq6_0_128 : Interval mainAtlas 6 0 128 := concat mainp6_0 mainp6_64
theorem mainq6_128_128 : Interval mainAtlas 6 128 128 := concat mainp6_128 mainp6_192
theorem mainq6_256_128 : Interval mainAtlas 6 256 128 := concat mainp6_256 mainp6_320
theorem mainq6_0_256 : Interval mainAtlas 6 0 256 := concat mainq6_0_128 mainq6_128_128
theorem mainq6_256_137 : Interval mainAtlas 6 256 137 := concat mainq6_256_128 mainp6_384
theorem mainq6_0_393 : Interval mainAtlas 6 0 393 := concat mainq6_0_256 mainq6_256_137
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_0 : Interval mainAtlas 7 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_64 : Interval mainAtlas 7 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_128 : Interval mainAtlas 7 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_192 : Interval mainAtlas 7 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_256 : Interval mainAtlas 7 256 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_320 : Interval mainAtlas 7 320 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_384 : Interval mainAtlas 7 384 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_448 : Interval mainAtlas 7 448 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_512 : Interval mainAtlas 7 512 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_576 : Interval mainAtlas 7 576 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_640 : Interval mainAtlas 7 640 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_704 : Interval mainAtlas 7 704 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_768 : Interval mainAtlas 7 768 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_832 : Interval mainAtlas 7 832 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_896 : Interval mainAtlas 7 896 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_960 : Interval mainAtlas 7 960 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1024 : Interval mainAtlas 7 1024 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1088 : Interval mainAtlas 7 1088 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1152 : Interval mainAtlas 7 1152 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1216 : Interval mainAtlas 7 1216 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1280 : Interval mainAtlas 7 1280 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1344 : Interval mainAtlas 7 1344 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1408 : Interval mainAtlas 7 1408 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1472 : Interval mainAtlas 7 1472 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1536 : Interval mainAtlas 7 1536 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1600 : Interval mainAtlas 7 1600 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1664 : Interval mainAtlas 7 1664 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1728 : Interval mainAtlas 7 1728 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1792 : Interval mainAtlas 7 1792 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1856 : Interval mainAtlas 7 1856 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1920 : Interval mainAtlas 7 1920 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_1984 : Interval mainAtlas 7 1984 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2048 : Interval mainAtlas 7 2048 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2112 : Interval mainAtlas 7 2112 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2176 : Interval mainAtlas 7 2176 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2240 : Interval mainAtlas 7 2240 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2304 : Interval mainAtlas 7 2304 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2368 : Interval mainAtlas 7 2368 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2432 : Interval mainAtlas 7 2432 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2496 : Interval mainAtlas 7 2496 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2560 : Interval mainAtlas 7 2560 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2624 : Interval mainAtlas 7 2624 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2688 : Interval mainAtlas 7 2688 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2752 : Interval mainAtlas 7 2752 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2816 : Interval mainAtlas 7 2816 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2880 : Interval mainAtlas 7 2880 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_2944 : Interval mainAtlas 7 2944 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3008 : Interval mainAtlas 7 3008 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3072 : Interval mainAtlas 7 3072 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3136 : Interval mainAtlas 7 3136 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3200 : Interval mainAtlas 7 3200 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3264 : Interval mainAtlas 7 3264 45 := block_range (n:=45) (by decide +kernel)
theorem mainq7_0_128 : Interval mainAtlas 7 0 128 := concat mainp7_0 mainp7_64
theorem mainq7_128_128 : Interval mainAtlas 7 128 128 := concat mainp7_128 mainp7_192
theorem mainq7_256_128 : Interval mainAtlas 7 256 128 := concat mainp7_256 mainp7_320
theorem mainq7_384_128 : Interval mainAtlas 7 384 128 := concat mainp7_384 mainp7_448
theorem mainq7_512_128 : Interval mainAtlas 7 512 128 := concat mainp7_512 mainp7_576
theorem mainq7_640_128 : Interval mainAtlas 7 640 128 := concat mainp7_640 mainp7_704
theorem mainq7_768_128 : Interval mainAtlas 7 768 128 := concat mainp7_768 mainp7_832
theorem mainq7_896_128 : Interval mainAtlas 7 896 128 := concat mainp7_896 mainp7_960
theorem mainq7_1024_128 : Interval mainAtlas 7 1024 128 := concat mainp7_1024 mainp7_1088
theorem mainq7_1152_128 : Interval mainAtlas 7 1152 128 := concat mainp7_1152 mainp7_1216
theorem mainq7_1280_128 : Interval mainAtlas 7 1280 128 := concat mainp7_1280 mainp7_1344
theorem mainq7_1408_128 : Interval mainAtlas 7 1408 128 := concat mainp7_1408 mainp7_1472
theorem mainq7_1536_128 : Interval mainAtlas 7 1536 128 := concat mainp7_1536 mainp7_1600
theorem mainq7_1664_128 : Interval mainAtlas 7 1664 128 := concat mainp7_1664 mainp7_1728
theorem mainq7_1792_128 : Interval mainAtlas 7 1792 128 := concat mainp7_1792 mainp7_1856
theorem mainq7_1920_128 : Interval mainAtlas 7 1920 128 := concat mainp7_1920 mainp7_1984
theorem mainq7_2048_128 : Interval mainAtlas 7 2048 128 := concat mainp7_2048 mainp7_2112
theorem mainq7_2176_128 : Interval mainAtlas 7 2176 128 := concat mainp7_2176 mainp7_2240
theorem mainq7_2304_128 : Interval mainAtlas 7 2304 128 := concat mainp7_2304 mainp7_2368
theorem mainq7_2432_128 : Interval mainAtlas 7 2432 128 := concat mainp7_2432 mainp7_2496
theorem mainq7_2560_128 : Interval mainAtlas 7 2560 128 := concat mainp7_2560 mainp7_2624
theorem mainq7_2688_128 : Interval mainAtlas 7 2688 128 := concat mainp7_2688 mainp7_2752
theorem mainq7_2816_128 : Interval mainAtlas 7 2816 128 := concat mainp7_2816 mainp7_2880
theorem mainq7_2944_128 : Interval mainAtlas 7 2944 128 := concat mainp7_2944 mainp7_3008
theorem mainq7_3072_128 : Interval mainAtlas 7 3072 128 := concat mainp7_3072 mainp7_3136
theorem mainq7_3200_109 : Interval mainAtlas 7 3200 109 := concat mainp7_3200 mainp7_3264
theorem mainq7_0_256 : Interval mainAtlas 7 0 256 := concat mainq7_0_128 mainq7_128_128
theorem mainq7_256_256 : Interval mainAtlas 7 256 256 := concat mainq7_256_128 mainq7_384_128
theorem mainq7_512_256 : Interval mainAtlas 7 512 256 := concat mainq7_512_128 mainq7_640_128
theorem mainq7_768_256 : Interval mainAtlas 7 768 256 := concat mainq7_768_128 mainq7_896_128
theorem mainq7_1024_256 : Interval mainAtlas 7 1024 256 := concat mainq7_1024_128 mainq7_1152_128
theorem mainq7_1280_256 : Interval mainAtlas 7 1280 256 := concat mainq7_1280_128 mainq7_1408_128
theorem mainq7_1536_256 : Interval mainAtlas 7 1536 256 := concat mainq7_1536_128 mainq7_1664_128
theorem mainq7_1792_256 : Interval mainAtlas 7 1792 256 := concat mainq7_1792_128 mainq7_1920_128
theorem mainq7_2048_256 : Interval mainAtlas 7 2048 256 := concat mainq7_2048_128 mainq7_2176_128
theorem mainq7_2304_256 : Interval mainAtlas 7 2304 256 := concat mainq7_2304_128 mainq7_2432_128
theorem mainq7_2560_256 : Interval mainAtlas 7 2560 256 := concat mainq7_2560_128 mainq7_2688_128
theorem mainq7_2816_256 : Interval mainAtlas 7 2816 256 := concat mainq7_2816_128 mainq7_2944_128
theorem mainq7_3072_237 : Interval mainAtlas 7 3072 237 := concat mainq7_3072_128 mainq7_3200_109
theorem mainq7_0_512 : Interval mainAtlas 7 0 512 := concat mainq7_0_256 mainq7_256_256
theorem mainq7_512_512 : Interval mainAtlas 7 512 512 := concat mainq7_512_256 mainq7_768_256
theorem mainq7_1024_512 : Interval mainAtlas 7 1024 512 := concat mainq7_1024_256 mainq7_1280_256
theorem mainq7_1536_512 : Interval mainAtlas 7 1536 512 := concat mainq7_1536_256 mainq7_1792_256
theorem mainq7_2048_512 : Interval mainAtlas 7 2048 512 := concat mainq7_2048_256 mainq7_2304_256
theorem mainq7_2560_512 : Interval mainAtlas 7 2560 512 := concat mainq7_2560_256 mainq7_2816_256
theorem mainq7_0_1024 : Interval mainAtlas 7 0 1024 := concat mainq7_0_512 mainq7_512_512
theorem mainq7_1024_1024 : Interval mainAtlas 7 1024 1024 := concat mainq7_1024_512 mainq7_1536_512
theorem mainq7_2048_1024 : Interval mainAtlas 7 2048 1024 := concat mainq7_2048_512 mainq7_2560_512
theorem mainq7_0_2048 : Interval mainAtlas 7 0 2048 := concat mainq7_0_1024 mainq7_1024_1024
theorem mainq7_2048_1261 : Interval mainAtlas 7 2048 1261 := concat mainq7_2048_1024 mainq7_3072_237
theorem mainq7_0_3309 : Interval mainAtlas 7 0 3309 := concat mainq7_0_2048 mainq7_2048_1261
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_0 : Interval mainAtlas 8 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_64 : Interval mainAtlas 8 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_128 : Interval mainAtlas 8 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_192 : Interval mainAtlas 8 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_256 : Interval mainAtlas 8 256 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_320 : Interval mainAtlas 8 320 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_384 : Interval mainAtlas 8 384 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_448 : Interval mainAtlas 8 448 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_512 : Interval mainAtlas 8 512 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_576 : Interval mainAtlas 8 576 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_640 : Interval mainAtlas 8 640 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_704 : Interval mainAtlas 8 704 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_768 : Interval mainAtlas 8 768 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_832 : Interval mainAtlas 8 832 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_896 : Interval mainAtlas 8 896 15 := block_range (n:=15) (by decide +kernel)
theorem mainq8_0_128 : Interval mainAtlas 8 0 128 := concat mainp8_0 mainp8_64
theorem mainq8_128_128 : Interval mainAtlas 8 128 128 := concat mainp8_128 mainp8_192
theorem mainq8_256_128 : Interval mainAtlas 8 256 128 := concat mainp8_256 mainp8_320
theorem mainq8_384_128 : Interval mainAtlas 8 384 128 := concat mainp8_384 mainp8_448
theorem mainq8_512_128 : Interval mainAtlas 8 512 128 := concat mainp8_512 mainp8_576
theorem mainq8_640_128 : Interval mainAtlas 8 640 128 := concat mainp8_640 mainp8_704
theorem mainq8_768_128 : Interval mainAtlas 8 768 128 := concat mainp8_768 mainp8_832
theorem mainq8_0_256 : Interval mainAtlas 8 0 256 := concat mainq8_0_128 mainq8_128_128
theorem mainq8_256_256 : Interval mainAtlas 8 256 256 := concat mainq8_256_128 mainq8_384_128
theorem mainq8_512_256 : Interval mainAtlas 8 512 256 := concat mainq8_512_128 mainq8_640_128
theorem mainq8_768_143 : Interval mainAtlas 8 768 143 := concat mainq8_768_128 mainp8_896
theorem mainq8_0_512 : Interval mainAtlas 8 0 512 := concat mainq8_0_256 mainq8_256_256
theorem mainq8_512_399 : Interval mainAtlas 8 512 399 := concat mainq8_512_256 mainq8_768_143
theorem mainq8_0_911 : Interval mainAtlas 8 0 911 := concat mainq8_0_512 mainq8_512_399
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp9_0 : Interval mainAtlas 9 0 34 := block_range (n:=34) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp10_0 : Interval mainAtlas 10 0 1 := block_range (n:=1) (by decide +kernel)
theorem mainComplete : Complete mainAtlas := by
  intro k hk i hi
  change k ≤ 10 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact mainp5_0 i (Nat.zero_le i) hi
  · exact mainq6_0_393 i (Nat.zero_le i) hi
  · exact mainq7_0_3309 i (Nat.zero_le i) hi
  · exact mainq8_0_911 i (Nat.zero_le i) hi
  · exact mainp9_0 i (Nat.zero_le i) hi
  · exact mainp10_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainPair : properPairs (target mainAtlas) (asRow mainPos) (asRow mainNeg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainLower (allSlice : ∀ j : Fin 67, Slice true (roots mainAtlas) (target mainAtlas) (sliceDomain mainAtlas j.val) (sliceBound mainAtlas j.val)) :
    Lower true (roots mainAtlas) (target mainAtlas) 11 := by
  have ready : Ready mainAtlas (asRow mainPos) (asRow mainNeg) := by
    refine ⟨mainPair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip mainAtlas k i % 65536 - 1, ht⟩
  exact frozen ready mainComplete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 17, 25), (inputs.getD 4 zero, 3, 19), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainSlices : ∀ a : Fin 67, Slice true (roots mainAtlas) (target mainAtlas) (sliceDomain mainAtlas a.val) (sliceBound mainAtlas a.val) := by
  intro a
  fin_cases a
  · exact sliceSigned (ms:=[swapRows 48, swapRows 82, swapRows 32, (0x5555555555555555, 0x0, 1)]) (base:=roots minor5xfffefc80Atlas) (G:=target minor5xfffefc80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfffefc80Lower minor5xfffefc80Slices)
  · exact sliceDual (ms:=[swapRows 48, swapRows 81, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xffffffff, 0xffffffff00000000, 32), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor5xfffcfa80Atlas) (G:=target minor5xfffcfa80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfffcfa80Lower minor5xfffcfa80Slices)
  · exact sliceDual (ms:=[swapRows 50, swapRows 82, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xffffffff, 0xffffffff00000000, 32), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor5xfffceaa8Atlas) (G:=target minor5xfffceaa8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfffceaa8Lower minor5xfffceaa8Slices)
  · exact sliceSigned (ms:=[swapRows 81, swapRows 66, swapRows 49, (0xff00ff00ff00ff, 0x0, 8)]) (base:=roots minor5xfff8eca0Atlas) (G:=target minor5xfff8eca0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfff8eca0Lower minor5xfff8eca0Slices)
  · exact sliceSigned (ms:=[swapRows 80, swapRows 50, swapRows 64, (0xffff0000ffff, 0x0, 16)]) (base:=roots minor5xfffefc80Atlas) (G:=target minor5xfffefc80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfffefc80Lower minor5xfffefc80Slices)
  · exact sliceSigned (ms:=[swapRows 48, swapRows 65, swapRows 33, (0xffffffff, 0x0, 32)]) (base:=roots minor5xfff8eca0Atlas) (G:=target minor5xfff8eca0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfff8eca0Lower minor5xfff8eca0Slices)
  · exact sliceDual (ms:=[swapRows 80, swapRows 66, swapRows 48, (0xffffffff, 0xffffffff00000000, 32), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor5xfff8cc80Atlas) (G:=target minor5xfff8cc80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfff8cc80Lower minor5xfff8cc80Slices)
  · exact sliceDual (ms:=[swapRows 48, swapRows 32, swapRows 66, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x3333333333333333, 0xcccccccccccccccc, 2), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xffffffff00000000, 32)]) (base:=roots minor5xfff8cc80Atlas) (G:=target minor5xfff8cc80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfff8cc80Lower minor5xfff8cc80Slices)
  · exact sliceDual (ms:=[swapRows 64, swapRows 81, swapRows 50, swapRows 33, swapRows 32, (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xffffffff, 0xffffffff00000000, 32), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xaaaaaaaaaaaaaaaa, 1)]) (base:=roots minor5xfffcfa00Atlas) (G:=target minor5xfffcfa00Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfffcfa00Lower minor5xfffcfa00Slices)
  · exact sliceDual (ms:=[swapRows 49, swapRows 82, swapRows 66, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xffffffff, 0xffffffff00000000, 32), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor5xfffcfa00Atlas) (G:=target minor5xfffcfa00Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor5xfffcfa00Lower minor5xfffcfa00Slices)
  · exact sliceDual (ms:=[swapRows 49, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xff000000ff, 0xff000000ff000000, 16), (0x55555555, 0xaaaaaaaa00000000, 32)]) (base:=roots minor4xfe60Atlas) (G:=target minor4xfe60Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe60Lower minor4xfe60Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, swapRows 80, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x5555555555555555, 0x0, 1), (0xff000000ff, 0xff000000ff000000, 16)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, swapRows 81, (0x1111111111111111, 0x8888888888888888, 2), (0xf0f00000f0f, 0xf0f00000f0f00000, 16)]) (base:=roots minor4xfe64Atlas) (G:=target minor4xfe64Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe64Lower minor4xfe64Slices)
  · exact sliceSigned (ms:=[swapRows 50, (0x333300003333, 0xcccc0000cccc0000, 16), (0x55555555, 0xaaaaaaaa00000000, 32)]) (base:=roots minor4xfe60Atlas) (G:=target minor4xfe60Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe60Lower minor4xfe60Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 82, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x505050505050505, 0xa0a0a0a0a0a0a0a0, 4), (0x333300003333, 0xcccc0000cccc0000, 16)]) (base:=roots minor4xfe64Atlas) (G:=target minor4xfe64Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe64Lower minor4xfe64Slices)
  · exact sliceDual (ms:=[swapRows 33, swapRows 49, swapRows 65, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x0, 0xcccccccccccccccc, 2), (0xff00ff00, 0xff00ff00000000, 32)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[(0xffff0000ffff, 0x0, 16), (0x55555555, 0xaaaaaaaa00000000, 32)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 64, swapRows 83, (0x5555555555555555, 0x0, 1), (0xcc00cc00cc00cc, 0x3300330033003300, 8)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, swapRows 64, (0x5555555555555555, 0x0, 1), (0xff00ff00, 0xff00ff00000000, 32)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceSigned (ms:=[(0xffff0000ffff, 0x0, 16), (0xcccccccc, 0x3333333300000000, 32)]) (base:=roots minor4xfee8Atlas) (G:=target minor4xfee8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee8Lower minor4xfee8Slices)
  · exact sliceDual (ms:=[swapRows 64, swapRows 16, swapRows 33, (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0xffff, 0xffff000000000000, 32)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 64, swapRows 50, swapRows 32, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4), (0xffff, 0xffff000000000000, 32)]) (base:=roots minor4xfe90Atlas) (G:=target minor4xfe90Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe90Lower minor4xfe90Slices)
  · exact sliceDual (ms:=[swapRows 48, swapRows 16, swapRows 33, swapRows 82, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffffffff, 0xffffffff00000000, 32), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0xff000000ff, 0xff000000ff000000, 16)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceDual (ms:=[swapRows 16, swapRows 50, swapRows 82, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xffffffff, 0xffffffff00000000, 32), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0x333300003333, 0xcccc0000cccc0000, 16)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceDual (ms:=[swapRows 65, swapRows 33, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0x55555555, 0xaaaaaaaa00000000, 32)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceDual (ms:=[swapRows 65, swapRows 33, swapRows 83, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffffffff, 0xffffffff00000000, 32), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0x55005500550055, 0xaa00aa00aa00aa00, 8)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceDual (ms:=[swapRows 65, swapRows 50, swapRows 82, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xffffffff, 0xffffffff00000000, 32), (0x1111111111111111, 0x8888888888888888, 2), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 82, swapRows 64, (0x5555555555555555, 0x0, 1), (0x0, 0xf0f0f0f0f0f0f0f0, 4)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 82, (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0xffff0000ffff, 0x0, 16)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)
  · exact sliceSigned (ms:=[swapRows 82, swapRows 67, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4), (0x55005500550055, 0xaa00aa00aa00aa00, 8)]) (base:=roots minor4xfe90Atlas) (G:=target minor4xfe90Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe90Lower minor4xfe90Slices)
  · exact sliceSigned (ms:=[swapRows 82, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4), (0xff000000ff00, 0xff000000ff0000, 16)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)
  · exact sliceSigned (ms:=[swapRows 65, swapRows 83, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x1111111111111111, 0x8888888888888888, 2), (0xff00ff00ff00ff, 0x0, 8)]) (base:=roots minor4xfee4Atlas) (G:=target minor4xfee4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee4Lower minor4xfee4Slices)
  · exact sliceSigned (ms:=[swapRows 32, swapRows 49, swapRows 64, swapRows 16, (0x2222222222222222, 0x4444444444444444, 2), (0xffffffff, 0x0, 32)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 81, (0x3300330033003300, 0xcc00cc00cc00cc, 2), (0xff000000ff00, 0xff000000ff0000, 16)]) (base:=roots minor4xfe80Atlas) (G:=target minor4xfe80Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfe80Lower minor4xfe80Slices)
  · exact sliceDual (ms:=[swapRows 65, swapRows 33, swapRows 50, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xff00ff00ff00ff00, 8), (0x0, 0xffffffff00000000, 32)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceDual (ms:=[swapRows 33, swapRows 49, swapRows 65, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x0, 0xcccccccccccccccc, 2), (0x0, 0xffffffff00000000, 32)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceDual (ms:=[swapRows 48, swapRows 33, swapRows 65, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x2222222222222222, 0x4444444444444444, 2), (0x0, 0xffffffff00000000, 32)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 48, swapRows 64, (0x5555555555555555, 0x0, 1), (0x0, 0xffffffff00000000, 32)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 64, swapRows 49, swapRows 33, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0xffff, 0xffff000000000000, 32)]) (base:=roots minor4xfed0Atlas) (G:=target minor4xfed0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfed0Lower minor4xfed0Slices)
  · exact sliceDual (ms:=[swapRows 81, swapRows 33, swapRows 50, (0xffffffff, 0xffffffff00000000, 32), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x55005500550055, 0xaa00aa00aa00aa00, 8), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor4xfed0Atlas) (G:=target minor4xfed0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfed0Lower minor4xfed0Slices)
  · exact sliceDual (ms:=[swapRows 48, swapRows 82, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffffffff, 0xffffffff00000000, 32), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xa0a0a0a0a0a0a0a, 0x5050505050505050, 4), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 48, swapRows 82, swapRows 32, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffffffff, 0xffffffff00000000, 32), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x5555555555555555, 0x0, 1), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 33, swapRows 81, swapRows 49, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xffffffff, 0xffffffff00000000, 32), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0x0, 8), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 32, swapRows 65, swapRows 80, swapRows 48, (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xffffffff, 0xffffffff00000000, 32), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x0, 0xcccccccccccccccc, 2), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 80, swapRows 48, (0x0, 0xff00ff00ff00ff00, 8), (0xffff0000ffff, 0x0, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 65, swapRows 33, swapRows 83, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xffffffff, 0xffffffff00000000, 32), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0xcc00cc00cc00cc, 0x3300330033003300, 8)]) (base:=roots minor4xfee0Atlas) (G:=target minor4xfee0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfee0Lower minor4xfee0Slices)
  · exact sliceSigned (ms:=[swapRows 48, swapRows 33, swapRows 81, swapRows 64, (0x5555555555555555, 0x0, 1), (0x0, 0xcccccccccccccccc, 2)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 82, swapRows 32, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x5555555555555555, 0x0, 1), (0x333300003333, 0xcccc0000cccc0000, 16)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceDual (ms:=[swapRows 80, swapRows 16, swapRows 67, (0xffffffff, 0xffffffff00000000, 32), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x0, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0x0, 8)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 48, swapRows 33, swapRows 65, (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xffff0000ffff, 0xffff0000ffff0000, 16), (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x0, 0xcccccccccccccccc, 2), (0xffffffff, 0x0, 32)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 66, swapRows 83, (0x303030303030303, 0xc0c0c0c0c0c0c0c0, 4), (0xff00ff00ff00ff, 0x0, 8)]) (base:=roots minor4xfed0Atlas) (G:=target minor4xfed0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfed0Lower minor4xfed0Slices)
  · exact sliceDual (ms:=[swapRows 64, swapRows 33, swapRows 49, (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x3333333333333333, 0xcccccccccccccccc, 2), (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0xcccccccc, 0x3333333300000000, 32)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 80, swapRows 50, (0xffffffff, 0xffffffff00000000, 32), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0xf0f00000f0f0, 0xf0f00000f0f0000, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 80, swapRows 50, (0xffffffff, 0xffffffff00000000, 32), (0x3333333333333333, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0x0, 16)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceDual (ms:=[swapRows 64, swapRows 33, swapRows 49, (0xffff0000ffff, 0xffff0000ffff0000, 16), (0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0, 4), (0xff00ff00ff00ff, 0xff00ff00ff00ff00, 8), (0x3333333333333333, 0xcccccccccccccccc, 2), (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0xffffffff, 0x0, 32)]) (base:=roots minor4xfec0Atlas) (G:=target minor4xfec0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xfec0Lower minor4xfec0Slices)
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 80, swapRows 67, (0x5555555555555555, 0x0, 1), (0xff00ff00ff00ff, 0x0, 8)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 49, swapRows 66, (0xf0f0f0f0f0f0f0f, 0x0, 4), (0xff00ff00, 0xff00ff00000000, 32)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, swapRows 49, (0xff00ff00ff00ff, 0x0, 8), (0xffffffff, 0x0, 32)]) (base:=roots minor4xffe8Atlas) (G:=target minor4xffe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (minor4xffe8Lower minor4xffe8Slices)
  · exact sliceSigned (ms:=[swapRows 33, swapRows 49, (0x0, 0xcccccccccccccccc, 2), (0xffff0000ffff, 0x0, 16), (0x0, 0xffffffff00000000, 32)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 80, (0x5555555555555555, 0x0, 1), (0xf000f000f000f, 0xf000f000f000f000, 8), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 33, swapRows 81, (0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 1), (0x1111111111111111, 0x8888888888888888, 2), (0xff00ff00ff00ff, 0x0, 8), (0x0, 0xffff0000ffff0000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 32, swapRows 65, swapRows 80, (0x5555555555555555, 0x0, 1), (0x0, 0xcccccccccccccccc, 2), (0x0, 0xff00ff00ff00ff00, 8)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 49, swapRows 82, (0x1111111111111111, 0x8888888888888888, 2), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0xaaaa0000aaaa, 0x5555000055550000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 48, swapRows 82, (0x3333333333333333, 0xcccccccccccccccc, 2), (0x5555555555555555, 0x0, 1), (0x0, 0xf0f0f0f0f0f0f0f0, 4), (0x333300003333, 0xcccc0000cccc0000, 16)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 49, swapRows 66, (0x0, 0xcccccccccccccccc, 2), (0xf0f0f0f0f0f0f0f, 0x0, 4), (0xff00ff00, 0xff00ff00000000, 32)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 33, swapRows 65, (0x0, 0xcccccccccccccccc, 2), (0xff00ff00ff00ff, 0x0, 8), (0xffffffff, 0x0, 32)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower
  · exact sliceSigned (ms:=[swapRows 16, swapRows 32, swapRows 48, (0x0, 0xaaaaaaaaaaaaaaaa, 1), (0xffff0000ffff, 0x0, 16), (0xffffffff, 0x0, 32)]) (base:=roots minor3xe8Atlas) (G:=target minor3xe8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) minor3xe8Lower


def fullRoots : List Sig := roots mainAtlas
def fullWord : Sig := target mainAtlas
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808928 * 2 ^ 32 + 4209557696) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def sample7 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_43508.Model.Repr at out
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

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [8, 7]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [10, 1]⟩, ⟨.and, [4, 0]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [13, 5]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [15, 11]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem witness_shape : MetaComplexity.Monotone2 witness := by
  simp [MetaComplexity.Monotone2, witness]

theorem witness_eval : ∀ x, witness.eval (List.ofFn x) = posted x := by decide +kernel

end PEqualNP.Outside.L_meta_43508

open PEqualNP.Outside.L_meta_43508 PEqualNP.Outside.L_meta_43508.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_43508 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209557696) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4209557696) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsize, heval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have cut : C.gates.countP (fun g => !isNot g) < C.gates.length := by
      rw [List.countP_eq_length_filter]
      exact (List.length_filter_lt_length_iff_exists (p := fun g => !isNot g)).mpr
        ⟨g, mem, by simp [isNot, op]⟩
    have hb := binaryLower (mainLower mainSlices) C.gates C.output hfan heval
    have hsz : C.size = C.gates.length := rfl
    have hw : witness.size = 12 := rfl
    exact ⟨witness, witness_shape, by omega, witness_eval⟩
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

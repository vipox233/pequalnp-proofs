import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46966.Model
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

end PEqualNP.Outside.L_meta_46966.Model
namespace PEqualNP.Outside.L_meta_46966
open PEqualNP.Outside.L_meta_46966.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Prior52376B0
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
end Prior52376B0

namespace Prior52376B4
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) Prior52376B0.low
end Prior52376B4

namespace Prior52376B6
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) Prior52376B0.low
end Prior52376B6

namespace Prior52376B7
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) Prior52376B0.low
end Prior52376B7

namespace Prior52376B10
def R : List Sig := vars 11
def T : Sig := 0x8800880088008800
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 10, 11), (0xcccccccccccccccc, 9, 11), (0xff00ff00ff00ff00, 3, 11)] (by decide +kernel)
end Prior52376B10

namespace Prior52376B11
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
    (by decide +kernel) (proper_of _ (by decide)) Prior52376B6.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior52376B7.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 0 w0 w1
def w5 := combineObserved 0 w0 w2
def w6 := combineObserved 0 w1 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w4, w5, w6, w3]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior52376B0.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 2 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior52376B10.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 4 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior52376B4.low
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
end Prior52376B11

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
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B1

namespace B2
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B2

namespace B3
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B3

namespace B4
def R : List Sig := vars 11
def T : Sig := 0xffeeffeeffeeffee
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
end B4

namespace B5
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
    (by decide +kernel) (proper_of _ (by decide)) B2.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 1 w2 w1
def w5 := combineObserved 1 w3 w1
def w6 := combineObserved 1 w3 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w4, w5, w6]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B3.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def w7 := combineObserved 1 w3 w0
def a0 : List Move := [swapRows 32]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v0 a0 a0ok
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w7, w5]
  (fun h => chooseRoute #[(usePool p2), (usePool p1)] #[r0] ((((0x408 : Nat) >>> ((h % 6) * 2)) &&& 3))) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p3 : Pool R T := prefixPool s3 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xfefefefefefefefe, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 2 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
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
end B5

namespace B10
def R : List Sig := vars 15
def T : Sig := 0xa880a880a880a880
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 1) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 6, 7)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B3.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 6, 7)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B10

namespace B13
def R : List Sig := vars 15
def T : Sig := 0xeaa8eaa8eaa8eaa8
def P : Nat → Bits
  | 0 => ((0xf7f7fffe3fffffc7 : BitVec 64) ++ (0xf7f7fffe3fffffc7 : BitVec 64))
  | 1 => ((0xb9f8e73fc7743579 : BitVec 64) ++ (0xb9f8e73fc7743579 : BitVec 64))
  | 2 => ((0xdaff07cff878c9ba : BitVec 64) ++ (0xdaff07cff878c9ba : BitVec 64))
  | 3 => ((0xecfff80fff830e3c : BitVec 64) ++ (0xecfff80fff830e3c : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x810000009100007 : BitVec 64) ++ (0x810000009100007 : BitVec 64))
  | 1 => ((0x46264a4642217558 : BitVec 64) ++ (0x46264a4642217558 : BitVec 64))
  | 2 => ((0x2542d41a9042d9a8 : BitVec 64) ++ (0x2542d41a9042d9a8 : BitVec 64))
  | 3 => ((0x138486ad2403ae30 : BitVec 64) ++ (0x138486ad2403ae30 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
def w4 := combineObserved 0 w0 w1
def w5 := combineObserved 1 w4 w3
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2, w5]
  (fun _ => ([], [])) (by decide +kernel)
def w6 := combineObserved 0 w0 w3
def w7 := combineObserved 3 w6 w1
def v1 : Closed T 3 := closeState (raw := R) properPN 3 [w7, w0, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w8 := combineObserved 1 w0 w2
def w9 := combineObserved 0 w8 w1
def v2 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w9, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w10 := combineObserved 1 w0 w1
def w11 := combineObserved 2 w10 w3
def v3 : Closed T 3 := closeState (raw := R) properPN 3 [w11, w0, w1, w2]
  (fun _ => ([], [])) (by decide +kernel)
def w12 := combineObserved 0 w1 w2
def w13 := combineObserved 1 w1 w2
def v4 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w12, w13, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w14 := combineObserved 2 w1 w2
def w15 := combineObserved 1 w14 w3
def v5 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2, w15]
  (fun _ => ([], [])) (by decide +kernel)
def w16 := combineObserved 2 w3 w2
def w17 := combineObserved 3 w16 w1
def v6 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w17, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def a0 : List Move := [swapRows 49]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v1 a0 a0ok
def a1 : List Move := [swapRows 50, swapRows 33]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 3 := rotateClosed v1 a1 a1ok
def a2 : List Move := [swapRows 50]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r2 : Closed T 3 := rotateClosed v0 a2 a2ok
def v7 : Closed T 4 := closeState (raw := R) properPN 4 [w4, w0, w1, w2, w3]
  (fun h => chooseRoute #[] #[r0, r1, v0, r2] ((((0xd08 : Nat) >>> ((h % 13) * 2)) &&& 3))) (by decide +kernel)
def r3 : Closed T 3 := rotateClosed v3 a2 a2ok
def a3 : List Move := [swapRows 33]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 3 := rotateClosed v2 a3 a3ok
def a4 : List Move := [swapRows 50, swapRows 49]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 3 := rotateClosed v2 a4 a4ok
def v8 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w10, w2, w3]
  (fun h => chooseRoute #[] #[v3, r3, r4, r5] ((((0x20043 : Nat) >>> ((h % 10) * 2)) &&& 3))) (by decide +kernel)
def w18 := combineObserved 2 w0 w3
def v9 : Closed T 4 := closeState (raw := R) properPN 4 [w18, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def w19 := combineObserved 3 w0 w1
def v10 : Closed T 4 := closeState (raw := R) properPN 4 [w19, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def v11 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w12, w1, w2, w3]
  (fun _ => ([], [v4])) (by decide +kernel)
def v12 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w13, w3]
  (fun _ => ([], [v4])) (by decide +kernel)
def w20 := combineObserved 2 w1 w3
def r6 : Closed T 3 := rotateClosed v6 a1 a1ok
def r7 : Closed T 3 := rotateClosed v5 a2 a2ok
def v13 : Closed T 4 := closeState (raw := R) properPN 4 [w20, w0, w1, w2, w3]
  (fun _ => ([], [r6, r7])) (by decide +kernel)
def r8 : Closed T 4 := rotateClosed v9 a0 a0ok
def r9 : Closed T 4 := rotateClosed v9 a2 a2ok
def r10 : Closed T 4 := rotateClosed v13 a3 a3ok
def r11 : Closed T 4 := rotateClosed v13 a0 a0ok
def r12 : Closed T 4 := rotateClosed v13 a2 a2ok
def r13 : Closed T 4 := rotateClosed v13 a1 a1ok
def r14 : Closed T 4 := rotateClosed v13 a4 a4ok
def r15 : Closed T 4 := rotateClosed v10 a3 a3ok
def r16 : Closed T 4 := rotateClosed v10 a0 a0ok
def r17 : Closed T 4 := rotateClosed v7 a3 a3ok
def r18 : Closed T 4 := rotateClosed v7 a0 a0ok
def r19 : Closed T 4 := rotateClosed v11 a0 a0ok
def r20 : Closed T 4 := rotateClosed v11 a2 a2ok
def r21 : Closed T 4 := rotateClosed v8 a3 a3ok
def r22 : Closed T 4 := rotateClosed v8 a0 a0ok
def r23 : Closed T 4 := rotateClosed v12 a0 a0ok
def r24 : Closed T 4 := rotateClosed v12 a2 a2ok
def v14 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[] #[v9, r8, r9, v13, r10, r11, r12, r13, r14, v10, r15, r16, v7, r17, r18, v11, r19, r20, v8, r21, r22, v12, r23, r24] ((((((((0x8 : Nat) <<< 64) ||| 0xe80500c55ab70460) <<< 64) ||| 0x96966e0c96f19006) >>> (((h / 8 + (((0x2300d101 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 27) * 5)) &&& 31))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v14 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B13

namespace B24
def R : List Sig := vars 15
def T : Sig := 0xe888e888e888e888
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 5, 13)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 5, 13)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B24

namespace B27
def R : List Sig := vars 15
def T : Sig := 0xeee8eee8eee8eee8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B27

namespace B38
def R : List Sig := vars 15
def T : Sig := 0xfeeafeeafeeafeea
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B3.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B38

namespace B42
def R : List Sig := vars 31
def T : Sig := 0xfeeefeeafeeefeea
theorem low : Lower true R T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 17 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 2, 18)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B3.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1), (0xffff0000ffff0000, 2, 18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide
  rw [he] at h
  exact h
end B42

namespace B49
def R : List Sig := vars 31
def T : Sig := 0xfefefee8fefefee8
theorem low : Lower true R T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 16 0) (raw := R)
    (T := T) (xs := [(0xffff0000ffff0000, 1, 17)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B5.low
  have he : (([(0xffff0000ffff0000, 1, 17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B49

namespace B51
def R : List Sig := vars 63
def T : Sig := 0xfeeefeeafeeae8a0
theorem s0 : Slice true R T 0xff00ff00ff00ff00 8 :=
  slice_correct (ms := [swapRows 83, swapRows 84] ++ fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B49.low
theorem s1 : Slice true R T 0xffff0000ffff0000 6 :=
  slice_correct (ms := [swapRows 84] ++ fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B42.low
theorem s2 : Slice true R T 0xffffffff00000000 6 :=
  slice_correct (ms := fixRows 0 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B42.low
theorem s3 : Slice true R T 0x4444444444444444 7 :=
  slice_correct (ms := [swapRows 64, swapRows 81, swapRows 66, swapRows 83] ++ fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s4 : Slice true R T 0x505050505050505 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 5 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
theorem s5 : Slice true R T 0x5050505050505050 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s6 : Slice true R T 0x55005500550055 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 9 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
theorem s7 : Slice true R T 0x5500550055005500 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s8 : Slice true R T 0x555500005555 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 17 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior52376B11.low
theorem s9 : Slice true R T 0x55555555 7 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 67] ++ fixRows 33 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) Prior52376B11.low
theorem s10 : Slice true R T 0xc0c0c0c0c0c0c0c 7 :=
  slice_correct (ms := [swapRows 65, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 4 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s11 : Slice true R T 0x3300330033003300 5 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 83] ++ fixRows 2 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s12 : Slice true R T 0xcc00cc00cc00cc 7 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 83] ++ fixRows 8 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s13 : Slice true R T 0xcccc0000cccc 7 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67, swapRows 84] ++ fixRows 16 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s14 : Slice true R T 0xcccccccc 7 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67] ++ fixRows 32 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s15 : Slice true R T 0xf000f000f000f00 5 :=
  slice_correct (ms := [swapRows 66, swapRows 83] ++ fixRows 4 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s16 : Slice true R T 0xf0f00000f0f 5 :=
  slice_correct (ms := [swapRows 33, swapRows 66, swapRows 84] ++ fixRows 20 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s17 : Slice true R T 0xf0f00000f0f0 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67, swapRows 84] ++ fixRows 16 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s18 : Slice true R T 0xf0f0f0f 5 :=
  slice_correct (ms := [swapRows 33, swapRows 66] ++ fixRows 36 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s19 : Slice true R T 0xf0f0f0f0 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67] ++ fixRows 32 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s20 : Slice true R T 0xff000000ff00 7 :=
  slice_correct (ms := [swapRows 67, swapRows 84] ++ fixRows 16 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s21 : Slice true R T 0xff00ff00 7 :=
  slice_correct (ms := [swapRows 67] ++ fixRows 32 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s22 : Slice true R T 0xffff 5 :=
  slice_correct (ms := [swapRows 33] ++ fixRows 48 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s23 : Slice true R T 0xffff00000000 5 :=
  slice_correct (ms := fixRows 16 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s24 : Slice true R T 0xffff0000 5 :=
  slice_correct (ms := fixRows 32 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s26 : Slice true R T 0x404040404040404 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 82] ++ fixRows 5 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s40 : Slice true R T 0x44444444 4 :=
  slice_correct (ms := [swapRows 48, swapRows 65, swapRows 50, swapRows 67] ++ fixRows 33 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s50 : Slice true R T 0x505000005050 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66, swapRows 84] ++ fixRows 17 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s54 : Slice true R T 0x50505050 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66] ++ fixRows 33 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s58 : Slice true R T 0x550000005500 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 17 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s62 : Slice true R T 0x55005500 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67] ++ fixRows 33 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s65 : Slice true R T 0x555500000000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50] ++ fixRows 17 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s66 : Slice true R T 0x55550000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50] ++ fixRows 33 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s72 : Slice true R T 0xc000c000c000c 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66, swapRows 83, swapRows 84] ++ fixRows 12 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s76 : Slice true R T 0xc0c00000c0c 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66, swapRows 84] ++ fixRows 20 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s80 : Slice true R T 0xc0c0c0c 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66] ++ fixRows 36 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s84 : Slice true R T 0x330000003300 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 18 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s89 : Slice true R T 0x33003300 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67] ++ fixRows 34 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s90 : Slice true R T 0xcc00cc 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67] ++ fixRows 40 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s96 : Slice true R T 0xcccc 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50] ++ fixRows 48 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s100 : Slice true R T 0xf0000000f00 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67, swapRows 84] ++ fixRows 20 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s104 : Slice true R T 0xf000f00 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67] ++ fixRows 36 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s116 : Slice true R T 0xff00 4 :=
  slice_correct (ms := fixRows 48 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s120 : Slice true R T 0x999900009999 6 :=
  slice_correct (ms := [swapRows 80, swapRows 81, swapRows 82, swapRows 83] ++ fixRows 16 0 ++ [(0x4444444444444444, 0x2222222222222222, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s121 : Slice true R T 0x99999999 6 :=
  slice_correct (ms := [swapRows 80, swapRows 81, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 32 0 ++ [(0x4444444444444444, 0x2222222222222222, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s124 : Slice true R T 0xa050a050a050a05 6 :=
  slice_correct (ms := [swapRows 80, swapRows 66, swapRows 83] ++ fixRows 4 0 ++ [(0x5500550055005500, 0xaa00aa00aa00aa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s125 : Slice true R T 0xaa550000aa55 6 :=
  slice_correct (ms := [swapRows 80, swapRows 83] ++ fixRows 16 0 ++ [(0x5500550055005500, 0xaa00aa00aa00aa, 1)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s135 : Slice true R T 0xc300c300c300c3 5 :=
  slice_correct (ms := [swapRows 81, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 8 0 ++ [(0x3030303030303030, 0xc0c0c0c0c0c0c0c, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
theorem s139 : Slice true R T 0x4444111144441111 6 :=
  slice_correct (ms := [swapRows 64, swapRows 81, swapRows 82, swapRows 83] ++ fixRows 1 0 ++ [(0x3333000033330000, 0xcccc0000cccc, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s142 : Slice true R T 0x4444444411111111 6 :=
  slice_correct (ms := [swapRows 64, swapRows 81, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 1 0 ++ [(0x3333333300000000, 0xcccccccc, 2)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s145 : Slice true R T 0x5005500550055005 6 :=
  slice_correct (ms := [swapRows 64, swapRows 82, swapRows 67, swapRows 84] ++ fixRows 1 0 ++ [(0xf000f000f000f00, 0xf000f000f000f0, 4)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s152 : Slice true R T 0xf0f00f0f 6 :=
  slice_correct (ms := [swapRows 16, swapRows 33, swapRows 82, swapRows 84] ++ fixRows 32 0 ++ [(0xf0f00000f0f0000, 0xf0f00000f0f0, 4)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s158 : Slice true R T 0xf0f000000f0f 6 :=
  slice_correct (ms := [swapRows 16, swapRows 33, swapRows 82] ++ fixRows 16 0 ++ [(0xf0f0f0f00000000, 0xf0f0f0f0, 4)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
theorem s162 : Slice true R T 0xff0000ff00000000 5 :=
  slice_correct (ms := [swapRows 83, swapRows 84] ++ fixRows 0 32 ++ [(0xff000000ff0000, 0xff000000ff00, 8)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
theorem s170 : Slice true R T 0xff0000000000ff00 7 :=
  slice_correct (ms := [swapRows 67, swapRows 84] ++ fixRows 0 8 ++ [(0xffff00000000, 0xffff0000, 16)]) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
def Pos : Nat → Bits
  | 0 => ((0xbb33729792d08d89 : BitVec 64) ++ (0xbb33729792d08d89 : BitVec 64))
  | 1 => ((0xd0f895656a6bb366 : BitVec 64) ++ (0xd0f895656a6bb366 : BitVec 64))
  | 2 => ((0x25ce596c25ac64bb : BitVec 64) ++ (0x25ce596c25ac64bb : BitVec 64))
  | 3 => ((0xca78a5b4d167396 : BitVec 64) ++ (0xca78a5b4d167396 : BitVec 64))
  | 4 => ((0xfc89ad12d5e79071 : BitVec 64) ++ (0xfc89ad12d5e79071 : BitVec 64))
  | 5 => ((0xc6552fa82b995e44 : BitVec 64) ++ (0xc6552fa82b995e44 : BitVec 64))
  | _ => 0
def Neg : Nat → Bits
  | 0 => ((0x30101180500888 : BitVec 64) ++ (0x30101180500888 : BitVec 64))
  | 1 => ((0x813814644a4b8322 : BitVec 64) ++ (0x813814644a4b8322 : BitVec 64))
  | 2 => ((0x234e416421a46411 : BitVec 64) ++ (0x234e416421a46411 : BitVec 64))
  | 3 => ((0x8878a1b44143386 : BitVec 64) ++ (0x8878a1b44143386 : BitVec 64))
  | 4 => ((0x74c1a90215a39071 : BitVec 64) ++ (0x74c1a90215a39071 : BitVec 64))
  | 5 => ((0xa6412f882b885444 : BitVec 64) ++ (0xa6412f882b885444 : BitVec 64))
  | _ => 0
theorem correctPairs : properPairs T (asRow Pos) (asRow Neg) := by unfold properPairs; decide +kernel
def auto1 : List Move := [swapRows 84]
theorem auto1ok : autoOK T auto1 = true := by decide +kernel
def w0 := inputObserved 63 Pos Neg 0
def w1 := inputObserved 63 Pos Neg 1
def w2 := inputObserved 63 Pos Neg 2
def w3 := inputObserved 63 Pos Neg 3
def w4 := inputObserved 63 Pos Neg 4
def w5 := inputObserved 63 Pos Neg 5
def w6 := combineObserved 0 w0 w1
def w7 := combineObserved 1 w6 w2
def w8 := combineObserved 1 w2 w3
def w9 := combineObserved 3 w6 w8
def w10 := combineObserved 1 w0 w1
def w11 := combineObserved 2 w0 w1
def w12 := combineObserved 1 w11 w3
def w13 := combineObserved 3 w11 w3
def w14 := combineObserved 3 w0 w1
def w15 := combineObserved 2 w14 w2
def w16 := combineObserved 3 w15 w1
def w17 := combineObserved 1 w15 w4
def w18 := combineObserved 2 w15 w5
def w19 := combineObserved 1 w4 w5
def w20 := combineObserved 2 w14 w5
def w21 := combineObserved 1 w20 w2
def w22 := combineObserved 1 w20 w4
def w23 := combineObserved 2 w20 w4
def w24 := combineObserved 1 w2 w4
def w25 := combineObserved 2 w1 w2
def w26 := combineObserved 2 w25 w5
def w27 := combineObserved 0 w1 w3
def w28 := combineObserved 1 w27 w2
def w29 := combineObserved 1 w27 w4
def w30 := combineObserved 1 w2 w5
def w31 := combineObserved 1 w24 w5
def w32 := combineObserved 3 w0 w31
def w33 := combineObserved 2 w24 w5
def w34 := combineObserved 3 w2 w19
def w35 := combineObserved 1 w34 w27
def w36 := combineObserved 2 w1 w5
def w37 := combineObserved 2 w36 w4
def w38 := combineObserved 0 w14 w8
def w39 := combineObserved 0 w14 w24
def w40 := combineObserved 0 w14 w3
def w41 := combineObserved 1 w3 w4
def w42 := combineObserved 0 w14 w41
def w43 := combineObserved 3 w2 w41
def w44 := combineObserved 0 w14 w19
def w45 := combineObserved 0 w0 w2
def w46 := combineObserved 1 w45 w1
def w47 := combineObserved 3 w45 w1
def w48 := combineObserved 1 w45 w3
def w49 := combineObserved 3 w45 w3
def w50 := combineObserved 1 w45 w5
def w51 := combineObserved 3 w45 w4
def w52 := combineObserved 1 w0 w3
def w53 := combineObserved 3 w2 w52
def w54 := combineObserved 1 w0 w2
def w55 := combineObserved 3 w0 w3
def w56 := combineObserved 1 w55 w2
def w57 := combineObserved 1 w16 w4
def w58 := combineObserved 2 w16 w5
def w59 := combineObserved 1 w54 w4
def w60 := combineObserved 3 w16 w41
def w61 := combineObserved 3 w16 w19
def w62 := combineObserved 0 w1 w19
def w63 := combineObserved 1 w0 w62
def w64 := combineObserved 1 w0 w27
def w65 := combineObserved 1 w64 w5
def w66 := combineObserved 1 w64 w4
def w67 := combineObserved 3 w2 w66
def w68 := combineObserved 0 w1 w59
def w69 := combineObserved 1 w54 w5
def w70 := combineObserved 1 w59 w5
def w71 := combineObserved 2 w59 w5
def w72 := combineObserved 2 w54 w5
def w73 := combineObserved 1 w72 w4
def w74 := combineObserved 1 w27 w54
def w75 := combineObserved 3 w27 w54
def w76 := combineObserved 3 w27 w24
def w77 := combineObserved 3 w27 w19
def w78 := combineObserved 3 w27 w31
def w79 := combineObserved 3 w27 w59
def w80 := combineObserved 3 w27 w70
def w81 := combineObserved 1 w1 w3
def w82 := combineObserved 2 w1 w3
def w83 := combineObserved 2 w54 w4
def w84 := combineObserved 3 w0 w8
def w85 := combineObserved 3 w2 w3
def w86 := combineObserved 1 w85 w0
def w87 := combineObserved 3 w0 w24
def w88 := combineObserved 0 w1 w24
def w89 := combineObserved 0 w54 w3
def w90 := combineObserved 0 w3 w24
def w91 := combineObserved 2 w3 w5
def w92 := combineObserved 0 w54 w19
def w93 := combineObserved 3 w0 w30
def w94 := combineObserved 2 w2 w5
def w95 := combineObserved 1 w94 w4
def w96 := combineObserved 2 w3 w4
def w97 := combineObserved 1 w89 w4
def w98 := combineObserved 1 w54 w3
def w99 := combineObserved 3 w89 w19
def w100 := combineObserved 0 w1 w98
def w101 := combineObserved 2 w54 w3
def w102 := combineObserved 3 w54 w3
def w103 := combineObserved 0 w3 w59
def w104 := combineObserved 3 w83 w1
def w105 := combineObserved 2 w72 w4
def w106 := combineObserved 0 w1 w41
def w107 := combineObserved 1 w0 w106
def w108 := combineObserved 2 w107 w2
def w109 := combineObserved 1 w106 w2
def w110 := combineObserved 1 w106 w54
def w111 := combineObserved 2 w110 w5
def w112 := combineObserved 1 w3 w5
def w113 := combineObserved 0 w1 w112
def w114 := combineObserved 3 w113 w54
def w115 := combineObserved 0 w54 w41
def w116 := combineObserved 3 w54 w41
def w117 := combineObserved 2 w63 w2
def w118 := combineObserved 1 w62 w2
def w119 := combineObserved 1 w62 w54
def w120 := combineObserved 3 w62 w54
def w121 := combineObserved 3 w54 w19
def w122 := combineObserved 0 w3 w19
def w123 := combineObserved 1 w0 w122
def w124 := combineObserved 2 w54 w122
def w125 := combineObserved 2 w0 w2
def w126 := combineObserved 3 w0 w2
def w127 := combineObserved 1 w126 w4
def w128 := combineObserved 1 w126 w5
def w129 := combineObserved 1 w127 w5
def w130 := combineObserved 2 w127 w5
def w131 := combineObserved 3 w126 w41
def w132 := combineObserved 3 w126 w19
def w133 := combineObserved 0 w0 w3
def w134 := combineObserved 1 w133 w2
def w135 := combineObserved 3 w133 w52
def w136 := combineObserved 0 w1 w2
def w137 := combineObserved 1 w0 w136
def w138 := combineObserved 3 w136 w52
def w139 := combineObserved 0 w25 w52
def w140 := combineObserved 0 w1 w52
def w141 := combineObserved 1 w140 w2
def w142 := combineObserved 3 w53 w1
def w143 := combineObserved 2 w0 w3
def w144 := combineObserved 1 w143 w1
def w145 := combineObserved 3 w143 w1
def w146 := combineObserved 1 w143 w2
def w147 := combineObserved 1 w56 w4
def w148 := combineObserved 2 w56 w5
def w149 := combineObserved 1 w55 w4
def w150 := combineObserved 3 w2 w149
def w151 := combineObserved 1 w55 w5
def w152 := combineObserved 1 w149 w5
def w153 := combineObserved 2 w149 w5
def w154 := combineObserved 3 w55 w24
def w155 := combineObserved 3 w55 w1
def w156 := combineObserved 1 w94 w55
def w157 := combineObserved 3 w55 w19
def w158 := combineObserved 0 w0 w4
def w159 := combineObserved 1 w158 w1
def w160 := combineObserved 0 w0 w5
def w161 := combineObserved 3 w160 w1
def w162 := combineObserved 1 w158 w2
def w163 := combineObserved 3 w160 w2
def w164 := combineObserved 1 w158 w3
def w165 := combineObserved 3 w160 w3
def w166 := combineObserved 1 w158 w5
def w167 := combineObserved 3 w160 w4
def w168 := combineObserved 1 w0 w4
def w169 := combineObserved 1 w137 w5
def w170 := combineObserved 1 w137 w4
def w171 := combineObserved 3 w5 w170
def w172 := combineObserved 1 w0 w5
def w173 := combineObserved 1 w168 w5
def w174 := combineObserved 0 w1 w173
def w175 := combineObserved 3 w2 w173
def w176 := combineObserved 1 w136 w5
def w177 := combineObserved 3 w136 w19
def w178 := combineObserved 3 w136 w173
def w179 := combineObserved 3 w136 w3
def w180 := combineObserved 2 w74 w5
def w181 := combineObserved 3 w5 w66
def w182 := combineObserved 1 w27 w5
def w183 := combineObserved 3 w27 w173
def w184 := combineObserved 1 w175 w27
def w185 := combineObserved 0 w2 w3
def w186 := combineObserved 1 w0 w185
def w187 := combineObserved 1 w186 w5
def w188 := combineObserved 1 w186 w4
def w189 := combineObserved 3 w5 w188
def w190 := combineObserved 1 w185 w5
def w191 := combineObserved 3 w185 w19
def w192 := combineObserved 3 w185 w173
def w193 := combineObserved 1 w85 w168
def w194 := combineObserved 3 w85 w173
def w195 := combineObserved 0 w2 w173
def w196 := combineObserved 1 w0 w88
def w197 := combineObserved 2 w196 w5
def w198 := combineObserved 3 w172 w24
def w199 := combineObserved 2 w2 w4
def w200 := combineObserved 1 w199 w5
def w201 := combineObserved 1 w94 w168
def w202 := combineObserved 3 w0 w19
def w203 := combineObserved 0 w2 w19
def w204 := combineObserved 3 w175 w1
def w205 := combineObserved 0 w3 w173
def w206 := combineObserved 2 w0 w5
def w207 := combineObserved 1 w206 w2
def w208 := combineObserved 3 w0 w5
def w209 := combineObserved 1 w206 w185
def w210 := combineObserved 1 w206 w85
def w211 := combineObserved 1 w208 w2
def w212 := combineObserved 1 w211 w4
def w213 := combineObserved 3 w0 w4
def w214 := combineObserved 1 w213 w2
def w215 := combineObserved 2 w214 w5
def w216 := combineObserved 1 w213 w5
def w217 := combineObserved 1 w208 w4
def w218 := combineObserved 3 w2 w217
def w219 := combineObserved 3 w208 w30
def w220 := combineObserved 3 w208 w24
def w221 := combineObserved 1 w94 w213
def w222 := combineObserved 1 w137 w3
def w223 := combineObserved 1 w170 w5
def w224 := combineObserved 2 w137 w5
def w225 := combineObserved 3 w137 w41
def w226 := combineObserved 3 w137 w19
def w227 := combineObserved 1 w136 w4
def w228 := combineObserved 3 w0 w227
def w229 := combineObserved 1 w227 w5
def w230 := combineObserved 2 w227 w5
def w231 := combineObserved 1 w1 w2
def w232 := combineObserved 3 w0 w41
def w233 := combineObserved 3 w136 w41
def w234 := combineObserved 1 w177 w0
def w235 := combineObserved 0 w231 w3
def w236 := combineObserved 2 w231 w3
def w237 := combineObserved 1 w26 w0
def w238 := combineObserved 0 w1 w30
def w239 := combineObserved 1 w26 w4
def w240 := combineObserved 2 w26 w4
def w241 := combineObserved 0 w25 w41
def w242 := combineObserved 0 w25 w19
def w243 := combineObserved 3 w1 w2
def w244 := combineObserved 1 w74 w4
def w245 := combineObserved 2 w244 w5
def w246 := combineObserved 2 w64 w2
def w247 := combineObserved 1 w66 w5
def w248 := combineObserved 3 w2 w247
def w249 := combineObserved 2 w64 w5
def w250 := combineObserved 3 w64 w24
def w251 := combineObserved 3 w64 w31
def w252 := combineObserved 1 w33 w0
def w253 := combineObserved 3 w64 w19
def w254 := combineObserved 1 w34 w0
def w255 := combineObserved 1 w34 w64
def w256 := combineObserved 3 w0 w28
def w257 := combineObserved 1 w28 w4
def w258 := combineObserved 2 w28 w5
def w259 := combineObserved 3 w0 w29
def w260 := combineObserved 3 w2 w29
def w261 := combineObserved 1 w29 w5
def w262 := combineObserved 2 w29 w5
def w263 := combineObserved 3 w27 w81
def w264 := combineObserved 1 w93 w4
def w265 := combineObserved 3 w27 w264
def w266 := combineObserved 1 w76 w0
def w267 := combineObserved 1 w77 w0
def w268 := combineObserved 1 w78 w0
def w269 := combineObserved 0 w1 w31
def w270 := combineObserved 1 w202 w2
def w271 := combineObserved 3 w27 w270
def w272 := combineObserved 3 w0 w35
def w273 := combineObserved 3 w1 w3
def w274 := combineObserved 0 w1 w4
def w275 := combineObserved 1 w274 w2
def w276 := combineObserved 0 w1 w5
def w277 := combineObserved 1 w276 w2
def w278 := combineObserved 1 w277 w4
def w279 := combineObserved 2 w275 w5
def w280 := combineObserved 1 w274 w5
def w281 := combineObserved 1 w276 w4
def w282 := combineObserved 3 w2 w281
def w283 := combineObserved 3 w276 w24
def w284 := combineObserved 1 w1 w4
def w285 := combineObserved 1 w37 w0
def w286 := combineObserved 1 w37 w2
def w287 := combineObserved 0 w36 w24
def w288 := combineObserved 3 w1 w4
def w289 := combineObserved 1 w288 w5
def w290 := combineObserved 3 w1 w5
def w291 := combineObserved 3 w290 w4
def w292 := combineObserved 1 w188 w5
def w293 := combineObserved 0 w1 w292
def w294 := combineObserved 2 w186 w5
def w295 := combineObserved 3 w186 w19
def w296 := combineObserved 1 w185 w4
def w297 := combineObserved 3 w0 w296
def w298 := combineObserved 1 w296 w5
def w299 := combineObserved 2 w296 w5
def w300 := combineObserved 1 w191 w0
def w301 := combineObserved 3 w84 w1
def w302 := combineObserved 0 w1 w8
def w303 := combineObserved 1 w0 w302
def w304 := combineObserved 2 w2 w3
def w305 := combineObserved 1 w304 w0
def w306 := combineObserved 2 w86 w5
def w307 := combineObserved 1 w85 w4
def w308 := combineObserved 3 w0 w307
def w309 := combineObserved 1 w85 w5
def w310 := combineObserved 1 w307 w5
def w311 := combineObserved 2 w307 w5
def w312 := combineObserved 3 w85 w19
def w313 := combineObserved 1 w0 w312
def w314 := combineObserved 0 w2 w4
def w315 := combineObserved 1 w314 w5
def w316 := combineObserved 0 w2 w5
def w317 := combineObserved 1 w316 w4
def w318 := combineObserved 3 w316 w4
def w319 := combineObserved 3 w316 w30
def w320 := combineObserved 0 w24 w5
def w321 := combineObserved 3 w24 w5
def w322 := combineObserved 1 w321 w314
def w323 := combineObserved 3 w30 w4
def w324 := combineObserved 3 w93 w1
def w325 := combineObserved 1 w196 w5
def w326 := combineObserved 1 w238 w4
def w327 := combineObserved 3 w4 w30
def w328 := combineObserved 3 w2 w4
def w329 := combineObserved 1 w328 w5
def w330 := combineObserved 1 w0 w90
def w331 := combineObserved 1 w90 w5
def w332 := combineObserved 2 w3 w30
def w333 := combineObserved 0 w3 w4
def w334 := combineObserved 1 w333 w5
def w335 := combineObserved 0 w3 w5
def w336 := combineObserved 1 w335 w24
def w337 := combineObserved 3 w335 w24
def w338 := combineObserved 0 w4 w30
def w339 := combineObserved 2 w5 w4
def w340 := combineObserved 3 w339 w30
def w341 := combineObserved 2 w4 w5
def w342 := combineObserved 1 w341 w2
def w343 := combineObserved 1 w0 w269
def w344 := combineObserved 0 w3 w31
def w345 := combineObserved 3 w327 w1
def w346 := combineObserved 1 w199 w0
def w347 := combineObserved 2 w346 w5
def w348 := combineObserved 1 w94 w0
def w349 := combineObserved 3 w0 w95
def w350 := combineObserved 3 w2 w5
def w351 := combineObserved 1 w94 w333
def w352 := combineObserved 1 w350 w4
def w353 := combineObserved 3 w350 w19
def w354 := combineObserved 1 w2 w333
def w355 := combineObserved 2 w354 w5
def w356 := combineObserved 1 w335 w4
def w357 := combineObserved 0 w2 w356
def w358 := combineObserved 1 w333 w30
def w359 := combineObserved 2 w2 w334
def w360 := combineObserved 3 w2 w356
def w361 := combineObserved 3 w335 w4
def w362 := combineObserved 3 w335 w112
def w363 := combineObserved 3 w0 w112
def w364 := combineObserved 3 w363 w1
def w365 := combineObserved 1 w232 w2
def w366 := combineObserved 3 w0 w110
def w367 := combineObserved 1 w43 w0
def w368 := combineObserved 3 w2 w112
def w369 := combineObserved 3 w368 w1
def w370 := combineObserved 3 w3 w5
def w371 := combineObserved 3 w3 w4
def w372 := combineObserved 1 w371 w2
def w373 := combineObserved 0 w4 w5
def w374 := combineObserved 1 w2 w373
def w375 := combineObserved 3 w373 w31
def w376 := combineObserved 2 w2 w19
def w377 := combineObserved 1 w376 w373
def w378 := combineObserved 3 w202 w1
def w379 := combineObserved 3 w0 w119
def w380 := combineObserved 1 w0 w203
def w381 := combineObserved 3 w34 w1
def w382 := combineObserved 1 w2 w122
def w383 := combineObserved 2 w3 w19
def x0 : Sig := 0xaaaaaaaaaaaaaaaa
def x1 : Sig := 0xcccccccccccccccc
def x2 : Sig := 0x8888888888888888
def x3 : Sig := 0xf0f0f0f0f0f0f0f0
def x4 : Sig := 0xc0c0c0c0c0c0c0c0
def x5 : Sig := 0xffff0000ffff0000
def x6 : Sig := 0xffffffff00000000
def x7 : Sig := 0xcccc0000cccc0000
def x8 : Sig := 0xeeeeeeeeeeeeeeee
def x9 : Sig := 0xfafafafafafafafa
def x10 : Sig := 0xffffaaaaffffaaaa
def x11 : Sig := 0xfcfcfcfcfcfcfcfc
def x12 : Sig := 0xfffff0f0fffff0f0
def x13 : Sig := 0xffffffffffff0000
def x14 : Sig := 0xa0a0a0a0a0a0a0a
def x15 : Sig := 0xaaaaaaaa
def x16 : Sig := 0xcccc0000cccc
def x17 : Sig := 0x4444444444444444
def x18 : Sig := 0xf0f00000f0f0000
def x19 : Sig := 0xff00ff00ff00ff00
def x20 : Sig := 0xcc00cc00cc00cc00
def x21 : Sig := 0xf000f000f000f000
def x22 : Sig := 0xf0f0f0f000000000
def x23 : Sig := 0xff00ff0000000000
def x24 : Sig := 0xffff000000000000
def x25 : Sig := 0xfff0fff0fff0fff0
def x26 : Sig := 0xf0f00000f0f00000
def x27 : Sig := 0xfffffffff0f0f0f0
def x28 : Sig := 0xff000000ff000000
def x29 : Sig := 0xffffff00ffffff00
def x30 : Sig := 0xf0f00000f0f0
def x31 : Sig := 0xf0f0f0f0
def x32 : Sig := 0xf0f0f0f00000000
def x33 : Sig := 0xff000000ff0000
def x34 : Sig := 0xcccccccc00000000
def x35 : Sig := 0xc0c0c0c0c0c0c0c
def x36 : Sig := 0xf000f000f000f00
def x37 : Sig := 0xffaaffaaffaaffaa
def x38 : Sig := 0xffffffffaaaaaaaa
def x39 : Sig := 0xffffffffff00ff00
def x40 : Sig := 0xaa00aa00aa00aa
def x41 : Sig := 0xffff0000
def x42 : Sig := 0x5500550055005500
def x43 : Sig := 0x5555000055550000
def x44 : Sig := 0x5555555500000000
def x45 : Sig := 0x5050505050505050
def x46 : Sig := 0xf000f000f000f0
def x47 : Sig := 0xcccccccc
def p0 := prefixPool s0 [] (by decide +kernel)
def p1 := prefixPool s0 [(0,x0,x1)] (by decide +kernel)
def p2 := prefixPool s0 [(0,x0,x1),(1,x2,x3)] (by decide +kernel)
def p3 := prefixPool s0 [(0,x0,x3)] (by decide +kernel)
def p4 := prefixPool s0 [(0,x1,x3)] (by decide +kernel)
def p5 := prefixPool s0 [(0,x1,x3),(0,x4,x5)] (by decide +kernel)
def p6 := prefixPool s0 [(0,x1,x3),(0,x4,x6)] (by decide +kernel)
def p7 := prefixPool s0 [(0,x1,x3),(1,x0,x1),(1,x1,x3)] (by decide +kernel)
def p8 := prefixPool s0 [(0,x1,x3),(1,x4,x0)] (by decide +kernel)
def p9 := prefixPool s0 [(0,x1,x3),(1,x4,x0),(1,x1,x3)] (by decide +kernel)
def p10 := prefixPool s0 [(0,x1,x3),(1,x4,x6)] (by decide +kernel)
def p11 := prefixPool s0 [(0,x1,x3),(1,x1,x3)] (by decide +kernel)
def p12 := prefixPool s0 [(0,x1,x5),(1,x7,x6)] (by decide +kernel)
def p13 := prefixPool s0 [(0,x3,x5)] (by decide +kernel)
def p14 := prefixPool s0 [(0,x3,x6)] (by decide +kernel)
def p15 := prefixPool s0 [(1,x0,x1)] (by decide +kernel)
def p16 := prefixPool s0 [(1,x0,x1),(0,x0,x1),(1,x2,x3)] (by decide +kernel)
def p17 := prefixPool s0 [(1,x0,x1),(1,x0,x3)] (by decide +kernel)
def p18 := prefixPool s0 [(1,x0,x1),(1,x0,x5)] (by decide +kernel)
def p19 := prefixPool s0 [(1,x0,x1),(1,x0,x6),(1,x5,x6)] (by decide +kernel)
def p20 := prefixPool s0 [(1,x0,x1),(1,x8,x3)] (by decide +kernel)
def p21 := prefixPool s0 [(1,x0,x1),(3,x8,x3)] (by decide +kernel)
def p22 := prefixPool s0 [(1,x0,x3)] (by decide +kernel)
def p23 := prefixPool s0 [(1,x0,x3),(0,x9,x1)] (by decide +kernel)
def p24 := prefixPool s0 [(1,x0,x3),(0,x9,x1),(1,x0,x1)] (by decide +kernel)
def p25 := prefixPool s0 [(1,x0,x3),(0,x9,x1),(1,x0,x1),(1,x1,x3)] (by decide +kernel)
def p26 := prefixPool s0 [(1,x0,x3),(1,x0,x6),(1,x5,x6)] (by decide +kernel)
def p27 := prefixPool s0 [(1,x0,x3),(1,x3,x5)] (by decide +kernel)
def p28 := prefixPool s0 [(1,x0,x3),(1,x3,x5),(1,x5,x6)] (by decide +kernel)
def p29 := prefixPool s0 [(1,x0,x3),(1,x9,x5)] (by decide +kernel)
def p30 := prefixPool s0 [(1,x0,x3),(1,x9,x5),(1,x5,x6)] (by decide +kernel)
def p31 := prefixPool s0 [(1,x0,x3),(2,x9,x1)] (by decide +kernel)
def p32 := prefixPool s0 [(1,x0,x3),(2,x9,x5)] (by decide +kernel)
def p33 := prefixPool s0 [(1,x0,x5)] (by decide +kernel)
def p34 := prefixPool s0 [(1,x0,x5),(1,x3,x5)] (by decide +kernel)
def p35 := prefixPool s0 [(1,x0,x5),(1,x10,x6)] (by decide +kernel)
def p36 := prefixPool s0 [(1,x0,x6),(1,x5,x6)] (by decide +kernel)
def p37 := prefixPool s0 [(1,x1,x3),(1,x11,x5)] (by decide +kernel)
def p38 := prefixPool s0 [(1,x3,x5)] (by decide +kernel)
def p39 := prefixPool s0 [(1,x3,x5),(0,x12,x1)] (by decide +kernel)
def p40 := prefixPool s0 [(1,x3,x5),(1,x5,x6)] (by decide +kernel)
def p41 := prefixPool s0 [(1,x3,x5),(1,x12,x6)] (by decide +kernel)
def p42 := prefixPool s0 [(1,x3,x5),(2,x12,x0)] (by decide +kernel)
def p43 := prefixPool s0 [(1,x3,x5),(2,x12,x1)] (by decide +kernel)
def p44 := prefixPool s0 [(1,x3,x5),(2,x12,x1),(1,x5,x6)] (by decide +kernel)
def p45 := prefixPool s0 [(1,x3,x5),(2,x12,x6)] (by decide +kernel)
def p46 := prefixPool s0 [(1,x3,x6)] (by decide +kernel)
def p47 := prefixPool s0 [(1,x3,x6),(1,x5,x6)] (by decide +kernel)
def p48 := prefixPool s0 [(1,x5,x6)] (by decide +kernel)
def p49 := prefixPool s0 [(1,x5,x6),(0,x13,x1)] (by decide +kernel)
def p50 := prefixPool s0 [(1,x5,x6),(0,x13,x3)] (by decide +kernel)
def p51 := prefixPool s0 [(1,x5,x6),(2,x13,x0)] (by decide +kernel)
def p52 := prefixPool s0 [(1,x5,x6),(2,x13,x1)] (by decide +kernel)
def p53 := prefixPool s0 [(1,x5,x6),(2,x13,x3)] (by decide +kernel)
def p54 := prefixPool s0 [(2,x0,x1),(1,x0,x3)] (by decide +kernel)
def p55 := prefixPool s0 [(2,x0,x3)] (by decide +kernel)
def p56 := prefixPool s0 [(2,x0,x3),(1,x14,x1)] (by decide +kernel)
def p57 := prefixPool s0 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p58 := prefixPool s0 [(2,x0,x6),(3,x15,x3)] (by decide +kernel)
def p59 := prefixPool s0 [(2,x1,x3)] (by decide +kernel)
def p60 := prefixPool s0 [(2,x1,x3),(0,x1,x3)] (by decide +kernel)
def p61 := prefixPool s0 [(2,x1,x5),(2,x16,x6)] (by decide +kernel)
def p62 := prefixPool s0 [(2,x1,x6)] (by decide +kernel)
def p63 := prefixPool s0 [(2,x1,x6),(1,x5,x6)] (by decide +kernel)
def p64 := prefixPool s0 [(2,x1,x6),(1,x5,x6),(0,x13,x1)] (by decide +kernel)
def p65 := prefixPool s0 [(2,x1,x6),(3,x0,x1)] (by decide +kernel)
def p66 := prefixPool s0 [(2,x1,x6),(3,x0,x1),(1,x5,x6)] (by decide +kernel)
def p67 := prefixPool s0 [(2,x3,x6)] (by decide +kernel)
def p68 := prefixPool s0 [(3,x0,x1)] (by decide +kernel)
def p69 := prefixPool s0 [(3,x0,x1),(0,x0,x1)] (by decide +kernel)
def p70 := prefixPool s0 [(3,x0,x1),(1,x0,x1),(1,x1,x3)] (by decide +kernel)
def p71 := prefixPool s0 [(3,x0,x1),(1,x5,x6)] (by decide +kernel)
def p72 := prefixPool s0 [(3,x0,x1),(2,x17,x6)] (by decide +kernel)
def p73 := prefixPool s0 [(3,x0,x1),(2,x17,x6),(1,x5,x6)] (by decide +kernel)
def p74 := prefixPool s0 [(3,x0,x3)] (by decide +kernel)
def p75 := prefixPool s0 [(3,x0,x5)] (by decide +kernel)
def p76 := prefixPool s0 [(3,x1,x3)] (by decide +kernel)
def p77 := prefixPool s0 [(3,x1,x3),(1,x0,x3)] (by decide +kernel)
def p78 := prefixPool s0 [(3,x3,x5)] (by decide +kernel)
def p79 := prefixPool s0 [(3,x3,x5),(1,x18,x6)] (by decide +kernel)
def p80 := prefixPool s0 [(3,x3,x6)] (by decide +kernel)
def p81 := prefixPool s1 [] (by decide +kernel)
def p82 := prefixPool s1 [(0,x1,x3)] (by decide +kernel)
def p83 := prefixPool s1 [(0,x1,x19)] (by decide +kernel)
def p84 := prefixPool s1 [(0,x1,x19),(1,x20,x0)] (by decide +kernel)
def p85 := prefixPool s1 [(0,x3,x19)] (by decide +kernel)
def p86 := prefixPool s1 [(0,x3,x19),(1,x21,x0)] (by decide +kernel)
def p87 := prefixPool s1 [(1,x0,x3)] (by decide +kernel)
def p88 := prefixPool s1 [(1,x0,x6)] (by decide +kernel)
def p89 := prefixPool s1 [(1,x3,x6)] (by decide +kernel)
def p90 := prefixPool s1 [(2,x1,x6)] (by decide +kernel)
def p91 := prefixPool s1 [(3,x0,x1)] (by decide +kernel)
def p92 := prefixPool s1 [(3,x0,x19)] (by decide +kernel)
def p93 := prefixPool s2 [] (by decide +kernel)
def p94 := prefixPool s2 [(1,x0,x3)] (by decide +kernel)
def p95 := prefixPool s2 [(1,x0,x5)] (by decide +kernel)
def p96 := prefixPool s2 [(1,x1,x3)] (by decide +kernel)
def p97 := prefixPool s2 [(1,x3,x19)] (by decide +kernel)
def p98 := prefixPool s2 [(1,x3,x5)] (by decide +kernel)
def p99 := prefixPool s2 [(3,x0,x1)] (by decide +kernel)
def p100 := prefixPool s2 [(3,x0,x19)] (by decide +kernel)
def p101 := prefixPool s3 [] (by decide +kernel)
def p102 := prefixPool s3 [(0,x3,x19)] (by decide +kernel)
def p103 := prefixPool s3 [(0,x3,x6),(1,x22,x19),(1,x3,x6)] (by decide +kernel)
def p104 := prefixPool s3 [(0,x3,x6),(1,x22,x5),(1,x3,x6)] (by decide +kernel)
def p105 := prefixPool s3 [(0,x19,x6),(1,x23,x3),(1,x19,x6)] (by decide +kernel)
def p106 := prefixPool s3 [(0,x19,x6),(1,x23,x5),(1,x19,x6)] (by decide +kernel)
def p107 := prefixPool s3 [(0,x5,x6),(1,x24,x3),(1,x5,x6)] (by decide +kernel)
def p108 := prefixPool s3 [(0,x5,x6),(1,x24,x19),(1,x5,x6)] (by decide +kernel)
def p109 := prefixPool s3 [(1,x3,x19)] (by decide +kernel)
def p110 := prefixPool s3 [(1,x3,x19),(0,x3,x19),(1,x21,x6)] (by decide +kernel)
def p111 := prefixPool s3 [(1,x3,x19),(1,x25,x5)] (by decide +kernel)
def p112 := prefixPool s3 [(1,x3,x19),(3,x25,x5)] (by decide +kernel)
def p113 := prefixPool s3 [(1,x3,x5)] (by decide +kernel)
def p114 := prefixPool s3 [(1,x3,x5),(0,x3,x5),(1,x26,x6)] (by decide +kernel)
def p115 := prefixPool s3 [(1,x3,x5),(0,x12,x19)] (by decide +kernel)
def p116 := prefixPool s3 [(1,x3,x5),(0,x12,x6),(1,x5,x6)] (by decide +kernel)
def p117 := prefixPool s3 [(1,x3,x5),(1,x5,x6)] (by decide +kernel)
def p118 := prefixPool s3 [(1,x3,x5),(1,x12,x6)] (by decide +kernel)
def p119 := prefixPool s3 [(1,x3,x5),(2,x12,x19)] (by decide +kernel)
def p120 := prefixPool s3 [(1,x3,x5),(2,x12,x6)] (by decide +kernel)
def p121 := prefixPool s3 [(1,x3,x5),(3,x12,x6)] (by decide +kernel)
def p122 := prefixPool s3 [(1,x3,x6)] (by decide +kernel)
def p123 := prefixPool s3 [(1,x3,x6),(1,x5,x6)] (by decide +kernel)
def p124 := prefixPool s3 [(1,x3,x6),(2,x27,x5)] (by decide +kernel)
def p125 := prefixPool s3 [(1,x19,x5)] (by decide +kernel)
def p126 := prefixPool s3 [(1,x19,x5),(0,x19,x5),(1,x28,x6)] (by decide +kernel)
def p127 := prefixPool s3 [(1,x19,x5),(2,x29,x3)] (by decide +kernel)
def p128 := prefixPool s3 [(1,x19,x6)] (by decide +kernel)
def p129 := prefixPool s3 [(1,x5,x6)] (by decide +kernel)
def p130 := prefixPool s3 [(1,x5,x6),(0,x13,x3)] (by decide +kernel)
def p131 := prefixPool s3 [(1,x5,x6),(0,x13,x19)] (by decide +kernel)
def p132 := prefixPool s3 [(1,x5,x6),(2,x13,x3)] (by decide +kernel)
def p133 := prefixPool s3 [(1,x5,x6),(2,x13,x19)] (by decide +kernel)
def p134 := prefixPool s3 [(2,x3,x5)] (by decide +kernel)
def p135 := prefixPool s3 [(2,x3,x5),(2,x30,x6)] (by decide +kernel)
def p136 := prefixPool s3 [(2,x3,x6)] (by decide +kernel)
def p137 := prefixPool s3 [(2,x3,x6),(1,x31,x5)] (by decide +kernel)
def p138 := prefixPool s3 [(2,x19,x5)] (by decide +kernel)
def p139 := prefixPool s3 [(2,x19,x6)] (by decide +kernel)
def p140 := prefixPool s3 [(3,x3,x19)] (by decide +kernel)
def p141 := prefixPool s3 [(3,x3,x5)] (by decide +kernel)
def p142 := prefixPool s3 [(3,x3,x5),(1,x18,x6)] (by decide +kernel)
def p143 := prefixPool s3 [(3,x3,x5),(2,x18,x6)] (by decide +kernel)
def p144 := prefixPool s3 [(3,x3,x6)] (by decide +kernel)
def p145 := prefixPool s3 [(3,x3,x6),(1,x32,x5)] (by decide +kernel)
def p146 := prefixPool s3 [(3,x19,x5),(1,x33,x3)] (by decide +kernel)
def p147 := prefixPool s3 [(3,x5,x6)] (by decide +kernel)
def p148 := prefixPool s4 [] (by decide +kernel)
def p149 := prefixPool s5 [] (by decide +kernel)
def p150 := prefixPool s5 [(1,x5,x6)] (by decide +kernel)
def p151 := prefixPool s6 [] (by decide +kernel)
def p152 := prefixPool s7 [] (by decide +kernel)
def p153 := prefixPool s8 [] (by decide +kernel)
def p154 := prefixPool s8 [(0,x1,x3)] (by decide +kernel)
def p155 := prefixPool s8 [(0,x1,x3),(0,x4,x19)] (by decide +kernel)
def p156 := prefixPool s8 [(0,x1,x3),(1,x4,x6)] (by decide +kernel)
def p157 := prefixPool s8 [(0,x1,x3),(2,x4,x6)] (by decide +kernel)
def p158 := prefixPool s8 [(0,x1,x3),(3,x4,x6)] (by decide +kernel)
def p159 := prefixPool s8 [(0,x1,x19)] (by decide +kernel)
def p160 := prefixPool s8 [(0,x1,x19),(1,x20,x3)] (by decide +kernel)
def p161 := prefixPool s8 [(0,x1,x19),(1,x20,x6)] (by decide +kernel)
def p162 := prefixPool s8 [(0,x1,x19),(1,x3,x6),(0,x27,x1)] (by decide +kernel)
def p163 := prefixPool s8 [(0,x1,x19),(2,x20,x6)] (by decide +kernel)
def p164 := prefixPool s8 [(0,x1,x19),(3,x20,x3)] (by decide +kernel)
def p165 := prefixPool s8 [(0,x1,x19),(3,x20,x6)] (by decide +kernel)
def p166 := prefixPool s8 [(0,x1,x6)] (by decide +kernel)
def p167 := prefixPool s8 [(0,x1,x6),(1,x34,x3)] (by decide +kernel)
def p168 := prefixPool s8 [(0,x1,x6),(3,x34,x3)] (by decide +kernel)
def p169 := prefixPool s8 [(0,x3,x19)] (by decide +kernel)
def p170 := prefixPool s8 [(0,x3,x19),(0,x21,x6)] (by decide +kernel)
def p171 := prefixPool s8 [(0,x3,x19),(0,x3,x6)] (by decide +kernel)
def p172 := prefixPool s8 [(0,x3,x19),(1,x21,x6)] (by decide +kernel)
def p173 := prefixPool s8 [(0,x3,x19),(3,x21,x6)] (by decide +kernel)
def p174 := prefixPool s8 [(0,x3,x6)] (by decide +kernel)
def p175 := prefixPool s8 [(0,x3,x6),(1,x3,x6)] (by decide +kernel)
def p176 := prefixPool s8 [(0,x19,x6)] (by decide +kernel)
def p177 := prefixPool s8 [(0,x19,x6),(3,x23,x3)] (by decide +kernel)
def p178 := prefixPool s8 [(1,x1,x6)] (by decide +kernel)
def p179 := prefixPool s8 [(1,x3,x19)] (by decide +kernel)
def p180 := prefixPool s8 [(1,x3,x6)] (by decide +kernel)
def p181 := prefixPool s8 [(1,x3,x6),(0,x27,x1)] (by decide +kernel)
def p182 := prefixPool s8 [(1,x19,x6)] (by decide +kernel)
def p183 := prefixPool s8 [(2,x1,x3)] (by decide +kernel)
def p184 := prefixPool s8 [(2,x1,x3),(2,x35,x6)] (by decide +kernel)
def p185 := prefixPool s8 [(2,x1,x6)] (by decide +kernel)
def p186 := prefixPool s8 [(2,x3,x19)] (by decide +kernel)
def p187 := prefixPool s8 [(2,x3,x6)] (by decide +kernel)
def p188 := prefixPool s8 [(2,x3,x6),(0,x1,x6)] (by decide +kernel)
def p189 := prefixPool s8 [(2,x3,x6),(1,x31,x19)] (by decide +kernel)
def p190 := prefixPool s8 [(2,x19,x6)] (by decide +kernel)
def p191 := prefixPool s8 [(3,x1,x3)] (by decide +kernel)
def p192 := prefixPool s8 [(3,x3,x19)] (by decide +kernel)
def p193 := prefixPool s8 [(3,x3,x19),(0,x36,x6)] (by decide +kernel)
def p194 := prefixPool s8 [(3,x3,x19),(3,x36,x6)] (by decide +kernel)
def p195 := prefixPool s8 [(3,x3,x19),(3,x3,x6)] (by decide +kernel)
def p196 := prefixPool s8 [(3,x3,x6)] (by decide +kernel)
def p197 := prefixPool s8 [(3,x3,x6),(0,x1,x3)] (by decide +kernel)
def p198 := prefixPool s8 [(3,x3,x6),(0,x3,x19)] (by decide +kernel)
def p199 := prefixPool s8 [(3,x3,x6),(0,x3,x19),(0,x19,x6)] (by decide +kernel)
def p200 := prefixPool s8 [(3,x3,x6),(3,x32,x19)] (by decide +kernel)
def p201 := prefixPool s8 [(3,x19,x6)] (by decide +kernel)
def p202 := prefixPool s9 [] (by decide +kernel)
def p203 := prefixPool s9 [(0,x1,x3)] (by decide +kernel)
def p204 := prefixPool s9 [(0,x1,x3),(1,x4,x5)] (by decide +kernel)
def p205 := prefixPool s9 [(0,x1,x3),(3,x4,x5)] (by decide +kernel)
def p206 := prefixPool s9 [(0,x1,x19)] (by decide +kernel)
def p207 := prefixPool s9 [(0,x1,x19),(0,x20,x5)] (by decide +kernel)
def p208 := prefixPool s9 [(0,x1,x19),(0,x1,x5)] (by decide +kernel)
def p209 := prefixPool s9 [(0,x1,x19),(1,x20,x3)] (by decide +kernel)
def p210 := prefixPool s9 [(0,x1,x19),(1,x20,x5)] (by decide +kernel)
def p211 := prefixPool s9 [(0,x1,x19),(3,x20,x3)] (by decide +kernel)
def p212 := prefixPool s9 [(0,x1,x19),(3,x20,x5)] (by decide +kernel)
def p213 := prefixPool s9 [(0,x1,x5)] (by decide +kernel)
def p214 := prefixPool s9 [(0,x3,x19)] (by decide +kernel)
def p215 := prefixPool s9 [(0,x3,x19),(1,x21,x5)] (by decide +kernel)
def p216 := prefixPool s9 [(0,x3,x19),(1,x3,x19)] (by decide +kernel)
def p217 := prefixPool s9 [(0,x3,x19),(3,x21,x5)] (by decide +kernel)
def p218 := prefixPool s9 [(0,x3,x5)] (by decide +kernel)
def p219 := prefixPool s9 [(0,x3,x5),(1,x3,x5)] (by decide +kernel)
def p220 := prefixPool s9 [(0,x19,x5)] (by decide +kernel)
def p221 := prefixPool s9 [(1,x1,x3)] (by decide +kernel)
def p222 := prefixPool s9 [(1,x1,x5)] (by decide +kernel)
def p223 := prefixPool s9 [(1,x3,x19)] (by decide +kernel)
def p224 := prefixPool s9 [(1,x3,x5)] (by decide +kernel)
def p225 := prefixPool s9 [(1,x3,x5),(0,x12,x1)] (by decide +kernel)
def p226 := prefixPool s9 [(1,x19,x5)] (by decide +kernel)
def p227 := prefixPool s9 [(1,x19,x5),(0,x29,x1)] (by decide +kernel)
def p228 := prefixPool s9 [(2,x1,x3)] (by decide +kernel)
def p229 := prefixPool s9 [(2,x1,x3),(1,x35,x5)] (by decide +kernel)
def p230 := prefixPool s9 [(2,x1,x19)] (by decide +kernel)
def p231 := prefixPool s9 [(2,x1,x5)] (by decide +kernel)
def p232 := prefixPool s9 [(2,x3,x5)] (by decide +kernel)
def p233 := prefixPool s9 [(2,x3,x5),(0,x1,x5)] (by decide +kernel)
def p234 := prefixPool s9 [(2,x3,x5),(3,x30,x1)] (by decide +kernel)
def p235 := prefixPool s9 [(2,x19,x5)] (by decide +kernel)
def p236 := prefixPool s9 [(3,x1,x5)] (by decide +kernel)
def p237 := prefixPool s9 [(3,x3,x19)] (by decide +kernel)
def p238 := prefixPool s9 [(3,x3,x19),(1,x36,x5)] (by decide +kernel)
def p239 := prefixPool s9 [(3,x3,x19),(3,x36,x5)] (by decide +kernel)
def p240 := prefixPool s9 [(3,x3,x5)] (by decide +kernel)
def p241 := prefixPool s9 [(3,x3,x5),(0,x1,x3)] (by decide +kernel)
def p242 := prefixPool s9 [(3,x3,x5),(0,x3,x19)] (by decide +kernel)
def p243 := prefixPool s9 [(3,x19,x5)] (by decide +kernel)
def p244 := prefixPool s10 [] (by decide +kernel)
def p245 := prefixPool s10 [(0,x0,x5)] (by decide +kernel)
def p246 := prefixPool s10 [(0,x0,x6)] (by decide +kernel)
def p247 := prefixPool s10 [(0,x19,x5)] (by decide +kernel)
def p248 := prefixPool s10 [(0,x19,x5),(1,x28,x6)] (by decide +kernel)
def p249 := prefixPool s10 [(0,x19,x6)] (by decide +kernel)
def p250 := prefixPool s10 [(0,x19,x6),(1,x23,x5)] (by decide +kernel)
def p251 := prefixPool s10 [(0,x19,x6),(3,x23,x5)] (by decide +kernel)
def p252 := prefixPool s10 [(0,x5,x6)] (by decide +kernel)
def p253 := prefixPool s10 [(0,x5,x6),(1,x5,x6)] (by decide +kernel)
def p254 := prefixPool s10 [(1,x0,x19)] (by decide +kernel)
def p255 := prefixPool s10 [(1,x0,x19),(1,x0,x5)] (by decide +kernel)
def p256 := prefixPool s10 [(1,x0,x19),(1,x0,x6)] (by decide +kernel)
def p257 := prefixPool s10 [(1,x0,x19),(1,x37,x5)] (by decide +kernel)
def p258 := prefixPool s10 [(1,x0,x19),(1,x37,x6)] (by decide +kernel)
def p259 := prefixPool s10 [(1,x0,x19),(3,x37,x5)] (by decide +kernel)
def p260 := prefixPool s10 [(1,x0,x5)] (by decide +kernel)
def p261 := prefixPool s10 [(1,x0,x5),(1,x0,x6)] (by decide +kernel)
def p262 := prefixPool s10 [(1,x0,x5),(1,x5,x6)] (by decide +kernel)
def p263 := prefixPool s10 [(1,x0,x5),(1,x10,x6)] (by decide +kernel)
def p264 := prefixPool s10 [(1,x0,x5),(2,x10,x6)] (by decide +kernel)
def p265 := prefixPool s10 [(1,x0,x5),(3,x10,x6)] (by decide +kernel)
def p266 := prefixPool s10 [(1,x0,x6)] (by decide +kernel)
def p267 := prefixPool s10 [(1,x0,x6),(1,x5,x6)] (by decide +kernel)
def p268 := prefixPool s10 [(1,x0,x6),(2,x38,x5)] (by decide +kernel)
def p269 := prefixPool s10 [(1,x19,x5)] (by decide +kernel)
def p270 := prefixPool s10 [(1,x19,x5),(1,x5,x6)] (by decide +kernel)
def p271 := prefixPool s10 [(1,x19,x5),(1,x29,x6)] (by decide +kernel)
def p272 := prefixPool s10 [(1,x19,x5),(2,x29,x0)] (by decide +kernel)
def p273 := prefixPool s10 [(1,x19,x5),(3,x29,x6)] (by decide +kernel)
def p274 := prefixPool s10 [(1,x19,x6)] (by decide +kernel)
def p275 := prefixPool s10 [(1,x19,x6),(2,x39,x0)] (by decide +kernel)
def p276 := prefixPool s10 [(1,x5,x6)] (by decide +kernel)
def p277 := prefixPool s10 [(1,x5,x6),(0,x13,x19)] (by decide +kernel)
def p278 := prefixPool s10 [(1,x5,x6),(2,x13,x0)] (by decide +kernel)
def p279 := prefixPool s10 [(1,x5,x6),(2,x13,x19)] (by decide +kernel)
def p280 := prefixPool s10 [(2,x0,x19)] (by decide +kernel)
def p281 := prefixPool s10 [(2,x0,x19),(2,x40,x5)] (by decide +kernel)
def p282 := prefixPool s10 [(2,x0,x5)] (by decide +kernel)
def p283 := prefixPool s10 [(2,x0,x5),(1,x0,x19)] (by decide +kernel)
def p284 := prefixPool s10 [(2,x0,x6)] (by decide +kernel)
def p285 := prefixPool s10 [(2,x0,x6),(1,x15,x19)] (by decide +kernel)
def p286 := prefixPool s10 [(2,x0,x6),(1,x15,x5)] (by decide +kernel)
def p287 := prefixPool s10 [(2,x0,x6),(3,x0,x6)] (by decide +kernel)
def p288 := prefixPool s10 [(2,x19,x5)] (by decide +kernel)
def p289 := prefixPool s10 [(2,x19,x6)] (by decide +kernel)
def p290 := prefixPool s10 [(2,x5,x6)] (by decide +kernel)
def p291 := prefixPool s10 [(2,x5,x6),(1,x41,x0)] (by decide +kernel)
def p292 := prefixPool s10 [(2,x5,x6),(1,x0,x5)] (by decide +kernel)
def p293 := prefixPool s10 [(2,x5,x6),(3,x5,x6)] (by decide +kernel)
def p294 := prefixPool s10 [(3,x0,x19)] (by decide +kernel)
def p295 := prefixPool s10 [(3,x0,x19),(1,x42,x5)] (by decide +kernel)
def p296 := prefixPool s10 [(3,x0,x5)] (by decide +kernel)
def p297 := prefixPool s10 [(3,x0,x5),(1,x43,x6)] (by decide +kernel)
def p298 := prefixPool s10 [(3,x0,x5),(1,x5,x6)] (by decide +kernel)
def p299 := prefixPool s10 [(3,x0,x5),(2,x43,x6)] (by decide +kernel)
def p300 := prefixPool s10 [(3,x0,x6)] (by decide +kernel)
def p301 := prefixPool s10 [(3,x0,x6),(1,x44,x5)] (by decide +kernel)
def p302 := prefixPool s10 [(3,x0,x6),(1,x5,x6)] (by decide +kernel)
def p303 := prefixPool s10 [(3,x19,x5),(1,x5,x6)] (by decide +kernel)
def p304 := prefixPool s10 [(3,x19,x6),(1,x5,x6)] (by decide +kernel)
def p305 := prefixPool s10 [(3,x5,x6)] (by decide +kernel)
def p306 := prefixPool s11 [] (by decide +kernel)
def p307 := prefixPool s11 [(1,x0,x3)] (by decide +kernel)
def p308 := prefixPool s11 [(1,x5,x6)] (by decide +kernel)
def p309 := prefixPool s12 [] (by decide +kernel)
def p310 := prefixPool s12 [(0,x0,x3)] (by decide +kernel)
def p311 := prefixPool s12 [(0,x0,x6)] (by decide +kernel)
def p312 := prefixPool s12 [(0,x3,x5)] (by decide +kernel)
def p313 := prefixPool s12 [(0,x3,x5),(1,x3,x5)] (by decide +kernel)
def p314 := prefixPool s12 [(1,x0,x3)] (by decide +kernel)
def p315 := prefixPool s12 [(1,x0,x3),(1,x0,x5)] (by decide +kernel)
def p316 := prefixPool s12 [(1,x0,x3),(1,x0,x5),(1,x3,x5)] (by decide +kernel)
def p317 := prefixPool s12 [(1,x0,x3),(1,x0,x5),(1,x10,x6)] (by decide +kernel)
def p318 := prefixPool s12 [(1,x0,x3),(1,x3,x5)] (by decide +kernel)
def p319 := prefixPool s12 [(1,x0,x3),(1,x9,x5)] (by decide +kernel)
def p320 := prefixPool s12 [(1,x0,x3),(1,x9,x6)] (by decide +kernel)
def p321 := prefixPool s12 [(1,x0,x3),(1,x9,x6),(1,x5,x6)] (by decide +kernel)
def p322 := prefixPool s12 [(1,x0,x3),(1,x5,x6)] (by decide +kernel)
def p323 := prefixPool s12 [(1,x0,x3),(2,x9,x5)] (by decide +kernel)
def p324 := prefixPool s12 [(1,x0,x3),(2,x9,x5),(1,x9,x5)] (by decide +kernel)
def p325 := prefixPool s12 [(1,x0,x3),(2,x9,x6)] (by decide +kernel)
def p326 := prefixPool s12 [(1,x0,x3),(3,x9,x5)] (by decide +kernel)
def p327 := prefixPool s12 [(1,x0,x5)] (by decide +kernel)
def p328 := prefixPool s12 [(1,x0,x5),(1,x3,x5)] (by decide +kernel)
def p329 := prefixPool s12 [(1,x0,x5),(1,x5,x6)] (by decide +kernel)
def p330 := prefixPool s12 [(1,x0,x5),(1,x10,x6)] (by decide +kernel)
def p331 := prefixPool s12 [(1,x0,x5),(3,x10,x6)] (by decide +kernel)
def p332 := prefixPool s12 [(1,x0,x6)] (by decide +kernel)
def p333 := prefixPool s12 [(1,x0,x6),(1,x3,x6)] (by decide +kernel)
def p334 := prefixPool s12 [(1,x0,x6),(1,x5,x6)] (by decide +kernel)
def p335 := prefixPool s12 [(1,x0,x6),(2,x38,x5)] (by decide +kernel)
def p336 := prefixPool s12 [(1,x3,x5)] (by decide +kernel)
def p337 := prefixPool s12 [(1,x3,x5),(1,x3,x6),(1,x5,x6)] (by decide +kernel)
def p338 := prefixPool s12 [(1,x3,x5),(1,x5,x6)] (by decide +kernel)
def p339 := prefixPool s12 [(1,x3,x5),(1,x12,x6)] (by decide +kernel)
def p340 := prefixPool s12 [(1,x3,x5),(2,x12,x0)] (by decide +kernel)
def p341 := prefixPool s12 [(1,x3,x5),(2,x12,x6)] (by decide +kernel)
def p342 := prefixPool s12 [(1,x3,x6)] (by decide +kernel)
def p343 := prefixPool s12 [(1,x3,x6),(1,x5,x6)] (by decide +kernel)
def p344 := prefixPool s12 [(1,x5,x6)] (by decide +kernel)
def p345 := prefixPool s12 [(1,x5,x6),(0,x13,x3)] (by decide +kernel)
def p346 := prefixPool s12 [(1,x5,x6),(2,x13,x0)] (by decide +kernel)
def p347 := prefixPool s12 [(1,x5,x6),(2,x13,x3)] (by decide +kernel)
def p348 := prefixPool s12 [(2,x0,x3)] (by decide +kernel)
def p349 := prefixPool s12 [(2,x0,x3),(3,x0,x3)] (by decide +kernel)
def p350 := prefixPool s12 [(2,x0,x6)] (by decide +kernel)
def p351 := prefixPool s12 [(2,x3,x5)] (by decide +kernel)
def p352 := prefixPool s12 [(2,x3,x5),(1,x30,x0)] (by decide +kernel)
def p353 := prefixPool s12 [(2,x3,x6)] (by decide +kernel)
def p354 := prefixPool s12 [(2,x3,x6),(1,x31,x5)] (by decide +kernel)
def p355 := prefixPool s12 [(2,x3,x6),(1,x0,x3)] (by decide +kernel)
def p356 := prefixPool s12 [(2,x5,x6)] (by decide +kernel)
def p357 := prefixPool s12 [(3,x0,x3)] (by decide +kernel)
def p358 := prefixPool s12 [(3,x0,x3),(1,x45,x5)] (by decide +kernel)
def p359 := prefixPool s12 [(3,x0,x3),(1,x3,x5)] (by decide +kernel)
def p360 := prefixPool s12 [(3,x0,x3),(2,x45,x5)] (by decide +kernel)
def p361 := prefixPool s12 [(3,x0,x3),(2,x45,x6)] (by decide +kernel)
def p362 := prefixPool s12 [(3,x0,x5)] (by decide +kernel)
def p363 := prefixPool s12 [(3,x0,x5),(2,x43,x6)] (by decide +kernel)
def p364 := prefixPool s12 [(3,x0,x6),(1,x3,x6)] (by decide +kernel)
def p365 := prefixPool s12 [(3,x0,x6),(1,x5,x6)] (by decide +kernel)
def p366 := prefixPool s12 [(3,x3,x5)] (by decide +kernel)
def p367 := prefixPool s12 [(3,x3,x6)] (by decide +kernel)
def p368 := prefixPool s13 [] (by decide +kernel)
def p369 := prefixPool s13 [(0,x3,x6)] (by decide +kernel)
def p370 := prefixPool s13 [(0,x3,x6),(1,x3,x6)] (by decide +kernel)
def p371 := prefixPool s13 [(1,x0,x3)] (by decide +kernel)
def p372 := prefixPool s13 [(1,x0,x3),(1,x9,x6)] (by decide +kernel)
def p373 := prefixPool s13 [(1,x0,x6),(2,x38,x3)] (by decide +kernel)
def p374 := prefixPool s13 [(1,x3,x19)] (by decide +kernel)
def p375 := prefixPool s13 [(1,x3,x19),(3,x25,x6)] (by decide +kernel)
def p376 := prefixPool s13 [(1,x3,x6)] (by decide +kernel)
def p377 := prefixPool s13 [(1,x3,x6),(2,x27,x0)] (by decide +kernel)
def p378 := prefixPool s13 [(1,x3,x6),(2,x27,x19)] (by decide +kernel)
def p379 := prefixPool s13 [(2,x3,x19),(2,x46,x6)] (by decide +kernel)
def p380 := prefixPool s13 [(2,x3,x6)] (by decide +kernel)
def p381 := prefixPool s13 [(3,x3,x19)] (by decide +kernel)
def p382 := prefixPool s13 [(3,x3,x6)] (by decide +kernel)
def p383 := prefixPool s14 [] (by decide +kernel)
def p384 := prefixPool s14 [(1,x0,x3)] (by decide +kernel)
def p385 := prefixPool s14 [(1,x0,x3),(1,x9,x5)] (by decide +kernel)
def p386 := prefixPool s14 [(1,x0,x3),(2,x9,x5)] (by decide +kernel)
def p387 := prefixPool s14 [(1,x0,x5)] (by decide +kernel)
def p388 := prefixPool s14 [(1,x0,x5),(1,x3,x5)] (by decide +kernel)
def p389 := prefixPool s14 [(1,x3,x19)] (by decide +kernel)
def p390 := prefixPool s14 [(1,x3,x5)] (by decide +kernel)
def p391 := prefixPool s14 [(1,x3,x5),(2,x12,x0)] (by decide +kernel)
def p392 := prefixPool s14 [(1,x3,x5),(2,x12,x19)] (by decide +kernel)
def p393 := prefixPool s14 [(1,x19,x5)] (by decide +kernel)
def p394 := prefixPool s14 [(2,x3,x19),(2,x46,x5)] (by decide +kernel)
def p395 := prefixPool s14 [(2,x3,x5)] (by decide +kernel)
def p396 := prefixPool s14 [(3,x3,x5)] (by decide +kernel)
def p397 := prefixPool s14 [(3,x3,x5),(1,x18,x19)] (by decide +kernel)
def p398 := prefixPool s15 [] (by decide +kernel)
def p399 := prefixPool s15 [(1,x5,x6)] (by decide +kernel)
def p400 := prefixPool s16 [] (by decide +kernel)
def p401 := prefixPool s16 [(0,x1,x19)] (by decide +kernel)
def p402 := prefixPool s17 [] (by decide +kernel)
def p403 := prefixPool s18 [] (by decide +kernel)
def p404 := prefixPool s19 [] (by decide +kernel)
def p405 := prefixPool s19 [(1,x0,x5)] (by decide +kernel)
def p406 := prefixPool s19 [(3,x0,x1)] (by decide +kernel)
def p407 := prefixPool s20 [] (by decide +kernel)
def p408 := prefixPool s20 [(0,x0,x1)] (by decide +kernel)
def p409 := prefixPool s20 [(0,x1,x3)] (by decide +kernel)
def p410 := prefixPool s20 [(0,x1,x3),(1,x4,x0)] (by decide +kernel)
def p411 := prefixPool s20 [(0,x1,x3),(1,x4,x6)] (by decide +kernel)
def p412 := prefixPool s20 [(0,x1,x3),(1,x1,x3)] (by decide +kernel)
def p413 := prefixPool s20 [(0,x1,x3),(2,x4,x6)] (by decide +kernel)
def p414 := prefixPool s20 [(0,x1,x3),(3,x4,x6)] (by decide +kernel)
def p415 := prefixPool s20 [(0,x1,x6)] (by decide +kernel)
def p416 := prefixPool s20 [(0,x1,x6),(1,x0,x3)] (by decide +kernel)
def p417 := prefixPool s20 [(0,x1,x6),(1,x34,x0)] (by decide +kernel)
def p418 := prefixPool s20 [(0,x1,x6),(1,x34,x3)] (by decide +kernel)
def p419 := prefixPool s20 [(0,x1,x6),(3,x34,x3)] (by decide +kernel)
def p420 := prefixPool s20 [(0,x3,x6)] (by decide +kernel)
def p421 := prefixPool s20 [(0,x3,x6),(1,x3,x6)] (by decide +kernel)
def p422 := prefixPool s20 [(1,x0,x1)] (by decide +kernel)
def p423 := prefixPool s20 [(1,x0,x1),(1,x0,x3)] (by decide +kernel)
def p424 := prefixPool s20 [(1,x0,x1),(1,x0,x6)] (by decide +kernel)
def p425 := prefixPool s20 [(1,x0,x3)] (by decide +kernel)
def p426 := prefixPool s20 [(1,x0,x3),(0,x9,x1)] (by decide +kernel)
def p427 := prefixPool s20 [(1,x0,x3),(0,x9,x1),(1,x0,x1)] (by decide +kernel)
def p428 := prefixPool s20 [(1,x0,x3),(1,x0,x6)] (by decide +kernel)
def p429 := prefixPool s20 [(1,x0,x3),(1,x3,x6)] (by decide +kernel)
def p430 := prefixPool s20 [(1,x0,x3),(1,x9,x6)] (by decide +kernel)
def p431 := prefixPool s20 [(1,x0,x3),(2,x9,x6)] (by decide +kernel)
def p432 := prefixPool s20 [(1,x0,x6)] (by decide +kernel)
def p433 := prefixPool s20 [(1,x0,x6),(0,x38,x1)] (by decide +kernel)
def p434 := prefixPool s20 [(1,x0,x6),(0,x38,x1),(1,x0,x1)] (by decide +kernel)
def p435 := prefixPool s20 [(1,x0,x6),(0,x38,x3)] (by decide +kernel)
def p436 := prefixPool s20 [(1,x0,x6),(1,x3,x6)] (by decide +kernel)
def p437 := prefixPool s20 [(1,x0,x6),(2,x38,x1)] (by decide +kernel)
def p438 := prefixPool s20 [(1,x0,x6),(2,x38,x3)] (by decide +kernel)
def p439 := prefixPool s20 [(1,x1,x3)] (by decide +kernel)
def p440 := prefixPool s20 [(1,x3,x6)] (by decide +kernel)
def p441 := prefixPool s20 [(1,x3,x6),(0,x27,x1)] (by decide +kernel)
def p442 := prefixPool s20 [(1,x3,x6),(2,x27,x0)] (by decide +kernel)
def p443 := prefixPool s20 [(2,x1,x3)] (by decide +kernel)
def p444 := prefixPool s20 [(2,x1,x3),(0,x35,x6)] (by decide +kernel)
def p445 := prefixPool s20 [(2,x1,x3),(2,x35,x6)] (by decide +kernel)
def p446 := prefixPool s20 [(2,x1,x3),(3,x0,x1)] (by decide +kernel)
def p447 := prefixPool s20 [(2,x1,x6)] (by decide +kernel)
def p448 := prefixPool s20 [(2,x1,x6),(1,x47,x0)] (by decide +kernel)
def p449 := prefixPool s20 [(2,x1,x6),(3,x0,x1)] (by decide +kernel)
def p450 := prefixPool s20 [(2,x3,x6)] (by decide +kernel)
def p451 := prefixPool s20 [(2,x3,x6),(1,x31,x0)] (by decide +kernel)
def p452 := prefixPool s20 [(2,x3,x6),(1,x0,x3)] (by decide +kernel)
def p453 := prefixPool s20 [(2,x3,x6),(3,x0,x1)] (by decide +kernel)
def p454 := prefixPool s20 [(3,x0,x1)] (by decide +kernel)
def p455 := prefixPool s20 [(3,x0,x1),(2,x17,x3)] (by decide +kernel)
def p456 := prefixPool s20 [(3,x0,x1),(2,x17,x6)] (by decide +kernel)
def p457 := prefixPool s20 [(3,x0,x3)] (by decide +kernel)
def p458 := prefixPool s20 [(3,x0,x3),(1,x0,x3)] (by decide +kernel)
def p459 := prefixPool s20 [(3,x0,x3),(3,x45,x6)] (by decide +kernel)
def p460 := prefixPool s20 [(3,x0,x6)] (by decide +kernel)
def p461 := prefixPool s20 [(3,x0,x6),(1,x44,x3)] (by decide +kernel)
def p462 := prefixPool s20 [(3,x0,x6),(1,x3,x6)] (by decide +kernel)
def p463 := prefixPool s20 [(3,x0,x6),(3,x44,x1)] (by decide +kernel)
def p464 := prefixPool s20 [(3,x3,x6)] (by decide +kernel)
def p465 := prefixPool s20 [(3,x3,x6),(1,x32,x0)] (by decide +kernel)
def p466 := prefixPool s20 [(3,x3,x6),(1,x32,x1)] (by decide +kernel)
def p467 := prefixPool s20 [(3,x3,x6),(1,x0,x6)] (by decide +kernel)
def p468 := prefixPool s20 [(3,x3,x6),(3,x0,x1)] (by decide +kernel)
def p469 := prefixPool s21 [] (by decide +kernel)
def p470 := prefixPool s21 [(0,x0,x1)] (by decide +kernel)
def p471 := prefixPool s21 [(0,x1,x3)] (by decide +kernel)
def p472 := prefixPool s21 [(0,x1,x3),(1,x4,x0)] (by decide +kernel)
def p473 := prefixPool s21 [(0,x1,x3),(1,x4,x5)] (by decide +kernel)
def p474 := prefixPool s21 [(0,x1,x3),(3,x4,x5)] (by decide +kernel)
def p475 := prefixPool s21 [(0,x1,x5)] (by decide +kernel)
def p476 := prefixPool s21 [(0,x1,x5),(1,x0,x3)] (by decide +kernel)
def p477 := prefixPool s21 [(0,x1,x5),(1,x7,x0)] (by decide +kernel)
def p478 := prefixPool s21 [(0,x1,x5),(1,x7,x3)] (by decide +kernel)
def p479 := prefixPool s21 [(0,x3,x5)] (by decide +kernel)
def p480 := prefixPool s21 [(0,x3,x5),(1,x26,x0)] (by decide +kernel)
def p481 := prefixPool s21 [(1,x0,x1)] (by decide +kernel)
def p482 := prefixPool s21 [(1,x0,x1),(1,x0,x3)] (by decide +kernel)
def p483 := prefixPool s21 [(1,x0,x3)] (by decide +kernel)
def p484 := prefixPool s21 [(1,x0,x3),(0,x9,x1)] (by decide +kernel)
def p485 := prefixPool s21 [(1,x0,x3),(0,x9,x1),(1,x0,x1)] (by decide +kernel)
def p486 := prefixPool s21 [(1,x0,x3),(1,x0,x5)] (by decide +kernel)
def p487 := prefixPool s21 [(1,x0,x3),(1,x9,x5)] (by decide +kernel)
def p488 := prefixPool s21 [(1,x0,x5)] (by decide +kernel)
def p489 := prefixPool s21 [(1,x0,x5),(0,x10,x1)] (by decide +kernel)
def p490 := prefixPool s21 [(1,x0,x5),(1,x3,x5)] (by decide +kernel)
def p491 := prefixPool s21 [(1,x0,x5),(2,x10,x3)] (by decide +kernel)
def p492 := prefixPool s21 [(1,x1,x3)] (by decide +kernel)
def p493 := prefixPool s21 [(1,x3,x5)] (by decide +kernel)
def p494 := prefixPool s21 [(1,x3,x5),(0,x12,x1)] (by decide +kernel)
def p495 := prefixPool s21 [(1,x3,x5),(2,x12,x0)] (by decide +kernel)
def p496 := prefixPool s21 [(2,x0,x3)] (by decide +kernel)
def p497 := prefixPool s21 [(2,x1,x3)] (by decide +kernel)
def p498 := prefixPool s21 [(2,x1,x3),(3,x0,x1)] (by decide +kernel)
def p499 := prefixPool s21 [(2,x1,x5)] (by decide +kernel)
def p500 := prefixPool s21 [(2,x3,x5),(1,x30,x0)] (by decide +kernel)
def p501 := prefixPool s21 [(3,x0,x1)] (by decide +kernel)
def p502 := prefixPool s21 [(3,x0,x1),(1,x1,x3)] (by decide +kernel)
def p503 := prefixPool s21 [(3,x0,x1),(1,x1,x5)] (by decide +kernel)
def p504 := prefixPool s21 [(3,x0,x1),(1,x3,x5)] (by decide +kernel)
def p505 := prefixPool s21 [(3,x0,x1),(2,x17,x3)] (by decide +kernel)
def p506 := prefixPool s21 [(3,x0,x3)] (by decide +kernel)
def p507 := prefixPool s21 [(3,x0,x3),(1,x45,x5)] (by decide +kernel)
def p508 := prefixPool s21 [(3,x0,x3),(1,x3,x5)] (by decide +kernel)
def p509 := prefixPool s21 [(3,x0,x3),(3,x45,x1)] (by decide +kernel)
def p510 := prefixPool s21 [(3,x1,x5),(1,x0,x3),(0,x9,x1)] (by decide +kernel)
def p511 := prefixPool s21 [(3,x3,x5)] (by decide +kernel)
def p512 := prefixPool s21 [(3,x3,x5),(3,x0,x1)] (by decide +kernel)
def p513 := prefixPool s22 [] (by decide +kernel)
def p514 := prefixPool s22 [(0,x1,x19)] (by decide +kernel)
def p515 := prefixPool s23 [] (by decide +kernel)
def p516 := prefixPool s24 [] (by decide +kernel)
def p517 := prefixPool s24 [(1,x0,x3)] (by decide +kernel)
def p518 := prefixPool s26 [] (by decide +kernel)
def p519 := prefixPool s40 [] (by decide +kernel)
def p520 := prefixPool s50 [] (by decide +kernel)
def p521 := prefixPool s54 [] (by decide +kernel)
def p522 := prefixPool s58 [] (by decide +kernel)
def p523 := prefixPool s62 [] (by decide +kernel)
def p524 := prefixPool s65 [] (by decide +kernel)
def p525 := prefixPool s66 [] (by decide +kernel)
def p526 := prefixPool s72 [] (by decide +kernel)
def p527 := prefixPool s76 [] (by decide +kernel)
def p528 := prefixPool s80 [] (by decide +kernel)
def p529 := prefixPool s84 [] (by decide +kernel)
def p530 := prefixPool s89 [] (by decide +kernel)
def p531 := prefixPool s90 [] (by decide +kernel)
def p532 := prefixPool s96 [] (by decide +kernel)
def p533 := prefixPool s100 [] (by decide +kernel)
def p534 := prefixPool s104 [] (by decide +kernel)
def p535 := prefixPool s116 [] (by decide +kernel)
def p536 := prefixPool s120 [] (by decide +kernel)
def p537 := prefixPool s120 [(0,x0,x19)] (by decide +kernel)
def p538 := prefixPool s121 [] (by decide +kernel)
def p539 := prefixPool s121 [(0,x0,x19)] (by decide +kernel)
def p540 := prefixPool s124 [] (by decide +kernel)
def p541 := prefixPool s125 [] (by decide +kernel)
def p542 := prefixPool s135 [] (by decide +kernel)
def p543 := prefixPool s139 [] (by decide +kernel)
def p544 := prefixPool s142 [] (by decide +kernel)
def p545 := prefixPool s145 [] (by decide +kernel)
def p546 := prefixPool s152 [] (by decide +kernel)
def p547 := prefixPool s152 [(2,x0,x3)] (by decide +kernel)
def p548 := prefixPool s158 [] (by decide +kernel)
def p549 := prefixPool s158 [(1,x0,x3)] (by decide +kernel)
def p550 := prefixPool s162 [] (by decide +kernel)
def p551 := prefixPool s170 [] (by decide +kernel)
def p552 := prefixPool s170 [(0,x3,x5)] (by decide +kernel)
def p553 := prefixPool s170 [(0,x3,x5),(1,x3,x5)] (by decide +kernel)
def p554 := prefixPool s170 [(1,x3,x5)] (by decide +kernel)
def p555 := prefixPool s170 [(2,x3,x5)] (by decide +kernel)
def p556 := prefixPool s170 [(2,x3,x5),(0,x3,x5)] (by decide +kernel)
def p557 := prefixPool s170 [(3,x3,x5)] (by decide +kernel)
def q0 := usePool p0
def q1 := usePool p1
def q2 := usePool p2
def q3 := usePool p3
def q4 := usePool p4
def q5 := usePool p5
def q6 := usePool p6
def q7 := usePool p8
def q8 := usePool p9
def q9 := usePool p10
def q10 := usePool p12
def q11 := usePool p13
def q12 := usePool p14
def q13 := usePool p15
def q14 := usePool p16
def q15 := usePool p17
def q16 := usePool p18
def q17 := usePool p19
def q18 := usePool p20
def q19 := usePool p21
def q20 := usePool p22
def q21 := usePool p23
def q22 := usePool p26
def q23 := usePool p27
def q24 := usePool p28
def q25 := usePool p29
def q26 := usePool p30
def q27 := usePool p31
def q28 := usePool p32
def q29 := usePool p33
def q30 := usePool p34
def q31 := usePool p35
def q32 := usePool p36
def q33 := usePool p38
def q34 := usePool p39
def q35 := usePool p40
def q36 := usePool p41
def q37 := usePool p42
def q38 := usePool p43
def q39 := usePool p44
def q40 := usePool p45
def q41 := usePool p46
def q42 := usePool p47
def q43 := usePool p48
def q44 := usePool p49
def q45 := usePool p50
def q46 := usePool p51
def q47 := usePool p52
def q48 := usePool p53
def q49 := usePool p54
def q50 := usePool p55
def q51 := usePool p56
def q52 := usePool p57
def q53 := usePool p58
def q54 := usePool p59
def q55 := usePool p61
def q56 := usePool p62
def q57 := usePool p63
def q58 := usePool p64
def q59 := usePool p65
def q60 := usePool p66
def q61 := usePool p67
def q62 := usePool p68
def q63 := usePool p71
def q64 := usePool p72
def q65 := usePool p73
def q66 := usePool p74
def q67 := usePool p75
def q68 := usePool p76
def q69 := usePool p77
def q70 := usePool p78
def q71 := usePool p79
def q72 := usePool p80
def q73 := usePool p81
def q74 := usePool p87
def q75 := usePool p88
def q76 := usePool p89
def q77 := usePool p90
def q78 := usePool p91
def q79 := usePool p92
def q80 := usePool p93
def q81 := usePool p94
def q82 := usePool p95
def q83 := usePool p98
def q84 := usePool p99
def q85 := usePool p100
def q86 := usePool p101
def q87 := usePool p102
def q88 := usePool p103
def q89 := usePool p104
def q90 := usePool p105
def q91 := usePool p106
def q92 := usePool p107
def q93 := usePool p108
def q94 := usePool p109
def q95 := usePool p110
def q96 := usePool p111
def q97 := usePool p112
def q98 := usePool p113
def q99 := usePool p114
def q100 := usePool p115
def q101 := usePool p116
def q102 := usePool p117
def q103 := usePool p118
def q104 := usePool p119
def q105 := usePool p120
def q106 := usePool p121
def q107 := usePool p122
def q108 := usePool p123
def q109 := usePool p124
def q110 := usePool p125
def q111 := usePool p126
def q112 := usePool p127
def q113 := usePool p128
def q114 := usePool p129
def q115 := usePool p130
def q116 := usePool p131
def q117 := usePool p132
def q118 := usePool p133
def q119 := usePool p134
def q120 := usePool p135
def q121 := usePool p136
def q122 := usePool p137
def q123 := usePool p138
def q124 := usePool p139
def q125 := usePool p140
def q126 := usePool p141
def q127 := usePool p142
def q128 := usePool p143
def q129 := usePool p144
def q130 := usePool p145
def q131 := usePool p146
def q132 := usePool p147
def q133 := usePool p148
def q134 := usePool p149
def q135 := usePool p150
def q136 := usePool p151
def q137 := usePool p152
def q138 := usePool p153
def q139 := usePool p154
def q140 := usePool p155
def q141 := usePool p156
def q142 := usePool p157
def q143 := usePool p158
def q144 := usePool p159
def q145 := usePool p160
def q146 := usePool p161
def q147 := joinPools p162 p84
def q148 := usePool p163
def q149 := usePool p164
def q150 := usePool p165
def q151 := usePool p166
def q152 := usePool p167
def q153 := usePool p168
def q154 := usePool p169
def q155 := usePool p170
def q156 := usePool p171
def q157 := usePool p172
def q158 := usePool p173
def q159 := usePool p174
def q160 := usePool p175
def q161 := usePool p176
def q162 := usePool p177
def q163 := usePool p178
def q164 := usePool p179
def q165 := usePool p180
def q166 := usePool p181
def q167 := usePool p182
def q168 := usePool p183
def q169 := usePool p184
def q170 := usePool p185
def q171 := usePool p186
def q172 := usePool p187
def q173 := usePool p188
def q174 := usePool p189
def q175 := usePool p190
def q176 := usePool p191
def q177 := usePool p192
def q178 := usePool p193
def q179 := usePool p194
def q180 := usePool p195
def q181 := usePool p196
def q182 := usePool p197
def q183 := usePool p198
def q184 := joinPools p199 p86
def q185 := usePool p200
def q186 := usePool p201
def q187 := usePool p202
def q188 := usePool p203
def q189 := usePool p204
def q190 := usePool p205
def q191 := usePool p206
def q192 := usePool p207
def q193 := usePool p208
def q194 := usePool p209
def q195 := usePool p210
def q196 := usePool p211
def q197 := usePool p212
def q198 := usePool p213
def q199 := usePool p214
def q200 := usePool p215
def q201 := usePool p216
def q202 := usePool p217
def q203 := usePool p218
def q204 := usePool p219
def q205 := usePool p220
def q206 := usePool p221
def q207 := usePool p222
def q208 := usePool p223
def q209 := usePool p224
def q210 := usePool p225
def q211 := usePool p226
def q212 := usePool p227
def q213 := usePool p228
def q214 := usePool p229
def q215 := usePool p230
def q216 := usePool p231
def q217 := usePool p232
def q218 := usePool p233
def q219 := usePool p234
def q220 := usePool p235
def q221 := usePool p236
def q222 := usePool p237
def q223 := usePool p238
def q224 := usePool p239
def q225 := usePool p240
def q226 := usePool p241
def q227 := usePool p242
def q228 := usePool p243
def q229 := usePool p244
def q230 := usePool p245
def q231 := usePool p246
def q232 := usePool p247
def q233 := usePool p248
def q234 := usePool p249
def q235 := usePool p250
def q236 := usePool p251
def q237 := usePool p252
def q238 := usePool p253
def q239 := usePool p254
def q240 := usePool p255
def q241 := usePool p256
def q242 := usePool p257
def q243 := usePool p258
def q244 := usePool p259
def q245 := usePool p260
def q246 := usePool p261
def q247 := usePool p262
def q248 := usePool p263
def q249 := usePool p264
def q250 := usePool p265
def q251 := usePool p266
def q252 := usePool p267
def q253 := usePool p268
def q254 := usePool p269
def q255 := usePool p270
def q256 := usePool p271
def q257 := usePool p272
def q258 := usePool p273
def q259 := usePool p274
def q260 := usePool p275
def q261 := usePool p276
def q262 := usePool p277
def q263 := usePool p278
def q264 := usePool p279
def q265 := usePool p280
def q266 := usePool p281
def q267 := usePool p282
def q268 := usePool p283
def q269 := usePool p284
def q270 := usePool p285
def q271 := usePool p286
def q272 := usePool p287
def q273 := usePool p288
def q274 := usePool p289
def q275 := usePool p290
def q276 := usePool p291
def q277 := usePool p292
def q278 := usePool p293
def q279 := usePool p294
def q280 := usePool p295
def q281 := usePool p296
def q282 := usePool p297
def q283 := usePool p298
def q284 := usePool p299
def q285 := usePool p300
def q286 := usePool p301
def q287 := usePool p302
def q288 := usePool p303
def q289 := usePool p304
def q290 := usePool p305
def q291 := usePool p306
def q292 := usePool p308
def q293 := usePool p309
def q294 := joinPools p309 p4
def q295 := joinPools p309 p68
def q296 := usePool p310
def q297 := usePool p311
def q298 := usePool p312
def q299 := usePool p313
def q300 := usePool p314
def q301 := joinPools p314 p8
def q302 := joinPools p314 p23
def q303 := usePool p315
def q304 := joinPools p315 p24
def q305 := joinPools p316 p25
def q306 := joinPools p317 p307
def q307 := usePool p318
def q308 := usePool p319
def q309 := joinPools p319 p410
def q310 := joinPools p319 p426
def q311 := usePool p320
def q312 := joinPools p321 p485
def q313 := joinPools p321 p510
def q314 := joinPools p322 p416
def q315 := joinPools p322 p476
def q316 := usePool p323
def q317 := joinPools p324 p427
def q318 := usePool p325
def q319 := usePool p326
def q320 := usePool p327
def q321 := usePool p328
def q322 := joinPools p328 p7
def q323 := joinPools p328 p70
def q324 := usePool p329
def q325 := usePool p330
def q326 := joinPools p330 p417
def q327 := joinPools p330 p477
def q328 := joinPools p330 p489
def q329 := usePool p331
def q330 := usePool p332
def q331 := usePool p333
def q332 := usePool p334
def q333 := usePool p335
def q334 := usePool p336
def q335 := joinPools p336 p11
def q336 := joinPools p336 p37
def q337 := joinPools p336 p409
def q338 := joinPools p336 p454
def q339 := usePool p337
def q340 := usePool p338
def q341 := joinPools p338 p412
def q342 := usePool p339
def q343 := joinPools p339 p494
def q344 := joinPools p339 p504
def q345 := usePool p340
def q346 := usePool p341
def q347 := joinPools p341 p453
def q348 := usePool p342
def q349 := joinPools p342 p10
def q350 := joinPools p342 p471
def q351 := usePool p343
def q352 := joinPools p343 p502
def q353 := joinPools p343 p503
def q354 := usePool p344
def q355 := joinPools p344 p415
def q356 := joinPools p344 p454
def q357 := joinPools p344 p475
def q358 := usePool p345
def q359 := usePool p346
def q360 := usePool p347
def q361 := joinPools p347 p468
def q362 := joinPools p347 p512
def q363 := usePool p348
def q364 := joinPools p348 p60
def q365 := usePool p349
def q366 := usePool p350
def q367 := usePool p351
def q368 := usePool p352
def q369 := usePool p353
def q370 := usePool p354
def q371 := usePool p355
def q372 := usePool p356
def q373 := usePool p357
def q374 := joinPools p357 p69
def q375 := usePool p358
def q376 := usePool p359
def q377 := usePool p360
def q378 := usePool p361
def q379 := usePool p362
def q380 := usePool p363
def q381 := usePool p364
def q382 := usePool p365
def q383 := usePool p366
def q384 := usePool p367
def q385 := usePool p368
def q386 := usePool p369
def q387 := usePool p370
def q388 := usePool p371
def q389 := joinPools p372 p83
def q390 := joinPools p373 p82
def q391 := usePool p374
def q392 := usePool p375
def q393 := usePool p376
def q394 := joinPools p377 p83
def q395 := usePool p378
def q396 := usePool p379
def q397 := usePool p380
def q398 := usePool p381
def q399 := usePool p382
def q400 := usePool p383
def q401 := usePool p384
def q402 := usePool p385
def q403 := usePool p386
def q404 := usePool p387
def q405 := usePool p388
def q406 := usePool p389
def q407 := usePool p390
def q408 := usePool p391
def q409 := usePool p392
def q410 := usePool p393
def q411 := usePool p394
def q412 := usePool p395
def q413 := usePool p396
def q414 := usePool p397
def q415 := usePool p398
def q416 := usePool p399
def q417 := usePool p400
def q418 := usePool p401
def q419 := usePool p402
def q420 := usePool p403
def q421 := usePool p404
def q422 := usePool p405
def q423 := usePool p406
def q424 := usePool p407
def q425 := usePool p408
def q426 := usePool p409
def q427 := usePool p410
def q428 := usePool p411
def q429 := usePool p412
def q430 := usePool p413
def q431 := usePool p414
def q432 := usePool p415
def q433 := usePool p417
def q434 := usePool p418
def q435 := usePool p419
def q436 := usePool p420
def q437 := usePool p421
def q438 := usePool p422
def q439 := usePool p423
def q440 := usePool p424
def q441 := usePool p425
def q442 := usePool p426
def q443 := usePool p427
def q444 := usePool p428
def q445 := usePool p429
def q446 := usePool p430
def q447 := usePool p431
def q448 := usePool p432
def q449 := usePool p433
def q450 := usePool p434
def q451 := usePool p435
def q452 := usePool p436
def q453 := usePool p437
def q454 := usePool p438
def q455 := joinPools p438 p85
def q456 := usePool p439
def q457 := usePool p440
def q458 := usePool p441
def q459 := usePool p442
def q460 := usePool p443
def q461 := usePool p444
def q462 := usePool p445
def q463 := usePool p446
def q464 := usePool p447
def q465 := usePool p448
def q466 := usePool p449
def q467 := usePool p450
def q468 := usePool p451
def q469 := usePool p452
def q470 := usePool p454
def q471 := usePool p455
def q472 := usePool p456
def q473 := usePool p457
def q474 := usePool p458
def q475 := usePool p459
def q476 := usePool p460
def q477 := usePool p461
def q478 := usePool p462
def q479 := usePool p463
def q480 := usePool p464
def q481 := usePool p465
def q482 := usePool p466
def q483 := usePool p467
def q484 := usePool p469
def q485 := usePool p470
def q486 := usePool p471
def q487 := usePool p472
def q488 := usePool p473
def q489 := usePool p474
def q490 := usePool p478
def q491 := usePool p479
def q492 := usePool p480
def q493 := usePool p481
def q494 := usePool p482
def q495 := usePool p483
def q496 := usePool p484
def q497 := usePool p486
def q498 := usePool p487
def q499 := usePool p488
def q500 := usePool p490
def q501 := usePool p491
def q502 := usePool p492
def q503 := usePool p493
def q504 := usePool p495
def q505 := usePool p496
def q506 := usePool p497
def q507 := usePool p498
def q508 := usePool p499
def q509 := usePool p500
def q510 := usePool p501
def q511 := usePool p505
def q512 := usePool p506
def q513 := usePool p507
def q514 := usePool p508
def q515 := usePool p509
def q516 := usePool p511
def q517 := usePool p513
def q518 := usePool p514
def q519 := usePool p515
def q520 := usePool p516
def q521 := usePool p517
def q522 := usePool p518
def q523 := usePool p519
def q524 := usePool p520
def q525 := usePool p521
def q526 := usePool p522
def q527 := usePool p523
def q528 := usePool p524
def q529 := usePool p525
def q530 := usePool p526
def q531 := usePool p527
def q532 := usePool p528
def q533 := usePool p529
def q534 := usePool p530
def q535 := usePool p531
def q536 := usePool p532
def q537 := usePool p533
def q538 := usePool p534
def q539 := usePool p535
def q540 := usePool p536
def q541 := joinPools p536 p81
def q542 := usePool p537
def q543 := usePool p538
def q544 := joinPools p538 p93
def q545 := usePool p539
def q546 := usePool p540
def q547 := usePool p541
def q548 := usePool p542
def q549 := usePool p543
def q550 := usePool p544
def q551 := usePool p545
def q552 := usePool p546
def q553 := joinPools p547 p96
def q554 := joinPools p547 p97
def q555 := usePool p548
def q556 := usePool p549
def q557 := usePool p550
def q558 := usePool p551
def q559 := usePool p552
def q560 := usePool p553
def q561 := usePool p554
def q562 := usePool p555
def q563 := usePool p556
def q564 := usePool p557
def cc (k : Nat) (w : List (Observed (asRow Pos) (asRow Neg))) (ps : List (ChosenPool R T))
    (ns : List (Closed T (k-1))) (h : stateCheck k w (fun _ => (ps,ns)) = true) : Closed T k :=
  closeState (raw := R) correctPairs k w (fun _ => (ps,ns)) h
def n0 := cc 8 [w0,w1,w7,w3,w8,w4,w5] [q2,q94,q164,q208,q300] [] (by decide +kernel)
def n1 := cc 9 [w0,w1,w2,w7,w3,w4,w5] [q0,q133,q134,q138,q187,q229,q300] [n0] (by decide +kernel)
def n2 := cc 8 [w9,w0,w1,w2,w3,w4,w5] [q94,q164,q208,q279] [] (by decide +kernel)
def n3 := cc 9 [w6,w0,w1,w2,w3,w8,w4,w5] [q1,q94,q164,q208,q229,q293] [n2,n0] (by decide +kernel)
def n4 := cc 10 [w6,w0,w1,w2,w3,w4,w5] [q0,q86,q138,q187,q229,q293] [n3,n1] (by decide +kernel)
def n5 := cc 10 [w0,w1,w10,w2,w3,w4,w5] [q86,q229,q293,q385,q400] [] (by decide +kernel)
def n6 := cc 9 [w0,w1,w2,w12,w4,w5] [q0,q86,q138,q187] [] (by decide +kernel)
def n7 := cc 9 [w0,w1,w13,w2,w4,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n8 := cc 10 [w11,w0,w1,w2,w3,w4,w5] [q86,q138,q187,q229,q293] [n7,n6] (by decide +kernel)
def n9 := cc 8 [w15,w0,w16,w2,w3,w4,w5] [q86,q133,q229,q540,q543] [] (by decide +kernel)
def n10 := cc 8 [w0,w1,w2,w3,w4,w17,w5] [q73,q80,q119,q214,q267,q316,q471] [] (by decide +kernel)
def n11 := cc 8 [w18,w0,w1,w2,w3,w4,w5] [q73,q80,q107,q169,q213,q251,q311,q511] [] (by decide +kernel)
def n12 := cc 8 [w15,w0,w1,w2,w3,w4,w5,w19] [q73,q114,q213,q261,q300,q354,q471,q511,q517,q540] [] (by decide +kernel)
def v0 : Closed T 8 := rotateClosed n11 auto1 auto1ok
def v1 : Closed T 8 := rotateClosed n10 auto1 auto1ok
def n13 := cc 9 [w15,w0,w1,w2,w3,w4,w5] [q0,q86,q168,q213,q229,q291,q300,q540,q543] [n11,v0,n9,n12,n10,v1] (by decide +kernel)
def n14 := cc 8 [w0,w1,w2,w21,w3,w4,w5] [q0,q129,q206,q293,q419] [] (by decide +kernel)
def n15 := cc 8 [w0,w1,w2,w3,w4,w22,w5] [q73,q132,q207,q253,q333,q472,q540] [] (by decide +kernel)
def n16 := cc 8 [w23,w0,w1,w2,w3,w4,w5] [q114,q216,q248,q325,q472,q541] [] (by decide +kernel)
def n17 := cc 7 [w20,w0,w1,w2,w3,w24,w19] [q35,q65,q83,q102,q170,q252,q417] [] (by decide +kernel)
def n18 := cc 8 [w20,w0,w1,w2,w3,w4,w24,w5] [q33,q64,q73,q209,q251,q330,q334,q417,q540] [n17] (by decide +kernel)
def n19 := cc 8 [w20,w0,w1,w2,w3,w4,w19] [q80,q114,q170,q332,q419,q510] [n17] (by decide +kernel)
def n20 := cc 9 [w20,w0,w1,w2,w3,w4,w5] [q86,q138,q187,q251,q330,q400,q510,q523,q540] [n16,n11,n18,n19,n14,n15] (by decide +kernel)
def n21 := cc 8 [w26,w14,w0,w2,w3,w4,w5] [q107,q213,q293,q524] [] (by decide +kernel)
def n22 := cc 8 [w25,w14,w0,w2,w3,w4,w5,w19] [q114,q261,q293,q463,q507,q524,q525] [] (by decide +kernel)
def v2 : Closed T 8 := rotateClosed n21 auto1 auto1ok
def n23 := cc 9 [w25,w14,w0,w2,w3,w4,w5] [q86,q168,q213,q229,q291,q293] [n21,v2,n22] (by decide +kernel)
def n24 := cc 8 [w14,w0,w2,w28,w3,w4,w5] [q94,q293,q524,q525] [] (by decide +kernel)
def n25 := cc 8 [w14,w0,w2,w3,w4,w29,w5] [q110,q134,q144,q293,q529] [] (by decide +kernel)
def n26 := cc 7 [w14,w0,w27,w2,w3,w4,w30,w19] [q63,q108,q229,q352,q353,q542] [] (by decide +kernel)
def n27 := cc 6 [w14,w32,w27,w2,w3,w4,w5] [q78,q84,q134] [] (by decide +kernel)
def n28 := cc 7 [w14,w0,w27,w2,w3,w4,w5,w31] [q62,q78,q103,q134,q293,q344,q542] [n27] (by decide +kernel)
def n29 := cc 7 [w33,w14,w0,w27,w2,w3,w4,w5] [q105,q347,q423] [] (by decide +kernel)
def v3 : Closed T 7 := rotateClosed n26 auto1 auto1ok
def n30 := cc 8 [w14,w0,w27,w2,w3,w4,w24,w5] [q98,q134,q191,q229,q291,q334,q338,q418,q470,q528] [n29,n28,v3] (by decide +kernel)
def n31 := cc 6 [w14,w0,w35,w2,w3,w4,w5] [] [] (by decide +kernel)
def n32 := cc 7 [w34,w14,w0,w27,w2,w3,w4,w5] [q62,q117,q293,q361,q362] [n31] (by decide +kernel)
def n33 := cc 8 [w14,w0,w27,w2,w3,w4,w5,w19] [q114,q191,q229,q291,q354,q356,q470,q518,q524,q528] [n32,n28,n26,v3] (by decide +kernel)
def v4 : Closed T 8 := rotateClosed n30 auto1 auto1ok
def v5 : Closed T 8 := rotateClosed n25 auto1 auto1ok
def n34 := cc 9 [w14,w0,w27,w2,w3,w4,w5] [q86,q144,q191,q229,q293] [n30,v4,n33,n24,n25,v5] (by decide +kernel)
def n35 := cc 8 [w37,w14,w0,w2,w3,w4,w5] [q114,q134,q216,q354,q385,q466,q549] [] (by decide +kernel)
def n36 := cc 7 [w36,w14,w0,w2,w3,w24,w19] [q60,q102,q261,q407,q517,q525] [] (by decide +kernel)
def n37 := cc 8 [w36,w14,w0,w2,w3,w4,w24,w5] [q59,q78,q98,q170,q229,q334,q407,q549] [n36] (by decide +kernel)
def n38 := cc 8 [w36,w14,w0,w2,w3,w4,w19] [q114,q354,q400,q510,q528] [n36] (by decide +kernel)
def n39 := cc 9 [w36,w14,w0,w2,w3,w4,w5] [q86,q170,q229,q293,q400,q510] [n35,n21,n37,n38] (by decide +kernel)
def n40 := cc 8 [w38,w0,w1,w2,w3,w4,w5] [q13,q279,q510,q540] [] (by decide +kernel)
def n41 := cc 9 [w14,w0,w1,w2,w3,w8,w4,w5] [q94,q229,q295,q470,q510] [n40] (by decide +kernel)
def n42 := cc 8 [w39,w0,w1,w2,w3,w4,w5] [q98,q139,q291,q543] [] (by decide +kernel)
def v6 : Closed T 7 := rotateClosed n17 auto1 auto1ok
def v7 : Closed T 7 := rotateClosed n36 auto1 auto1ok
def n43 := cc 8 [w14,w0,w1,w2,w3,w4,w30,w19] [q84,q108,q261,q351,q510,q517,q524,q540] [v6,v7,n26] (by decide +kernel)
def n44 := cc 6 [w40,w32,w1,w2,w3,w4,w5] [q73,q80,q134] [] (by decide +kernel)
def n45 := cc 7 [w14,w32,w1,w2,w3,w4,w5] [q103,q134,q165,q209] [n44,n27] (by decide +kernel)
def n46 := cc 8 [w14,w0,w1,w2,w3,w4,w5,w31] [q36,q62,q103,q134,q165,q209,q342,q540] [n45,n28] (by decide +kernel)
def n47 := cc 8 [w33,w14,w0,w1,w2,w3,w4,w5] [q40,q80,q105,q134,q172,q209,q275,q291,q346,q423] [n29] (by decide +kernel)
def v8 : Closed T 8 := rotateClosed n43 auto1 auto1ok
def n48 := cc 9 [w14,w0,w1,w2,w3,w4,w24,w5] [q98,q138,q187,q229,q334,q417,q470,q525] [v0,v2,n18,n37,n47,n42,n30,n46,v8] (by decide +kernel)
def n49 := cc 8 [w42,w0,w1,w2,w3,w4,w5] [q110,q134,q229,q510,q540] [] (by decide +kernel)
def n50 := cc 8 [w43,w14,w0,w1,w2,w3,w4,w5] [q112,q134,q177,q510,q540] [] (by decide +kernel)
def n51 := cc 9 [w14,w0,w1,w2,w3,w4,w41,w5] [q110,q138,q229,q291,q295,q510] [n50,n49] (by decide +kernel)
def n52 := cc 8 [w44,w0,w1,w2,w3,w4,w5] [q134,q151,q198,q229,q291] [] (by decide +kernel)
def n53 := cc 8 [w34,w14,w0,w1,w2,w3,w4,w5] [q48,q117,q134,q181,q225,q291,q360] [n32] (by decide +kernel)
def v9 : Closed T 8 := rotateClosed n19 auto1 auto1ok
def v10 : Closed T 8 := rotateClosed n38 auto1 auto1ok
def n54 := cc 9 [w14,w0,w1,w2,w3,w4,w5,w19] [q114,q138,q187,q261,q354,q470,q510,q528,q536] [n16,n35,n19,v9,n38,v10,n12,n22,n53,n52,n33,n46,n43,v8] (by decide +kernel)
def v11 : Closed T 9 := rotateClosed n20 auto1 auto1ok
def v12 : Closed T 9 := rotateClosed n39 auto1 auto1ok
def v13 : Closed T 9 := rotateClosed n48 auto1 auto1ok
def v14 : Closed T 9 := rotateClosed n51 auto1 auto1ok
def n55 := cc 10 [w14,w0,w1,w2,w3,w4,w5] [q0,q86,q138,q187,q229,q293] [n20,v11,n39,v12,n13,n23,n34,n41,n48,v13,n51,v14,n54] (by decide +kernel)
def n56 := cc 9 [w0,w46,w2,w3,w4,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n57 := cc 9 [w47,w0,w2,w3,w4,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n58 := cc 9 [w0,w1,w2,w48,w4,w5] [q0,q86,q138,q187] [] (by decide +kernel)
def n59 := cc 9 [w49,w0,w1,w2,w4,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n60 := cc 9 [w0,w1,w2,w3,w4,w50] [q86,q138,q187,q229] [] (by decide +kernel)
def n61 := cc 9 [w51,w0,w1,w2,w3,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def v15 : Closed T 9 := rotateClosed n61 auto1 auto1ok
def v16 : Closed T 9 := rotateClosed n60 auto1 auto1ok
def n62 := cc 10 [w45,w0,w1,w2,w3,w4,w5] [q0,q86,q138,q187,q229,q293] [n57,n59,n61,v15,n60,v16,n58,n56] (by decide +kernel)
def n63 := cc 8 [w53,w0,w1,w54,w3,w4,w5] [q125,q177,q222,q239,q551] [] (by decide +kernel)
def n64 := cc 9 [w0,w1,w2,w54,w3,w52,w4,w5] [q20,q86,q133,q134,q138,q187,q229,q239,q293] [n63] (by decide +kernel)
def n65 := cc 8 [w0,w1,w56,w54,w3,w4,w5] [q164,q208,q300,q546] [] (by decide +kernel)
def n66 := cc 9 [w55,w0,w1,w2,w54,w3,w4,w5] [q0,q134,q138,q187,q229,q300,q546] [n65] (by decide +kernel)
def n67 := cc 8 [w0,w1,w2,w3,w4,w57,w5] [q73,q80,q139,q189,q245,q308,q442] [] (by decide +kernel)
def n68 := cc 8 [w58,w0,w1,w2,w3,w4,w5] [q73,q80,q121,q142,q269,q318,q496] [] (by decide +kernel)
def n69 := cc 8 [w0,w16,w1,w2,w3,w4,w5,w19] [q73,q80,q188,q261,q517,q533] [] (by decide +kernel)
def v17 : Closed T 8 := rotateClosed n68 auto1 auto1ok
def v18 : Closed T 8 := rotateClosed n67 auto1 auto1ok
def n70 := cc 9 [w0,w16,w1,w2,w3,w4,w5] [q0,q86,q138,q188,q229,q300,q533,q534] [n68,v17,n9,n69,n67,v18] (by decide +kernel)
def n71 := cc 8 [w0,w1,w2,w54,w3,w4,w57,w5] [q20,q133,q300,q419,q529] [] (by decide +kernel)
def n72 := cc 8 [w0,w16,w1,w54,w3,w4,w24,w5] [q23,q133,q139,q307,q421] [] (by decide +kernel)
def n73 := cc 8 [w0,w16,w1,w2,w3,w4,w59,w5] [q21,q25,q98,q133,q176,q308,q421] [] (by decide +kernel)
def n74 := cc 7 [w60,w0,w1,w2,w54,w3,w4,w5] [q21,q27] [] (by decide +kernel)
def n75 := cc 8 [w0,w16,w1,w2,w54,w3,w4,w41,w5] [q21,q133,q134,q138,q300,q302,q529,q540] [n74] (by decide +kernel)
def n76 := cc 7 [w61,w0,w1,w2,w54,w3,w4,w5] [q103,q117] [] (by decide +kernel)
def n77 := cc 6 [w16,w63,w2,w54,w3,w4,w5] [] [] (by decide +kernel)
def n78 := cc 7 [w0,w16,w62,w2,w54,w3,w4,w5] [q114,q134,q549,q550] [n77] (by decide +kernel)
def n79 := cc 8 [w0,w16,w1,w2,w54,w3,w4,w5,w19] [q114,q133,q419,q421,q528,q529] [n76,n78] (by decide +kernel)
def v19 : Closed T 8 := rotateClosed n75 auto1 auto1ok
def v20 : Closed T 8 := rotateClosed n73 auto1 auto1ok
def v21 : Closed T 8 := rotateClosed n72 auto1 auto1ok
def v22 : Closed T 8 := rotateClosed n71 auto1 auto1ok
def n80 := cc 9 [w0,w16,w1,w2,w54,w3,w4,w5] [q20,q86,q133,q139,q188,q291,q300] [n9,n75,v19,n79,n73,v20,n72,v21,n71,v22] (by decide +kernel)
def n81 := cc 9 [w15,w0,w1,w2,w54,w3,w4,w5] [q20,q86,q229,q291,q300,q419,q421] [n9] (by decide +kernel)
def n82 := cc 6 [w1,w64,w54,w3,w4,w65,w30] [q136,q239] [] (by decide +kernel)
def n83 := cc 6 [w67,w1,w64,w54,w3,w4,w5] [] [] (by decide +kernel)
def v23 : Closed T 6 := rotateClosed n82 auto1 auto1ok
def n84 := cc 7 [w1,w64,w2,w54,w3,w4,w66,w5] [q144,q242,q319,q320] [n83,v23] (by decide +kernel)
def n85 := cc 6 [w1,w64,w54,w3,w4,w30,w19] [] [] (by decide +kernel)
def n86 := cc 6 [w1,w64,w54,w3,w4,w5,w31] [q136] [] (by decide +kernel)
def n87 := cc 6 [w33,w1,w64,w54,w3,w4,w5] [] [] (by decide +kernel)
def v24 : Closed T 6 := rotateClosed n85 auto1 auto1ok
def n88 := cc 7 [w1,w64,w54,w3,w4,w24,w5] [q136,q144,q417,q522] [n87,n86,v23,v24] (by decide +kernel)
def n89 := cc 6 [w68,w64,w2,w3,w4,w59,w5] [q308,q317,q443] [] (by decide +kernel)
def n90 := cc 6 [w1,w64,w2,w3,w4,w69,w19] [q312] [] (by decide +kernel)
def n91 := cc 6 [w1,w64,w2,w3,w4,w5,w70] [q147,q293] [] (by decide +kernel)
def n92 := cc 6 [w71,w1,w64,w2,w3,w4,w5] [] [] (by decide +kernel)
def v25 : Closed T 6 := rotateClosed n90 auto1 auto1ok
def n93 := cc 7 [w1,w64,w2,w3,w4,w59,w5] [q144,q308,q417,q439,q522,q540] [n92,n89,n91,v25] (by decide +kernel)
def n94 := cc 6 [w68,w64,w2,w54,w3,w4,w5] [q308,q317,q443] [] (by decide +kernel)
def n95 := cc 7 [w1,w64,w2,w54,w3,w4,w59,w5] [q15,q126,q244,q300,q522] [n94] (by decide +kernel)
def n96 := cc 6 [w1,w64,w2,w3,w4,w73,w5] [] [] (by decide +kernel)
def n97 := cc 7 [w72,w1,w64,w2,w3,w4,w5] [q107,q297,q522] [n96] (by decide +kernel)
def n98 := cc 7 [w1,w64,w2,w54,w3,w4,w5,w19] [q144,q354,q522] [n91,n90,v25,n86,n85,v24] (by decide +kernel)
def v26 : Closed T 7 := rotateClosed n97 auto1 auto1ok
def v27 : Closed T 7 := rotateClosed n84 auto1 auto1ok
def v28 : Closed T 7 := rotateClosed n95 auto1 auto1ok
def v29 : Closed T 7 := rotateClosed n93 auto1 auto1ok
def v30 : Closed T 7 := rotateClosed n88 auto1 auto1ok
def n99 := cc 8 [w1,w64,w2,w54,w3,w4,w5] [q136,q144,q191,q239,q300,q522] [n97,v26,n84,v27,n95,v28,n98,n93,v29,n88,v30] (by decide +kernel)
def n100 := cc 8 [w0,w1,w54,w28,w3,w4,w5] [q134,q300,q419,q421] [] (by decide +kernel)
def n101 := cc 8 [w0,w1,w2,w74,w3,w4,w5] [q80,q94,q187,q239,q300,q419] [] (by decide +kernel)
def n102 := cc 6 [w75,w0,w1,w3,w4,w30,w19] [q133] [] (by decide +kernel)
def n103 := cc 6 [w75,w0,w1,w3,w4,w5,w31] [] [] (by decide +kernel)
def n104 := cc 6 [w33,w75,w0,w1,w3,w4,w5] [] [] (by decide +kernel)
def v31 : Closed T 6 := rotateClosed n102 auto1 auto1ok
def n105 := cc 7 [w75,w0,w1,w3,w4,w24,w5] [q133,q140,q149] [n104,n103,v31] (by decide +kernel)
def n106 := cc 6 [w75,w0,w62,w2,w3,w4,w5] [q306] [] (by decide +kernel)
def n107 := cc 7 [w75,w0,w1,w2,w3,w4,w5,w19] [q27,q73,q80,q149,q265,q300,q517] [n106,n103,n102,v31] (by decide +kernel)
def v32 : Closed T 7 := rotateClosed n105 auto1 auto1ok
def n108 := cc 8 [w75,w0,w1,w2,w3,w4,w5] [q73,q80,q133,q149,q196,q300] [n107,n105,v32] (by decide +kernel)
def n109 := cc 8 [w0,w1,w2,w54,w3,w4,w29,w5] [q133,q134,q144,q254,q300,q529] [] (by decide +kernel)
def n110 := cc 6 [w76,w0,w1,w54,w3,w5,w19] [] [] (by decide +kernel)
def n111 := cc 7 [w76,w0,w1,w54,w3,w4,w5] [q81,q87,q104,q417] [n110] (by decide +kernel)
def n112 := cc 6 [w77,w0,w1,w54,w3,w4,w30] [q133] [] (by decide +kernel)
def v33 : Closed T 6 := rotateClosed n110 auto1 auto1ok
def n113 := cc 7 [w0,w27,w1,w54,w3,w4,w30,w19] [q108,q135,q165,q522,q529] [n102,v33,n112,n85] (by decide +kernel)
def n114 := cc 6 [w78,w0,w1,w54,w3,w4,w5] [q86] [] (by decide +kernel)
def n115 := cc 7 [w0,w27,w1,w54,w3,w4,w5,w31] [q74,q81,q103,q134,q165,q209] [n103,n114,n86] (by decide +kernel)
def n116 := cc 7 [w33,w0,w27,w1,w54,w3,w4,w5] [q81,q105,q172,q421,q521] [n104,n87] (by decide +kernel)
def v34 : Closed T 7 := rotateClosed n113 auto1 auto1ok
def n117 := cc 8 [w0,w27,w1,w54,w3,w4,w24,w5] [q98,q134,q144,q307,q522,q528,q529,q531,q537] [n116,n105,n111,n115,v34,n88] (by decide +kernel)
def n118 := cc 6 [w79,w0,w1,w2,w3,w5,w19] [q187] [] (by decide +kernel)
def n119 := cc 7 [w79,w0,w1,w2,w3,w4,w5] [q4,q80,q104,q149,q187] [n118] (by decide +kernel)
def n120 := cc 7 [w79,w0,w1,w2,w3,w4,w59,w5] [q73,q100,q138,q417] [] (by decide +kernel)
def n121 := cc 7 [w0,w27,w68,w2,w3,w4,w59,w5] [q73,q134,q308,q442,q522] [n89] (by decide +kernel)
def n122 := cc 6 [w77,w0,w1,w2,w3,w4,w69] [q313] [] (by decide +kernel)
def v35 : Closed T 6 := rotateClosed n118 auto1 auto1ok
def n123 := cc 7 [w0,w27,w1,w2,w3,w4,w69,w19] [q135,q144,q165,q252,q292,q557] [v35,n122,n90] (by decide +kernel)
def n124 := cc 5 [w80,w0,w2,w81,w4,w5] [q548] [] (by decide +kernel)
def n125 := cc 6 [w80,w0,w1,w2,w3,w4,w5] [q0,q86] [n124] (by decide +kernel)
def n126 := cc 7 [w0,w27,w1,w2,w3,w4,w5,w70] [q0,q73,q80,q134,q165,q209,q248,q293,q389] [n125,n91] (by decide +kernel)
def n127 := cc 7 [w71,w0,w27,w1,w2,w3,w4,w5] [q73,q80,q105,q172,q249,q421] [n92] (by decide +kernel)
def v36 : Closed T 7 := rotateClosed n123 auto1 auto1ok
def n128 := cc 8 [w0,w27,w1,w2,w3,w4,w59,w5] [q73,q134,q144,q191,q209,q245,q291,q308,q441,q522,q528,q531] [n127,n120,n119,n121,n126,v36,n93] (by decide +kernel)
def n129 := cc 7 [w79,w0,w1,w2,w54,w3,w4,w5] [q21,q27,q97,q131,q244] [] (by decide +kernel)
def n130 := cc 7 [w0,w27,w68,w2,w54,w3,w4,w5] [q20,q134,q310,q522] [n94] (by decide +kernel)
def n131 := cc 8 [w0,w27,w1,w2,w54,w3,w4,w59,w5] [q20,q134,q144,q281,q300,q522,q529] [n129,n130,n95] (by decide +kernel)
def n132 := cc 7 [w0,w27,w1,w2,w3,w4,w73,w5] [q73,q122,q271,q419,q519] [n96] (by decide +kernel)
def n133 := cc 8 [w72,w0,w27,w1,w2,w3,w4,w5] [q144,q172,q191,q318,q421,q522,q529] [n97,n132] (by decide +kernel)
def v37 : Closed T 6 := rotateClosed n122 auto1 auto1ok
def v38 : Closed T 6 := rotateClosed n112 auto1 auto1ok
def n134 := cc 7 [w77,w0,w1,w2,w54,w3,w4,w5] [q47,q133,q134,q150,q197,q354] [n122,v37,n112,v38] (by decide +kernel)
def n135 := cc 6 [w27,w63,w2,w54,w3,w4,w5] [q306,q433] [] (by decide +kernel)
def n136 := cc 7 [w0,w27,w62,w2,w54,w3,w4,w5] [q20,q44,q314,q315,q354] [n106,n135] (by decide +kernel)
def n137 := cc 8 [w0,w27,w1,w2,w54,w3,w4,w5,w19] [q20,q43,q191,q261,q300,q354,q419,q522,q528,q529,q536] [n107,n134,n136,n126,n123,v36,n115,n113,v34,n98] (by decide +kernel)
def v39 : Closed T 8 := rotateClosed n133 auto1 auto1ok
def v40 : Closed T 8 := rotateClosed n131 auto1 auto1ok
def v41 : Closed T 8 := rotateClosed n128 auto1 auto1ok
def v42 : Closed T 8 := rotateClosed n117 auto1 auto1ok
def v43 : Closed T 8 := rotateClosed n109 auto1 auto1ok
def n138 := cc 9 [w0,w27,w1,w2,w54,w3,w4,w5] [q0,q86,q134,q144,q191,q229,q300,q522] [n133,v39,n108,n131,v40,n137,n128,v41,n117,v42,n109,v43,n101,n100,n99] (by decide +kernel)
def n139 := cc 9 [w82,w0,w1,w2,w54,w3,w4,w5] [q86,q229,q300,q441,q495] [] (by decide +kernel)
def n140 := cc 8 [w37,w0,w1,w2,w54,w3,w4,w5] [q20,q55,q133,q134,q216,q261,q300,q354,q388,q549] [] (by decide +kernel)
def n141 := cc 7 [w36,w0,w1,w54,w3,w24,w19] [q24,q421,q522,q528] [] (by decide +kernel)
def n142 := cc 8 [w36,w0,w1,w54,w3,w4,w24,w5] [q23,q170,q307,q421] [n141] (by decide +kernel)
def n143 := cc 7 [w36,w0,w1,w2,w3,w59,w19] [q26,q57,q77,q170,q247,q402] [] (by decide +kernel)
def n144 := cc 8 [w36,w0,w1,w2,w3,w4,w59,w5] [q25,q56,q80,q170,q308,q402,q421] [n143] (by decide +kernel)
def n145 := cc 8 [w36,w83,w0,w1,w2,w3,w4,w5] [q28,q56,q77,q80,q170,q267,q316,q403,q419,q421] [] (by decide +kernel)
def n146 := cc 8 [w36,w72,w0,w1,w2,w3,w4] [q121,q269,q519] [] (by decide +kernel)
def n147 := cc 8 [w36,w0,w1,w2,w54,w3,w4,w19] [q261,q354,q401,q421,q495,q522,q528] [n143,n141] (by decide +kernel)
def n148 := cc 9 [w36,w0,w1,w2,w54,w3,w4,w5] [q86,q170,q229,q300,q401,q421,q495,q522] [n140,n11,n68,n146,n145,n147,n144,n142] (by decide +kernel)
def n149 := cc 8 [w84,w1,w2,w54,w3,w4,w5] [q94,q279,q441,q495,q546] [] (by decide +kernel)
def n150 := cc 9 [w0,w1,w2,w54,w3,w8,w4,w5] [q86,q134,q229,q293,q441,q495] [n149] (by decide +kernel)
def n151 := cc 8 [w86,w1,w2,w54,w3,w4,w5] [q134,q239,q300,q419] [] (by decide +kernel)
def n152 := cc 9 [w85,w0,w1,w2,w54,w3,w4,w5] [q0,q86,q134,q229,q300,q419,q421] [n151] (by decide +kernel)
def n153 := cc 8 [w87,w1,w54,w3,w4,w24,w5] [q421,q531] [] (by decide +kernel)
def n154 := cc 8 [w0,w88,w1,w54,w3,w4,w24,w5] [q134,q421,q537] [] (by decide +kernel)
def n155 := cc 8 [w0,w1,w89,w54,w3,w4,w24,w5] [q133,q154,q307,q421] [] (by decide +kernel)
def n156 := cc 8 [w72,w0,w1,w54,w3,w4,w30] [q187,q419,q522] [] (by decide +kernel)
def n157 := cc 8 [w0,w1,w54,w90,w3,w4,w24,w5] [q134,q307,q417,q421] [] (by decide +kernel)
def n158 := cc 8 [w91,w0,w1,w54,w3,w4,w24,w5] [q175,q307,q421] [] (by decide +kernel)
def n159 := cc 7 [w0,w1,w92,w3,w4,w30] [q419,q522] [] (by decide +kernel)
def v44 : Closed T 7 := rotateClosed n141 auto1 auto1ok
def n160 := cc 8 [w0,w1,w54,w3,w4,w30,w19] [q108,q419,q495,q528] [v44,n113,n159] (by decide +kernel)
def n161 := cc 8 [w0,w1,w54,w3,w4,w5,w31] [q103,q134,q165,q209,q445] [n115] (by decide +kernel)
def n162 := cc 8 [w33,w0,w1,w54,w3,w4,w5] [q105,q172,q421,q469] [n116] (by decide +kernel)
def v45 : Closed T 8 := rotateClosed n156 auto1 auto1ok
def v46 : Closed T 8 := rotateClosed n160 auto1 auto1ok
def n163 := cc 9 [w0,w1,w54,w3,w4,w24,w5] [q138,q229,q421,q441] [n142,v45,n158,n162,n153,n72,n117,n154,n155,n157,n161,v46] (by decide +kernel)
def n164 := cc 8 [w87,w1,w2,w54,w3,w4,w5] [q134,q138,q281,q421,q474] [] (by decide +kernel)
def n165 := cc 7 [w72,w93,w1,w2,w3,w4] [q80,q134,q272,q419] [] (by decide +kernel)
def n166 := cc 8 [w72,w0,w1,w2,w3,w4,w30] [q80,q187,q269,q419] [n165] (by decide +kernel)
def v47 : Closed T 8 := rotateClosed n166 auto1 auto1ok
def n167 := cc 9 [w0,w1,w2,w54,w3,w4,w24,w5] [q138,q229,q300,q334,q421,q441] [v47,n164] (by decide +kernel)
def n168 := cc 8 [w0,w1,w54,w3,w4,w95,w5] [q74,q133,q209,q229,q419,q469,q556] [] (by decide +kernel)
def n169 := cc 8 [w94,w96,w0,w1,w54,w3,w4,w5] [q172,q220,q273,q371,q469] [] (by decide +kernel)
def n170 := cc 9 [w94,w0,w1,w54,w3,w4,w5] [q133,q172,q187,q229,q421,q495] [n169,n168] (by decide +kernel)
def n171 := cc 8 [w0,w1,w2,w54,w3,w4,w97,w5] [q133,q300,q419,q529] [] (by decide +kernel)
def n172 := cc 8 [w0,w1,w2,w89,w98,w4,w5] [q201,q300,q363,q441,q495,q546] [] (by decide +kernel)
def n173 := cc 8 [w0,w1,w2,w89,w3,w4,w59,w5] [q154,q171,q308,q421] [] (by decide +kernel)
def n174 := cc 7 [w99,w0,w1,w2,w54,w3,w4,w5] [q20,q103,q117] [] (by decide +kernel)
def n175 := cc 8 [w0,w1,w2,w89,w54,w3,w4,w5,w19] [q133,q300,q419,q421,q441,q528,q529] [n174] (by decide +kernel)
def v48 : Closed T 8 := rotateClosed n173 auto1 auto1ok
def v49 : Closed T 8 := rotateClosed n171 auto1 auto1ok
def v50 : Closed T 8 := rotateClosed n155 auto1 auto1ok
def n176 := cc 9 [w0,w1,w2,w89,w54,w3,w4,w5] [q0,q133,q154,q199,q300] [n175,n173,v48,n172,n171,v49,n155,v50] (by decide +kernel)
def n177 := cc 8 [w0,w100,w1,w2,w54,w3,w4,w5] [q134,q300,q441,q495] [] (by decide +kernel)
def n178 := cc 9 [w0,w1,w2,w54,w3,w98,w4,w5] [q134,q291,q300,q441,q495] [n63,n149,n177,n172] (by decide +kernel)
def n179 := cc 9 [w101,w0,w1,w2,w54,w3,w4,w5] [q293,q441,q495,q522,q546] [] (by decide +kernel)
def n180 := cc 9 [w102,w0,w1,w2,w54,w3,w4,w5] [q0,q134,q300,q419,q421,q546] [n65,n151] (by decide +kernel)
def n181 := cc 8 [w87,w1,w2,w3,w4,w59,w5] [q138,q421,q531] [] (by decide +kernel)
def n182 := cc 8 [w0,w68,w1,w2,w3,w4,w5] [q98,q139,q534] [] (by decide +kernel)
def n183 := cc 8 [w0,w68,w1,w2,w3,w4,w59,w5] [q73,q98,q308,q421,q442,q522] [n121] (by decide +kernel)
def n184 := cc 8 [w0,w1,w2,w103,w3,w4,w59,w5] [q0,q154,q308,q421] [] (by decide +kernel)
def n185 := cc 8 [w91,w0,w1,w2,w3,w4,w59,w5] [q80,q175,q308,q421,q498] [] (by decide +kernel)
def n186 := cc 8 [w72,w0,w1,w2,w3,w4,w69] [q187,q419,q522] [n165] (by decide +kernel)
def v51 : Closed T 7 := rotateClosed n143 auto1 auto1ok
def n187 := cc 8 [w0,w1,w2,w3,w4,w69,w19] [q80,q135,q165,q181,q252,q495,q533] [v51,n123] (by decide +kernel)
def n188 := cc 8 [w0,w1,w2,w3,w4,w5,w70] [q0,q73,q103,q134,q209,q293,q446,q541] [n126] (by decide +kernel)
def n189 := cc 8 [w71,w0,w1,w2,w3,w4,w5] [q73,q80,q134,q209,q249,q293,q447,q543] [n127] (by decide +kernel)
def v52 : Closed T 8 := rotateClosed n186 auto1 auto1ok
def v53 : Closed T 8 := rotateClosed n187 auto1 auto1ok
def n190 := cc 9 [w0,w1,w2,w3,w4,w59,w5] [q138,q187,q245,q293,q421,q441] [v0,n144,v52,n185,n189,n181,n128,n183,n182,n184,n188,v53] (by decide +kernel)
def n191 := cc 8 [w0,w68,w1,w2,w54,w3,w4,w5] [q20,q139,q300,q421,q522] [n130] (by decide +kernel)
def n192 := cc 9 [w0,w1,w2,w54,w3,w4,w59,w5] [q98,q138,q300,q421,q441] [v52,n164,n73,n131,n191,n173] (by decide +kernel)
def n193 := cc 8 [w0,w104,w1,w2,w3,w4,w5] [q80,q168,q219,q267,q316,q471,q540] [] (by decide +kernel)
def n194 := cc 8 [w0,w1,w2,w3,w4,w73,w5] [q73,q209,q271,q419,q447,q519] [n132] (by decide +kernel)
def n195 := cc 8 [w105,w0,w1,w2,w3,w4,w5] [q0,q73,q80,q293,q522] [] (by decide +kernel)
def n196 := cc 8 [w72,w96,w0,w1,w2,w3,w4,w5] [q12,q172,q318,q419,q447] [] (by decide +kernel)
def v54 : Closed T 8 := rotateClosed n145 auto1 auto1ok
def v55 : Closed T 8 := rotateClosed n193 auto1 auto1ok
def n197 := cc 9 [w72,w0,w1,w2,w3,w4,w5] [q80,q172,q187,q269,q293,q421,q495] [n195,n68,n146,v54,n196,n133,n166,n186,v55,n194] (by decide +kernel)
def n198 := cc 8 [w72,w96,w0,w1,w2,w54,w3,w4,w5] [q220,q318,q419,q447] [] (by decide +kernel)
def n199 := cc 9 [w72,w0,w1,w2,w54,w3,w4,w5] [q172,q187,q421,q495,q522] [n198,n186,n156] (by decide +kernel)
def n200 := cc 6 [w108,w1,w107,w54,w3,w4,w5] [] [] (by decide +kernel)
def n201 := cc 7 [w1,w107,w2,w54,w3,w4,w5] [q144,q242,q304,q494,q540] [n200] (by decide +kernel)
def n202 := cc 6 [w1,w107,w54,w109,w3,w4,w5] [q8,q14,q305] [] (by decide +kernel)
def n203 := cc 7 [w106,w1,w107,w2,w54,w3,w4,w5] [q49,q242,q291] [n202] (by decide +kernel)
def n204 := cc 7 [w0,w106,w1,w54,w109,w3,w4,w5] [q69,q96,q291] [n202] (by decide +kernel)
def n205 := cc 6 [w111,w0,w106,w1,w2,w3,w4] [] [] (by decide +kernel)
def n206 := cc 7 [w0,w106,w1,w2,w110,w3,w4,w5] [q0,q212,q316] [n205] (by decide +kernel)
def n207 := cc 7 [w114,w0,w113,w1,w2,w3,w4,w5] [q18,q27] [] (by decide +kernel)
def v56 : Closed T 7 := rotateClosed n207 auto1 auto1ok
def n208 := cc 8 [w0,w106,w1,w2,w54,w3,w4,w5] [q110,q133,q134,q144,q254,q291,q302,q495] [v56,n206,n204,n203,n201] (by decide +kernel)
def n209 := cc 8 [w0,w1,w2,w115,w3,w4,w5] [q86,q133,q154,q291,q495] [] (by decide +kernel)
def n210 := cc 8 [w116,w0,w1,w2,w3,w4,w5] [q50,q66,q112,q257,q291,q495,q547] [] (by decide +kernel)
def n211 := cc 9 [w0,w1,w2,w54,w3,w4,w41,w5] [q133,q138,q254,q291,q419,q495] [n210,n75,n208,n209] (by decide +kernel)
def v57 : Closed T 8 := rotateClosed n169 auto1 auto1ok
def v58 : Closed T 8 := rotateClosed n198 auto1 auto1ok
def v59 : Closed T 8 := rotateClosed n196 auto1 auto1ok
def n212 := cc 9 [w91,w0,w1,w2,w54,w3,w4,w5] [q175,q187,q274,q300,q421,q495] [v57,v58,v59,n185,n158] (by decide +kernel)
def n213 := cc 6 [w117,w1,w63,w54,w3,w4,w5] [] [] (by decide +kernel)
def n214 := cc 7 [w1,w63,w2,w54,w3,w4,w5] [q151,q198,q248,q433,q540] [n213,n77,n135] (by decide +kernel)
def n215 := cc 6 [w1,w63,w54,w118,w3,w4,w5] [q291] [] (by decide +kernel)
def n216 := cc 7 [w62,w1,w63,w2,w54,w3,w4,w5] [q248,q291,q549] [n215] (by decide +kernel)
def n217 := cc 7 [w0,w62,w1,w54,w118,w3,w4,w5] [q103,q120,q291] [n215] (by decide +kernel)
def n218 := cc 7 [w0,w62,w1,w2,w119,w3,w4,w5] [q44,q73,q120,q173,q354] [] (by decide +kernel)
def n219 := cc 7 [w120,w0,w62,w1,w2,w3,w4,w5] [q73,q103,q114] [] (by decide +kernel)
def n220 := cc 8 [w0,w62,w1,w2,w54,w3,w4,w5] [q20,q133,q134,q151,q198,q261,q291,q300,q354,q549] [n219,n78,n136,n218,n217,n216,n214] (by decide +kernel)
def n221 := cc 7 [w1,w63,w2,w54,w3,w4,w5,w19] [q151,q517,q528,q529,q540] [] (by decide +kernel)
def n222 := cc 7 [w120,w0,w1,w2,w3,w4,w5,w19] [q114,q120,q153,q165,q209] [] (by decide +kernel)
def n223 := cc 8 [w0,w62,w1,w2,w54,w3,w4,w5,w19] [q151,q261,q419,q517,q528,q529,q533] [n222,n221] (by decide +kernel)
def v60 : Closed T 7 := rotateClosed n159 auto1 auto1ok
def n224 := cc 8 [w0,w1,w2,w92,w3,w4,w5] [q0,q159,q203,q293,q522] [n159,v60] (by decide +kernel)
def n225 := cc 8 [w0,w1,w2,w92,w54,w3,w4,w5,w19] [q133,q172,q419,q421] [] (by decide +kernel)
def n226 := cc 8 [w121,w0,w1,w2,w3,w4,w5] [q0,q134,q293,q536] [] (by decide +kernel)
def n227 := cc 7 [w1,w2,w54,w3,w123,w4,w5,w19] [q354,q497,q517,q528,q529] [] (by decide +kernel)
def n228 := cc 7 [w124,w0,w1,w2,w3,w4,w5,w19] [q43,q120,q162,q165,q209] [] (by decide +kernel)
def n229 := cc 8 [w0,w1,w2,w54,w122,w3,w4,w5,w19] [q261,q354,q419,q495,q517,q528,q529] [n228,n227] (by decide +kernel)
def v61 : Closed T 8 := rotateClosed n147 auto1 auto1ok
def n230 := cc 9 [w0,w1,w2,w54,w3,w4,w5,w19] [q133,q138,q187,q229,q261,q300,q354,q419,q421,q441,q495,q517,q528] [n140,n195,n147,v61,n12,n226,n79,n69,n137,n220,n223,n175,n225,n224,n229,n188,n187,v53,n161,n160,v46] (by decide +kernel)
def v62 : Closed T 9 := rotateClosed n148 auto1 auto1ok
def v63 : Closed T 9 := rotateClosed n170 auto1 auto1ok
def v64 : Closed T 9 := rotateClosed n199 auto1 auto1ok
def v65 : Closed T 9 := rotateClosed n197 auto1 auto1ok
def v66 : Closed T 9 := rotateClosed n212 auto1 auto1ok
def v67 : Closed T 9 := rotateClosed n167 auto1 auto1ok
def v68 : Closed T 9 := rotateClosed n192 auto1 auto1ok
def v69 : Closed T 9 := rotateClosed n211 auto1 auto1ok
def v70 : Closed T 9 := rotateClosed n190 auto1 auto1ok
def v71 : Closed T 9 := rotateClosed n163 auto1 auto1ok
def n231 := cc 10 [w0,w1,w2,w54,w3,w4,w5] [q0,q86,q138,q187,q229,q293] [n148,v62,n170,v63,n199,v64,n197,v65,n212,v66,n139,n179,n81,n13,n180,n152,n66,n80,n70,n138,n176,n64,n150,n178,n167,v67,n192,v68,n211,v69,n230,n190,v70,n163,v71] (by decide +kernel)
def n232 := cc 9 [w0,w1,w2,w54,w3,w4,w5] [q20,q138,q187,q229,q300] [] (by decide +kernel)
def n233 := cc 9 [w125,w126,w1,w3,w4,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n234 := cc 8 [w125,w84,w1,w2,w3,w4,w5] [q3,q50,q94,q164,q208,q279,q365] [] (by decide +kernel)
def n235 := cc 9 [w125,w0,w1,w2,w3,w8,w4,w5] [q50,q94,q164,q208,q229,q293] [n234] (by decide +kernel)
def n236 := cc 8 [w125,w86,w1,w2,w3,w4,w5] [q52,q125,q177,q222,q239,q296] [] (by decide +kernel)
def n237 := cc 9 [w125,w85,w0,w1,w2,w3,w4,w5] [q0,q125,q177,q222,q229,q363] [n236] (by decide +kernel)
def n238 := cc 10 [w125,w0,w1,w2,w3,w4,w5] [q0,q86,q138,q187,q229,q293] [n237,n233,n235,n232] (by decide +kernel)
def n239 := cc 8 [w91,w0,w1,w2,w3,w4,w127,w5] [q175,q209,q274,q375,q513] [] (by decide +kernel)
def n240 := cc 8 [w0,w1,w2,w3,w4,w128,w19] [q80,q165,q261,q512] [] (by decide +kernel)
def n241 := cc 8 [w0,w1,w2,w3,w4,w5,w129] [q0,q73,q165,q209,q261,q293] [] (by decide +kernel)
def n242 := cc 8 [w130,w0,w1,w2,w3,w4,w5] [q0,q80,q172,q275,q293] [] (by decide +kernel)
def v72 : Closed T 8 := rotateClosed n240 auto1 auto1ok
def n243 := cc 9 [w0,w1,w2,w3,w4,w127,w5] [q73,q138,q209,q229,q293,q417,q473] [n239,n242,n241,v72] (by decide +kernel)
def n244 := cc 8 [w53,w126,w0,w1,w3,w4,w5] [q3,q177,q222,q239,q365] [] (by decide +kernel)
def n245 := cc 9 [w126,w0,w1,w2,w3,w52,w4,w5] [q66,q138,q187,q239,q293] [n244] (by decide +kernel)
def n246 := cc 8 [w126,w0,w1,w56,w3,w4,w5] [q52,q164,q208,q279,q296] [] (by decide +kernel)
def n247 := cc 9 [w126,w55,w0,w1,w2,w3,w4,w5] [q0,q138,q187,q279,q373] [n246] (by decide +kernel)
def n248 := cc 8 [w91,w126,w0,w1,w3,w4,w24,w5] [q175,q209,q274,q376,q514] [] (by decide +kernel)
def n249 := cc 8 [w126,w0,w1,w3,w4,w30,w19] [q261,q512,q528] [] (by decide +kernel)
def n250 := cc 8 [w126,w0,w1,w3,w4,w5,w31] [q134,q165,q209,q261] [] (by decide +kernel)
def n251 := cc 8 [w33,w126,w0,w1,w3,w4,w5] [q209,q275,q417] [] (by decide +kernel)
def v73 : Closed T 8 := rotateClosed n249 auto1 auto1ok
def n252 := cc 9 [w126,w0,w1,w3,w4,w24,w5] [q134,q138,q209,q229,q417,q473] [n248,n251,n250,v73] (by decide +kernel)
def n253 := cc 8 [w0,w131,w1,w2,w3,w4,w5] [q177,q254,q512] [] (by decide +kernel)
def n254 := cc 9 [w126,w0,w1,w2,w3,w4,w41,w5] [q138,q254,q512] [n253] (by decide +kernel)
def n255 := cc 9 [w91,w126,w0,w1,w2,w3,w4,w5] [q175,q187,q274,q373,q512] [n248,n239] (by decide +kernel)
def n256 := cc 8 [w0,w132,w1,w2,w3,w4,w5] [q134,q225,q261,q293,q475] [] (by decide +kernel)
def n257 := cc 8 [w126,w0,w1,w2,w122,w3,w4,w5,w19] [q262,q512,q517,q524,q528,q529] [] (by decide +kernel)
def n258 := cc 9 [w126,w0,w1,w2,w3,w4,w5,w19] [q138,q187,q261,q354,q373,q473,q512,q517,q528] [n257,n250,n249,v73,n256,n241,n240,v72] (by decide +kernel)
def v74 : Closed T 9 := rotateClosed n255 auto1 auto1ok
def v75 : Closed T 9 := rotateClosed n254 auto1 auto1ok
def v76 : Closed T 9 := rotateClosed n252 auto1 auto1ok
def v77 : Closed T 9 := rotateClosed n243 auto1 auto1ok
def n259 := cc 10 [w126,w0,w1,w2,w3,w4,w5] [q0,q138,q187,q229,q293] [n255,v74,n233,n247,n245,n254,v75,n258,n252,v76,n232,n243,v77] (by decide +kernel)
def n260 := cc 9 [w0,w1,w2,w134,w3,w4,w5] [q86,q138,q187,q293] [] (by decide +kernel)
def n261 := cc 8 [w135,w1,w2,w4,w5] [q86,q138,q546] [] (by decide +kernel)
def n262 := cc 9 [w133,w1,w2,w52,w4,w5] [q0,q86,q138,q187] [n261] (by decide +kernel)
def n263 := cc 10 [w133,w0,w1,w2,w3,w4,w5] [q86,q138,q187,q229,q293] [n262,n260] (by decide +kernel)
def n264 := cc 8 [w1,w137,w2,w3,w52,w4,w5] [q239,q300,q427,q487] [] (by decide +kernel)
def n265 := cc 8 [w138,w0,w1,w2,w3,w4,w5] [q125,q363,q426,q486] [] (by decide +kernel)
def n266 := cc 8 [w53,w0,w136,w1,w3,w4,w5] [q68,q125,q239,q426,q486] [] (by decide +kernel)
def n267 := cc 9 [w0,w136,w1,w2,w3,w52,w4,w5] [q86,q239,q293,q426,q486] [n266,n265,n264] (by decide +kernel)
def n268 := cc 8 [w139,w0,w1,w2,w3,w4,w5] [q239,q460,q506,q551] [] (by decide +kernel)
def n269 := cc 8 [w25,w53,w0,w1,w3,w4,w5] [q125,q364,q460,q506] [] (by decide +kernel)
def n270 := cc 9 [w25,w0,w1,w2,w3,w52,w4,w5] [q86,q239,q293,q460,q506] [n268,n269] (by decide +kernel)
def n271 := cc 8 [w0,w1,w2,w28,w52,w4,w5] [q94,q239,q293,q456,q502] [] (by decide +kernel)
def n272 := cc 9 [w0,w27,w1,w2,w52,w4,w5] [q86,q229,q293,q424,q484] [n271] (by decide +kernel)
def n273 := cc 8 [w0,w1,w2,w141,w3,w4,w5] [q94,q239,q456,q502,q551] [] (by decide +kernel)
def n274 := cc 8 [w0,w140,w1,w2,w141,w3,w4,w5] [q136,q239,q456,q502] [] (by decide +kernel)
def n275 := cc 9 [w0,w140,w1,w2,w3,w4,w5] [q86,q136,q239,q424,q484] [n268,n274,n273] (by decide +kernel)
def n276 := cc 9 [w85,w0,w1,w2,w52,w4,w5] [q134,q222,q239,q293,q424,q484] [] (by decide +kernel)
def n277 := cc 8 [w0,w142,w1,w2,w3,w4,w5] [q125,q239,q364,q426,q486] [] (by decide +kernel)
def n278 := cc 9 [w53,w0,w1,w2,w3,w4,w5] [q125,q134,q293,q415,q424,q484] [n268,n269,n244,n266,n63,n277] (by decide +kernel)
def n279 := cc 10 [w0,w1,w2,w3,w52,w4,w5] [q86,q229,q293,q424,q484] [n270,n276,n278,n245,n262,n267,n272,n275,n64] (by decide +kernel)
def n280 := cc 9 [w0,w144,w2,w3,w4,w5] [q0,q86,q138,q187] [] (by decide +kernel)
def n281 := cc 9 [w0,w145,w2,w3,w4,w5] [q0,q86,q138,q187] [] (by decide +kernel)
def n282 := cc 9 [w0,w1,w2,w146,w3,w4,w5] [q0,q86,q138,q187] [] (by decide +kernel)
def n283 := cc 9 [w143,w55,w1,w2,w4,w5] [q86,q138,q187,q293] [n261] (by decide +kernel)
def n284 := cc 10 [w143,w0,w1,w2,w3,w4,w5] [q0,q86,q138,q187,q229] [n283,n281,n282,n280] (by decide +kernel)
def n285 := cc 8 [w0,w1,w2,w3,w4,w147,w5] [q73,q80,q134,q164,q187,q334] [] (by decide +kernel)
def n286 := cc 8 [w148,w0,w1,w2,w3,w4,w5] [q73,q138,q208,q369,q546] [] (by decide +kernel)
def n287 := cc 8 [w0,w1,w2,w56,w3,w4,w5,w19] [q73,q80,q135,q164,q208,q354,q517,q546] [] (by decide +kernel)
def v78 : Closed T 8 := rotateClosed n286 auto1 auto1ok
def v79 : Closed T 8 := rotateClosed n285 auto1 auto1ok
def n288 := cc 9 [w0,w1,w2,w56,w3,w4,w5] [q0,q134,q164,q208,q293,q546] [n286,v78,n246,n287,n285,v79,n65] (by decide +kernel)
def n289 := cc 8 [w150,w0,w1,w2,w3,w4,w5] [q134,q177,q383,q421] [] (by decide +kernel)
def n290 := cc 7 [w0,w1,w2,w3,w149,w30,w19] [q76,q135,q211,q351,q420] [] (by decide +kernel)
def n291 := cc 8 [w0,w1,w2,w3,w4,w149,w5,w30] [q73,q134,q165,q211,q280,q348,q420,q547] [n290] (by decide +kernel)
def n292 := cc 8 [w94,w0,w1,w2,w3,w4,w149,w5] [q73,q211,q280,q369,q547] [] (by decide +kernel)
def v80 : Closed T 7 := rotateClosed n290 auto1 auto1ok
def n293 := cc 8 [w0,w1,w2,w3,w4,w151,w19] [q80,q167,q354,q419] [v80] (by decide +kernel)
def n294 := cc 8 [w0,w1,w2,w3,w4,w5,w152] [q73,q134,q167,q211,q229,q354] [] (by decide +kernel)
def n295 := cc 8 [w153,w0,w1,w2,w3,w4,w5] [q80,q134,q175,q229,q372] [] (by decide +kernel)
def v81 : Closed T 8 := rotateClosed n293 auto1 auto1ok
def n296 := cc 9 [w0,w1,w2,w3,w4,w149,w5] [q73,q138,q211,q229,q293,q547] [n292,n295,n289,n291,n285,n294,v81] (by decide +kernel)
def n297 := cc 9 [w55,w0,w1,w2,w8,w4,w5] [q134,q208,q279,q293,q424,q484] [] (by decide +kernel)
def n298 := cc 8 [w0,w154,w1,w2,w3,w4,w5] [q171,q334,q527] [] (by decide +kernel)
def n299 := cc 8 [w55,w0,w1,w2,w3,w4,w30,w19] [q279,q351,q484,q524,q526,q528] [n290] (by decide +kernel)
def n300 := cc 6 [w32,w155,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n301 := cc 6 [w55,w32,w27,w1,w2,w4,w5] [q79,q85,q134] [] (by decide +kernel)
def n302 := cc 7 [w55,w32,w1,w2,w3,w4,w5] [q134,q209,q459] [n44,n301,n300] (by decide +kernel)
def n303 := cc 8 [w55,w0,w1,w2,w3,w4,w5,w31] [q134,q137,q165,q209,q342] [n302] (by decide +kernel)
def n304 := cc 8 [w33,w55,w0,w1,w2,w3,w4,w5] [q80,q134,q137,q172,q209,q275,q346,q421,q467] [] (by decide +kernel)
def v82 : Closed T 8 := rotateClosed n299 auto1 auto1ok
def v83 : Closed T 8 := rotateClosed n291 auto1 auto1ok
def n305 := cc 9 [w55,w0,w1,w2,w3,w4,w24,w5] [q138,q187,q279,q334,q417,q424,q525] [n304,n303,v82,n298,v83,n285] (by decide +kernel)
def n306 := cc 8 [w156,w0,w1,w2,w3,w4,w5] [q73,q174,q208,q279,q369,q546] [] (by decide +kernel)
def n307 := cc 8 [w55,w0,w1,w2,w3,w4,w95,w5] [q73,q209,q279,q370,q467,q555] [] (by decide +kernel)
def n308 := cc 9 [w94,w55,w0,w1,w2,w3,w4,w5] [q172,q187,q279,q369,q484] [n292,n307,n306] (by decide +kernel)
def n309 := cc 8 [w43,w55,w0,w1,w2,w4,w5] [q177,q383,q484] [] (by decide +kernel)
def n310 := cc 9 [w55,w0,w1,w2,w4,w41,w5] [q138,q293,q484] [n309] (by decide +kernel)
def n311 := cc 8 [w0,w157,w1,w2,w3,w4,w5] [q134,q137,q186,q228,q229,q354] [] (by decide +kernel)
def n312 := cc 8 [w34,w55,w0,w1,w2,w3,w4,w5] [q134,q137,q225,q360,q480] [] (by decide +kernel)
def n313 := cc 9 [w55,w0,w1,w2,w3,w4,w5,w19] [q138,q261,q279,q354,q424,q484,q528,q539] [n312,n303,n299,v82,n311,n287,n294,n293,v81] (by decide +kernel)
def v84 : Closed T 9 := rotateClosed n308 auto1 auto1ok
def v85 : Closed T 9 := rotateClosed n305 auto1 auto1ok
def v86 : Closed T 9 := rotateClosed n310 auto1 auto1ok
def v87 : Closed T 9 := rotateClosed n296 auto1 auto1ok
def n314 := cc 10 [w55,w0,w1,w2,w3,w4,w5] [q0,q138,q187,q229,q293] [n308,v84,n283,n247,n66,n305,v85,n313,n297,n310,v86,n288,n296,v87] (by decide +kernel)
def n315 := cc 9 [w0,w159,w2,w3,w4,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n316 := cc 9 [w161,w0,w2,w3,w4,w5] [q86,q138,q484] [] (by decide +kernel)
def n317 := cc 9 [w0,w1,w162,w3,w4,w5] [q86,q187,q424] [] (by decide +kernel)
def n318 := cc 9 [w0,w1,w2,w162,w3,w4,w5] [q86,q187,q424] [] (by decide +kernel)
def n319 := cc 9 [w163,w0,w1,w3,w4,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n320 := cc 9 [w0,w1,w2,w164,w4,w5] [q0,q86,q138,q187] [] (by decide +kernel)
def n321 := cc 9 [w165,w0,w1,w2,w4,w5] [q86,q138,q187,q293] [] (by decide +kernel)
def n322 := cc 9 [w0,w1,w2,w3,w4,w166] [q86,q187,q424] [] (by decide +kernel)
def n323 := cc 9 [w167,w0,w1,w2,w3,w5] [q86,q187,q424] [] (by decide +kernel)
def n324 := cc 9 [w158,w1,w2,w3,w168,w5] [q86,q138,q187,q424] [] (by decide +kernel)
def v88 : Closed T 9 := rotateClosed n316 auto1 auto1ok
def v89 : Closed T 9 := rotateClosed n319 auto1 auto1ok
def v90 : Closed T 9 := rotateClosed n321 auto1 auto1ok
def v91 : Closed T 9 := rotateClosed n323 auto1 auto1ok
def n325 := cc 10 [w158,w0,w1,w2,w3,w4,w5] [q86,q187,q229,q424] [v88,v89,v90,v91,n324,n318,n322,n320,n317,n315] (by decide +kernel)
def n326 := cc 6 [w1,w137,w2,w3,w168,w169,w19] [q133,q139] [] (by decide +kernel)
def n327 := cc 6 [w171,w1,w137,w2,w3,w4,w172] [] [] (by decide +kernel)
def v92 : Closed T 6 := rotateClosed n327 auto1 auto1ok
def n328 := cc 7 [w1,w137,w2,w3,w4,w168,w5,w169] [q141,q250] [v92,n326] (by decide +kernel)
def v93 : Closed T 6 := rotateClosed n326 auto1 auto1ok
def n329 := cc 7 [w1,w137,w2,w3,w4,w172,w19] [q133,q139,q188,q252,q487,q517] [v93] (by decide +kernel)
def n330 := cc 6 [w174,w137,w2,w3,w4,w5,w173] [q248] [] (by decide +kernel)
def n331 := cc 6 [w175,w1,w137,w3,w4,w5,w173] [q115] [] (by decide +kernel)
def n332 := cc 7 [w1,w137,w2,w3,w4,w5,w173] [q7,q139,q188,q248,q517] [n331,n330] (by decide +kernel)
def v94 : Closed T 7 := rotateClosed n329 auto1 auto1ok
def n333 := cc 8 [w1,w137,w2,w3,w4,w168,w5] [q133,q139,q188,q245,q303,q427] [n328,n332,v94] (by decide +kernel)
def n334 := cc 8 [w0,w1,w2,w3,w4,w172,w176] [q9,q107,q251,q519] [] (by decide +kernel)
def n335 := cc 8 [w0,w1,w2,w3,w4,w170,w5] [q73,q80,q139,q189,q245,q308,q427] [] (by decide +kernel)
def n336 := cc 7 [w177,w0,w1,w2,w3,w4,w172] [q103,q117,q190,q489,q517] [] (by decide +kernel)
def n337 := cc 8 [w0,w136,w1,w2,w3,w4,w172,w19] [q80,q114,q139,q188,q252,q332,q486,q529,q536] [n336,n329] (by decide +kernel)
def n338 := cc 7 [w178,w0,w1,w2,w3,w4,w5] [q5,q6,q103,q106,q117,q127,q128,q130,q293] [] (by decide +kernel)
def n339 := cc 7 [w178,w0,w1,w2,w3,w4,w5,w173] [q115,q138,q187,q517] [] (by decide +kernel)
def n340 := cc 7 [w0,w136,w174,w2,w3,w4,w5,w173] [q73,q80,q248,q390,q524] [n330] (by decide +kernel)
def n341 := cc 6 [w175,w179,w0,w1,w3,w4,w5] [] [] (by decide +kernel)
def n342 := cc 7 [w175,w0,w136,w1,w3,w4,w5] [q134,q182,q226,q248] [n341] (by decide +kernel)
def n343 := cc 7 [w175,w0,w136,w1,w3,w4,w5,w173] [q73,q80,q248,q390] [n331] (by decide +kernel)
def n344 := cc 8 [w0,w136,w1,w2,w3,w4,w5,w173] [q31,q73,q80,q114,q139,q188,q248,q291,q325,q536] [n342,n343,n338,n339,n340,n332] (by decide +kernel)
def v95 : Closed T 8 := rotateClosed n337 auto1 auto1ok
def v96 : Closed T 8 := rotateClosed n334 auto1 auto1ok
def n345 := cc 9 [w0,w136,w1,w2,w3,w4,w168,w5] [q86,q139,q188,q245,q320,q426,q528] [n344,v95,n335,v96,n333] (by decide +kernel)
def n346 := cc 8 [w25,w0,w1,w2,w3,w4,w172,w19] [q80,q187,q252,q506,q525,q536] [] (by decide +kernel)
def n347 := cc 8 [w25,w0,w1,w2,w3,w4,w5,w173] [q54,q213,q248,q293,q524,q536] [] (by decide +kernel)
def v97 : Closed T 8 := rotateClosed n346 auto1 auto1ok
def n348 := cc 9 [w25,w0,w1,w2,w3,w4,w168,w5] [q86,q138,q213,q245,q320,q460,q524] [v0,n347,v97] (by decide +kernel)
def n349 := cc 6 [w1,w64,w74,w3,w4,w172,w30] [q136,q191] [] (by decide +kernel)
def n350 := cc 6 [w180,w1,w64,w2,w3,w4,w172] [] [] (by decide +kernel)
def v98 : Closed T 6 := rotateClosed n350 auto1 auto1ok
def v99 : Closed T 6 := rotateClosed n349 auto1 auto1ok
def n351 := cc 7 [w1,w64,w2,w74,w3,w4,w168,w5] [q16,q145,q240,q377] [v98,v99] (by decide +kernel)
def n352 := cc 6 [w1,w64,w2,w3,w168,w65,w19] [q136,q144] [] (by decide +kernel)
def n353 := cc 6 [w181,w1,w64,w2,w3,w4,w172] [] [] (by decide +kernel)
def v100 : Closed T 6 := rotateClosed n353 auto1 auto1ok
def n354 := cc 7 [w1,w64,w2,w3,w4,w168,w5,w65] [q146,q329] [v100,n352] (by decide +kernel)
def n355 := cc 6 [w1,w64,w2,w3,w4,w30,w173] [] [] (by decide +kernel)
def n356 := cc 6 [w1,w64,w2,w3,w4,w172,w31] [q136] [] (by decide +kernel)
def n357 := cc 6 [w33,w1,w64,w2,w3,w168,w5] [] [] (by decide +kernel)
def v101 : Closed T 6 := rotateClosed n357 auto1 auto1ok
def n358 := cc 7 [w1,w64,w2,w3,w4,w172,w30] [q136,q191,q241,q420] [v101,n356,n355,n349] (by decide +kernel)
def n359 := cc 6 [w1,w64,w2,w3,w168,w30,w19] [] [] (by decide +kernel)
def v102 : Closed T 6 := rotateClosed n356 auto1 auto1ok
def n360 := cc 7 [w1,w64,w2,w3,w4,w168,w5,w30] [q144,q165,q191] [n91,v102,n355,n359] (by decide +kernel)
def n361 := cc 6 [w34,w1,w64,w2,w3,w4,w172] [] [] (by decide +kernel)
def v103 : Closed T 6 := rotateClosed n352 auto1 auto1ok
def v104 : Closed T 6 := rotateClosed n359 auto1 auto1ok
def n362 := cc 7 [w1,w64,w2,w3,w4,w172,w19] [q17,q114,q136,q144,q191,q517] [n361,n356,n90,v103,v104] (by decide +kernel)
def n363 := cc 6 [w174,w64,w2,w3,w4,w5,w173] [q325,q450] [] (by decide +kernel)
def n364 := cc 6 [w175,w1,w64,w2,w3,w4,w5] [] [] (by decide +kernel)
def v105 : Closed T 6 := rotateClosed n355 auto1 auto1ok
def n365 := cc 7 [w1,w64,w2,w3,w4,w5,w173] [q144,q191,q325,q440,q517,q540] [n364,n363,n91,n355,v105] (by decide +kernel)
def v106 : Closed T 7 := rotateClosed n358 auto1 auto1ok
def v107 : Closed T 7 := rotateClosed n362 auto1 auto1ok
def n366 := cc 8 [w1,w64,w2,w3,w4,w168,w5] [q136,q144,q191,q240,q320] [n351,n354,n360,n93,n365,v106,v107] (by decide +kernel)
def n367 := cc 8 [w0,w1,w2,w3,w4,w172,w182] [q113,q134,q191,q330,q519] [] (by decide +kernel)
def n368 := cc 8 [w0,w1,w2,w3,w4,w66,w5] [q110,q134,q144,q229,q320,q520] [] (by decide +kernel)
def n369 := cc 6 [w76,w0,w1,w2,w3,w5,w173] [] [] (by decide +kernel)
def n370 := cc 7 [w76,w0,w1,w2,w3,w168,w5] [q82,q149,q417] [n369] (by decide +kernel)
def n371 := cc 6 [w183,w0,w1,w2,w3,w4,w30] [q229] [] (by decide +kernel)
def v108 : Closed T 6 := rotateClosed n369 auto1 auto1ok
def n372 := cc 7 [w0,w27,w1,w2,w3,w4,w30,w173] [q76,q135,q165,q248] [v108,n371,n355] (by decide +kernel)
def n373 := cc 6 [w78,w0,w1,w2,w3,w4,w172] [q86] [] (by decide +kernel)
def n374 := cc 7 [w0,w27,w1,w2,w3,w4,w172,w31] [q75,q80,q103,q134,q165,q209,q252] [n373,n356] (by decide +kernel)
def n375 := cc 7 [w33,w0,w27,w1,w2,w3,w168,w5] [q73,q82,q105,q172,q277,q422] [n357] (by decide +kernel)
def v109 : Closed T 7 := rotateClosed n375 auto1 auto1ok
def v110 : Closed T 7 := rotateClosed n370 auto1 auto1ok
def n376 := cc 8 [w0,w27,w1,w2,w3,w4,w172,w30] [q80,q134,q165,q191,q251,q331,q529,q532,q538] [v109,v110,n374,n372,n358] (by decide +kernel)
def n377 := cc 6 [w76,w0,w1,w2,w3,w172,w19] [q187] [] (by decide +kernel)
def n378 := cc 7 [w76,w0,w1,w2,w3,w4,w5,w172] [q80,q149,q187] [n369,n377] (by decide +kernel)
def n379 := cc 6 [w77,w0,w1,w2,w3,w168,w30] [] [] (by decide +kernel)
def v111 : Closed T 6 := rotateClosed n377 auto1 auto1ok
def n380 := cc 7 [w0,w27,w1,w2,w3,w168,w30,w19] [q76,q135,q144,q165,q247,q533] [v111,n379,n359] (by decide +kernel)
def v112 : Closed T 7 := rotateClosed n378 auto1 auto1ok
def v113 : Closed T 7 := rotateClosed n374 auto1 auto1ok
def n381 := cc 8 [w0,w27,w1,w2,w3,w4,w168,w5,w30] [q134,q144,q165,q191,q245,q320,q519,q520,q532,q533] [v112,n126,v113,n372,n380,n360] (by decide +kernel)
def v114 : Closed T 6 := rotateClosed n379 auto1 auto1ok
def n382 := cc 7 [w77,w0,w1,w2,w3,w4,w172] [q118,q134,q197,q517] [n122,v114] (by decide +kernel)
def n383 := cc 6 [w0,w1,w35,w2,w3,w4,w172] [] [] (by decide +kernel)
def n384 := cc 7 [w34,w0,w27,w1,w2,w3,w4,w172] [q80,q117,q181,q529,q552] [n361,n383] (by decide +kernel)
def v115 : Closed T 7 := rotateClosed n380 auto1 auto1ok
def n385 := cc 8 [w0,w27,w1,w2,w3,w4,w172,w19] [q80,q191,q252,q332,q448,q524,q529,q539] [n384,n382,n374,n123,v115,n362] (by decide +kernel)
def v116 : Closed T 6 := rotateClosed n371 auto1 auto1ok
def n386 := cc 7 [w183,w0,w1,w2,w3,w4,w5] [q134,q150,q197,q229,q325,q453] [n371,v116] (by decide +kernel)
def n387 := cc 7 [w183,w0,w1,w2,w3,w4,w5,w173] [q116,q138,q187,q517] [] (by decide +kernel)
def n388 := cc 7 [w0,w27,w174,w2,w3,w4,w5,w173] [q73,q325,q328,q449] [n363] (by decide +kernel)
def n389 := cc 6 [w0,w1,w184,w2,w3,w4,w5] [q73] [] (by decide +kernel)
def n390 := cc 7 [w175,w0,w27,w1,w2,w3,w4,w5] [q0,q73,q80,q134,q181,q225,q248,q293] [n364,n389] (by decide +kernel)
def v117 : Closed T 7 := rotateClosed n372 auto1 auto1ok
def n391 := cc 8 [w0,w27,w1,w2,w3,w4,w5,w173] [q73,q80,q144,q191,q248,q291,q325,q448,q524,q536] [n390,n386,n387,n388,n126,n372,v117,n365] (by decide +kernel)
def v118 : Closed T 8 := rotateClosed n376 auto1 auto1ok
def v119 : Closed T 8 := rotateClosed n385 auto1 auto1ok
def v120 : Closed T 8 := rotateClosed n367 auto1 auto1ok
def n392 := cc 9 [w0,w27,w1,w2,w3,w4,w168,w5] [q86,q144,q191,q245,q320,q524,q528] [n381,n128,n391,v118,v119,n368,v120,n366] (by decide +kernel)
def n393 := cc 8 [w36,w0,w1,w2,w3,w168,w24,w5] [q30,q170,q245,q321,q405,q520] [] (by decide +kernel)
def n394 := cc 8 [w36,w0,w1,w2,w3,w168,w19] [q324,q404,q464,q528] [n143] (by decide +kernel)
def n395 := cc 9 [w36,w0,w1,w2,w3,w4,w168,w5] [q86,q170,q245,q320,q404,q464,q524] [n16,n144,n393,n394] (by decide +kernel)
def n396 := cc 6 [w1,w2,w186,w3,w168,w187,w19] [q133,q154] [] (by decide +kernel)
def n397 := cc 6 [w189,w1,w2,w186,w3,w4,w172] [] [] (by decide +kernel)
def v121 : Closed T 6 := rotateClosed n397 auto1 auto1ok
def n398 := cc 7 [w1,w2,w186,w3,w4,w168,w5,w187] [q157,q250] [v121,n396] (by decide +kernel)
def v122 : Closed T 6 := rotateClosed n396 auto1 auto1ok
def n399 := cc 7 [w1,w2,w186,w3,w4,w172,w19] [q22,q133,q154,q199,q252,q517] [v122] (by decide +kernel)
def n400 := cc 6 [w175,w1,w186,w3,w4,w5,w173] [q156,q184] [] (by decide +kernel)
def n401 := cc 7 [w1,w2,w186,w3,w4,w5,w173] [q154,q199,q248,q325,q444,q517] [n400] (by decide +kernel)
def v123 : Closed T 7 := rotateClosed n399 auto1 auto1ok
def n402 := cc 8 [w1,w2,w186,w3,w4,w168,w5] [q133,q154,q199,q245,q320] [n398,n401,v123] (by decide +kernel)
def n403 := cc 8 [w0,w1,w2,w3,w4,w172,w190] [q199,q251,q519] [] (by decide +kernel)
def n404 := cc 8 [w0,w1,w2,w3,w4,w188,w5] [q73,q80,q154,q187,q245,q320] [] (by decide +kernel)
def n405 := cc 7 [w191,w0,w1,w2,w3,w4,w172] [q202,q252,q517] [] (by decide +kernel)
def n406 := cc 8 [w0,w1,w185,w2,w3,w4,w172,w19] [q80,q199,q252,q448,q529,q539] [n405,n399] (by decide +kernel)
def n407 := cc 7 [w192,w0,w1,w2,w3,w4,w5] [q0,q158,q178,q185,q248] [] (by decide +kernel)
def n408 := cc 7 [w192,w0,w1,w2,w3,w4,w5,w173] [q155,q187,q517] [] (by decide +kernel)
def n409 := cc 7 [w175,w0,w1,w185,w3,w4,w5] [q134,q227,q248,q454] [] (by decide +kernel)
def n410 := cc 7 [w175,w0,w1,w185,w3,w4,w5,w173] [q73,q80,q156,q454,q455] [n400] (by decide +kernel)
def n411 := cc 8 [w0,w1,w185,w2,w3,w4,w5,w173] [q73,q80,q154,q199,q248,q325,q448,q539] [n409,n410,n407,n408,n401] (by decide +kernel)
def v124 : Closed T 8 := rotateClosed n406 auto1 auto1ok
def v125 : Closed T 8 := rotateClosed n403 auto1 auto1ok
def n412 := cc 9 [w0,w1,w185,w2,w3,w4,w168,w5] [q154,q199,q245,q424,q528] [n411,v124,n404,v125,n402] (by decide +kernel)
def n413 := cc 8 [w0,w1,w2,w3,w4,w193,w5] [q73,q80,q134,q177,q223,q242,q320] [] (by decide +kernel)
def n414 := cc 8 [w85,w0,w1,w2,w3,w4,w172,w19] [q80,q135,q138,q222,q252,q332,q529,q539] [] (by decide +kernel)
def n415 := cc 7 [w0,w1,w2,w194,w3,w4,w5,w173] [q178] [] (by decide +kernel)
def n416 := cc 7 [w85,w0,w1,w195,w3,w4,w5,w173] [q73,q180] [] (by decide +kernel)
def n417 := cc 8 [w85,w0,w1,w2,w3,w4,w5,w173] [q73,q222,q325,q415,q524,q539] [n416,n415] (by decide +kernel)
def v126 : Closed T 8 := rotateClosed n414 auto1 auto1ok
def n418 := cc 9 [w85,w0,w1,w2,w3,w4,w168,w5] [q134,q177,q222,q245,q320,q424,q528] [n417,v126,n413] (by decide +kernel)
def n419 := cc 8 [w87,w1,w2,w3,w168,w24,w5] [q86,q520,q531] [] (by decide +kernel)
def n420 := cc 8 [w0,w88,w1,w2,w3,w168,w24,w5] [q98,q520,q537] [] (by decide +kernel)
def n421 := cc 8 [w91,w0,w1,w2,w3,w168,w24,w5] [q175,q321,q500,q520] [] (by decide +kernel)
def n422 := cc 8 [w0,w1,w2,w90,w3,w168,w24,w5] [q154,q321,q417,q520] [] (by decide +kernel)
def n423 := cc 8 [w0,w1,w2,w3,w4,w30,w173] [q80,q135,q165,q181,q229,q248,q452] [n372] (by decide +kernel)
def n424 := cc 8 [w0,w1,w2,w3,w4,w172,w31] [q80,q103,q134,q165,q452] [n374] (by decide +kernel)
def n425 := cc 8 [w33,w0,w1,w2,w3,w168,w5] [q82,q134,q172,q277,q422,q467] [n375] (by decide +kernel)
def v127 : Closed T 8 := rotateClosed n393 auto1 auto1ok
def v128 : Closed T 8 := rotateClosed n421 auto1 auto1ok
def v129 : Closed T 8 := rotateClosed n425 auto1 auto1ok
def v130 : Closed T 8 := rotateClosed n419 auto1 auto1ok
def v131 : Closed T 8 := rotateClosed n420 auto1 auto1ok
def v132 : Closed T 8 := rotateClosed n422 auto1 auto1ok
def n426 := cc 9 [w0,w1,w2,w3,w4,w172,w30] [q134,q187,q251,q484,q519] [v127,v128,v129,v130,n376,v131,v132,n424,n423] (by decide +kernel)
def n427 := cc 6 [w197,w1,w196,w2,w3,w4,w172] [] [] (by decide +kernel)
def n428 := cc 6 [w1,w196,w2,w3,w172,w19] [q102,q198,q221,q534] [] (by decide +kernel)
def n429 := cc 7 [w1,w196,w2,w3,w4,w5,w172] [q98,q139,q246,q534] [n427,n428] (by decide +kernel)
def n430 := cc 7 [w0,w88,w1,w2,w3,w172,w19] [q252,q529,q534] [n428] (by decide +kernel)
def n431 := cc 8 [w0,w88,w1,w2,w3,w4,w5,w172] [q80,q139,q210,q251,q534] [n430,n429] (by decide +kernel)
def v133 : Closed T 7 := rotateClosed n430 auto1 auto1ok
def n432 := cc 8 [w0,w1,w2,w3,w168,w30,w19] [q108,q138,q457,q524,q528] [v6,n380,v133] (by decide +kernel)
def n433 := cc 8 [w198,w0,w1,w2,w3,w4,w5] [q0,q209,q293,q531] [] (by decide +kernel)
def v134 : Closed T 8 := rotateClosed n18 auto1 auto1ok
def v135 : Closed T 8 := rotateClosed n433 auto1 auto1ok
def v136 : Closed T 8 := rotateClosed n431 auto1 auto1ok
def v137 : Closed T 8 := rotateClosed n424 auto1 auto1ok
def n434 := cc 9 [w0,w1,w2,w3,w4,w168,w5,w30] [q107,q138,q187,q320,q348,q457,q524] [v134,v135,n381,v136,n188,v137,n423,n432] (by decide +kernel)
def n435 := cc 8 [w0,w1,w2,w3,w4,w200,w172] [q80,q165,q251] [] (by decide +kernel)
def n436 := cc 8 [w0,w1,w2,w3,w4,w201,w5] [q0,q73,q209,q245,q293] [] (by decide +kernel)
def v138 : Closed T 8 := rotateClosed n435 auto1 auto1ok
def n437 := cc 9 [w94,w0,w1,w2,w3,w4,w168,w5] [q29,q61,q172,q187,q245,q320,q369] [n436,v138] (by decide +kernel)
def n438 := cc 9 [w91,w0,w1,w2,w3,w4,w168,w5] [q175,q187,q274,q320,q499] [n185,n421] (by decide +kernel)
def n439 := cc 8 [w202,w1,w2,w3,w4,w172,w19] [q86,q529,q536,q539] [] (by decide +kernel)
def n440 := cc 8 [w0,w62,w1,w2,w3,w4,w172,w19] [q80,q114,q252,q524,q529,q539] [] (by decide +kernel)
def n441 := cc 8 [w0,w1,w203,w2,w3,w4,w172,w19] [q159,q181,q252,q332,q491,q529] [] (by decide +kernel)
def n442 := cc 8 [w34,w0,w1,w2,w3,w4,w172] [q117,q134,q181,q225,q483] [n384] (by decide +kernel)
def n443 := cc 8 [w34,w0,w1,w2,w3,w4,w172,w19] [q32,q80,q138,q332,q529,q536] [] (by decide +kernel)
def n444 := cc 8 [w0,w1,w2,w122,w3,w4,w172,w19] [q80,q161,q252,q332,q517,q524,q529] [] (by decide +kernel)
def v139 : Closed T 8 := rotateClosed n394 auto1 auto1ok
def v140 : Closed T 8 := rotateClosed n432 auto1 auto1ok
def n445 := cc 9 [w0,w1,w2,w3,w4,w172,w19] [q80,q114,q138,q187,q484] [n19,v139,n346,n414,n442,n443,n439,n337,n385,n440,n406,n441,n444,n424,n187,v140] (by decide +kernel)
def n446 := cc 8 [w202,w1,w2,w3,w4,w5,w173] [q73,q80,q138,q536,q539] [] (by decide +kernel)
def n447 := cc 8 [w0,w174,w1,w2,w3,w4,w5] [q114,q134,q151,q198,q229,q291] [] (by decide +kernel)
def n448 := cc 7 [w175,w0,w174,w1,w2,w3,w4,w5] [q134,q248,q390] [] (by decide +kernel)
def n449 := cc 8 [w0,w174,w1,w2,w3,w4,w5,w173] [q73,q80,q114,q151,q198,q248,q325,q449,q524] [n448,n340,n388] (by decide +kernel)
def n450 := cc 8 [w0,w1,w195,w2,w3,w4,w5,w173] [q73,q80,q181,q203,q248,q325,q451,q546] [n416] (by decide +kernel)
def n451 := cc 8 [w175,w0,w1,w2,w3,w4,w5] [q117,q134,q181,q225,q291,q293,q454] [n342,n390,n409] (by decide +kernel)
def n452 := cc 7 [w0,w204,w1,w2,w3,w4,w5,w173] [q115,q117,q163,q207,q390,q536] [] (by decide +kernel)
def n453 := cc 7 [w175,w0,w1,w2,w205,w3,w4,w5] [q31,q134,q248,q293,q455] [] (by decide +kernel)
def n454 := cc 8 [w175,w0,w1,w2,w3,w4,w5,w173] [q73,q80,q138,q248,q325,q454,q524] [n343,n448,n410,n453,n452] (by decide +kernel)
def n455 := cc 8 [w0,w1,w2,w205,w3,w4,w5,w173] [q73,q80,q205,q248,q325,q448,q524,q546] [n453] (by decide +kernel)
def v141 : Closed T 8 := rotateClosed n423 auto1 auto1ok
def n456 := cc 9 [w0,w1,w2,w3,w4,w5,w173] [q73,q114,q138,q187,q229,q293,q448] [n16,n347,n417,n451,n454,n446,n344,n391,n447,n449,n411,n450,n455,n188,n423,v141] (by decide +kernel)
def v142 : Closed T 9 := rotateClosed n426 auto1 auto1ok
def v143 : Closed T 9 := rotateClosed n445 auto1 auto1ok
def n457 := cc 10 [w0,w1,w2,w3,w4,w168,w5] [q86,q138,q187,q229,q293,q424] [v11,n395,n437,n438,n348,n418,n324,n345,n392,n412,n434,n190,n456,v142,v143] (by decide +kernel)
def n458 := cc 9 [w0,w1,w2,w207,w3,w4,w5] [q86,q133,q134,q138,q187,q293,q495] [] (by decide +kernel)
def n459 := cc 9 [w206,w208,w1,w2,w3,w4] [q86,q138,q187,q484] [] (by decide +kernel)
def n460 := cc 8 [w0,w1,w209,w2,w3,w4,w5] [q87,q154,q199,q269,q366] [] (by decide +kernel)
def n461 := cc 8 [w206,w1,w2,w186,w3,w4,w5] [q87,q154,q199,q231,q269,q366] [] (by decide +kernel)
def n462 := cc 9 [w206,w0,w1,w185,w2,w3,w4,w5] [q87,q154,q269,q484] [n461,n460] (by decide +kernel)
def n463 := cc 8 [w210,w0,w1,w2,w3,w4,w5] [q53,q125,q177,q222,q270] [] (by decide +kernel)
def n464 := cc 9 [w206,w85,w0,w1,w2,w3,w4,w5] [q134,q177,q366,q484] [n463] (by decide +kernel)
def n465 := cc 10 [w206,w0,w1,w2,w3,w4,w5] [q86,q138,q187,q229,q293,q484] [n464,n459,n462,n458] (by decide +kernel)
def n466 := cc 8 [w0,w1,w2,w3,w4,w212,w5] [q73,q165,q181,q407,q503] [] (by decide +kernel)
def n467 := cc 8 [w215,w0,w1,w2,w3,w4,w5] [q80,q172,q209,q284,q397,q467] [] (by decide +kernel)
def n468 := cc 8 [w0,w1,w2,w214,w3,w5,w19] [q135,q209,q385,q417,q424,q517] [] (by decide +kernel)
def v144 : Closed T 8 := rotateClosed n466 auto1 auto1ok
def n469 := cc 9 [w0,w1,w2,w214,w3,w4,w5] [q134,q138,q209,q385,q417,q424] [n467,n468,v144] (by decide +kernel)
def n470 := cc 8 [w0,w1,w2,w3,w4,w216,w30] [q80,q135,q165,q181,q229,q282,q393,q457] [] (by decide +kernel)
def n471 := cc 8 [w218,w0,w1,w2,w3,w4,w5] [q73,q181,q225,q413,q516] [] (by decide +kernel)
def n472 := cc 8 [w0,w1,w2,w3,w4,w217,w30] [q135,q165,q229,q400,q420,q484,q517] [] (by decide +kernel)
def v145 : Closed T 8 := rotateClosed n470 auto1 auto1ok
def n473 := cc 9 [w0,w1,w2,w3,w4,w217,w5] [q73,q138,q229,q400,q484,q517] [n471,n472,n466,v145] (by decide +kernel)
def n474 := cc 8 [w0,w219,w1,w2,w3,w4,w30] [q133,q231,q421,q484] [] (by decide +kernel)
def n475 := cc 8 [w213,w0,w1,w2,w3,w5,w31] [q134,q209,q393] [] (by decide +kernel)
def n476 := cc 8 [w33,w213,w0,w1,w2,w3,w5] [q165,q172,q397,q467,q555] [] (by decide +kernel)
def v146 : Closed T 8 := rotateClosed n474 auto1 auto1ok
def v147 : Closed T 8 := rotateClosed n472 auto1 auto1ok
def n477 := cc 9 [w213,w0,w1,w2,w3,w24,w5] [q134,q138,q229,q385,q417,q424] [n476,n475,v146,v147] (by decide +kernel)
def n478 := cc 8 [w220,w0,w1,w2,w3,w4,w5] [q134,q172,q407,q503] [] (by decide +kernel)
def n479 := cc 8 [w213,w0,w1,w2,w3,w30,w19] [q165,q187,q393,q419,q457,q517] [] (by decide +kernel)
def v148 : Closed T 8 := rotateClosed n478 auto1 auto1ok
def n480 := cc 9 [w213,w0,w1,w2,w3,w4,w5,w30] [q187,q393,q419,q457] [n475,n479,v148,v144,n470] (by decide +kernel)
def n481 := cc 8 [w221,w0,w1,w2,w3,w4,w5] [q209,q281,q467] [] (by decide +kernel)
def n482 := cc 8 [w213,w0,w1,w2,w3,w95,w5] [q172,q209,q230,q281,q467] [] (by decide +kernel)
def n483 := cc 9 [w94,w213,w0,w1,w2,w3,w4,w5] [q61,q67,q172,q187,q281,q369,q379] [n482,n481] (by decide +kernel)
def n484 := cc 8 [w34,w213,w0,w1,w2,w3,w5] [q165,q181,q399,q480,q555] [] (by decide +kernel)
def n485 := cc 9 [w213,w0,w1,w2,w3,w5,w19] [q138,q187,q385,q424,q517,q519] [n484,n475,n479,n468] (by decide +kernel)
def v149 : Closed T 9 := rotateClosed n473 auto1 auto1ok
def n486 := cc 10 [w213,w0,w1,w2,w3,w4,w5] [q138,q187,q229,q385,q424] [n483,n480,n477,n485,n469,v149] (by decide +kernel)
def n487 := cc 8 [w0,w1,w137,w2,w3,w222,w4,w5] [q125,q239,q279,q300,q427,q487] [] (by decide +kernel)
def n488 := cc 6 [w0,w1,w2,w3,w170,w169,w19] [q89,q92,q99] [] (by decide +kernel)
def n489 := cc 7 [w0,w1,w2,w3,w4,w170,w5,w169] [q73,q80,q139,q188] [n488] (by decide +kernel)
def n490 := cc 7 [w0,w1,w137,w2,w3,w4,w169,w19] [q133,q141,q287] [n488,n326] (by decide +kernel)
def n491 := cc 7 [w0,w1,w137,w2,w3,w4,w5,w223] [q7,q117,q263,q300,q540] [] (by decide +kernel)
def n492 := cc 7 [w171,w0,w1,w137,w2,w3,w4,w5] [q80,q189,q284] [n327] (by decide +kernel)
def v150 : Closed T 7 := rotateClosed n490 auto1 auto1ok
def v151 : Closed T 7 := rotateClosed n328 auto1 auto1ok
def n493 := cc 8 [w0,w1,w137,w2,w3,w4,w170,w5] [q133,q139,q189,q308,q427,q540] [n492,n491,v150,n489,v151] (by decide +kernel)
def n494 := cc 8 [w224,w0,w1,w2,w3,w4,w5] [q73,q80,q121,q142,q269,q318,q487] [] (by decide +kernel)
def n495 := cc 7 [w225,w0,w1,w137,w2,w3,w4,w5] [q242] [] (by decide +kernel)
def n496 := cc 8 [w0,w1,w137,w2,w3,w4,w41,w5] [q133,q139,q254,q300,q301,q487,q547] [n495] (by decide +kernel)
def n497 := cc 7 [w1,w137,w2,w3,w4,w5,w19,w173] [q139,q188,q261,q517] [] (by decide +kernel)
def n498 := cc 7 [w226,w0,w1,w137,w2,w3,w4,w5] [q248] [] (by decide +kernel)
def n499 := cc 8 [w0,w1,w137,w2,w3,w4,w5,w19] [q73,q80,q133,q139,q188,q261,q300,q354,q427,q487,q517] [n498,n491,n490,v150,n497,n332,n329,v94] (by decide +kernel)
def v152 : Closed T 8 := rotateClosed n494 auto1 auto1ok
def v153 : Closed T 8 := rotateClosed n493 auto1 auto1ok
def v154 : Closed T 8 := rotateClosed n496 auto1 auto1ok
def v155 : Closed T 8 := rotateClosed n335 auto1 auto1ok
def v156 : Closed T 8 := rotateClosed n333 auto1 auto1ok
def n500 := cc 9 [w0,w1,w137,w2,w3,w4,w5] [q0,q86,q133,q139,q188,q229,q300] [n494,v152,n487,n493,v153,n496,v154,n499,n335,v155,n264,n333,v156] (by decide +kernel)
def n501 := cc 8 [w228,w0,w1,w2,w3,w4,w5] [q281,q529,q540] [] (by decide +kernel)
def n502 := cc 8 [w0,w1,w2,w3,w4,w176,w112] [q229,q348,q349,q528] [] (by decide +kernel)
def n503 := cc 8 [w0,w1,w2,w3,w4,w176,w19] [q138,q261,q486,q528] [] (by decide +kernel)
def n504 := cc 8 [w0,w1,w2,w3,w4,w5,w229] [q73,q261,q293,q428,q528] [] (by decide +kernel)
def n505 := cc 8 [w230,w0,w1,w2,w3,w4,w5] [q80,q275,q346,q397,q488,q520] [] (by decide +kernel)
def v157 : Closed T 8 := rotateClosed n502 auto1 auto1ok
def v158 : Closed T 8 := rotateClosed n503 auto1 auto1ok
def n506 := cc 9 [w0,w1,w2,w3,w4,w227,w5] [q187,q229,q334,q385,q426,q529] [n505,n501,n335,n504,v96,v157,v158] (by decide +kernel)
def n507 := cc 9 [w0,w136,w231,w3,w4,w5] [q86,q229,q293,q385] [] (by decide +kernel)
def n508 := cc 8 [w232,w0,w136,w1,w2,w3,w4,w5] [q139,q257,q379,q486,q529,q547] [] (by decide +kernel)
def n509 := cc 8 [w233,w0,w1,w2,w3,w4,w5] [q86,q254,q291,q383,q398,q486,q547] [] (by decide +kernel)
def n510 := cc 9 [w0,w136,w1,w2,w3,w4,w41,w5] [q110,q254,q293,q294,q385,q486] [n509,n508,n496,v157] (by decide +kernel)
def n511 := cc 7 [w178,w0,w1,w2,w3,w4,w5,w19] [q115,q143,q187] [] (by decide +kernel)
def n512 := cc 7 [w175,w0,w136,w1,w3,w4,w5,w19] [q73,q80,q114,q182] [] (by decide +kernel)
def n513 := cc 8 [w0,w136,w1,w2,w3,w4,w5,w19,w173] [q73,q80,q139,q188,q261,q533,q536] [n512,n511,n497] (by decide +kernel)
def n514 := cc 8 [w202,w0,w136,w1,w2,w3,w4,w5] [q4,q46,q114,q263,q359,q528,q529,q536] [] (by decide +kernel)
def n515 := cc 7 [w0,w234,w1,w2,w3,w4,w5] [q0,q103,q117,q293,q517] [] (by decide +kernel)
def v159 : Closed T 7 := rotateClosed n336 auto1 auto1ok
def n516 := cc 8 [w177,w0,w1,w2,w3,w4,w5] [q86,q261,q360,q431,q489,q517] [n336,v159,n515] (by decide +kernel)
def n517 := cc 9 [w0,w136,w1,w2,w3,w4,w5,w19] [q73,q188,q261,q354,q385,q400,q426,q486,q536] [n516,n514,n513,n344,n337,v95,n499,n504,n503,v158] (by decide +kernel)
def v160 : Closed T 9 := rotateClosed n345 auto1 auto1ok
def v161 : Closed T 9 := rotateClosed n510 auto1 auto1ok
def v162 : Closed T 9 := rotateClosed n506 auto1 auto1ok
def n518 := cc 10 [w0,w136,w1,w2,w3,w4,w5] [q0,q86,q229,q293,q385,q400] [n267,n345,v160,n510,v161,n517,n507,n500,n506,v162] (by decide +kernel)
def n519 := cc 9 [w0,w1,w2,w235,w4,w5] [q86,q229,q293,q385] [] (by decide +kernel)
def n520 := cc 9 [w236,w0,w1,w2,w4,w5] [q0,q86,q229,q385] [] (by decide +kernel)
def n521 := cc 10 [w0,w1,w2,w231,w3,w4,w5] [q86,q229,q293,q385,q400] [n520,n507,n519] (by decide +kernel)
def n522 := cc 8 [w0,w237,w1,w2,w3,w4,w5] [q0,q213,q285,q293,q524] [] (by decide +kernel)
def n523 := cc 8 [w26,w0,w238,w2,w3,w4,w5] [q80,q229,q291,q400,q550] [] (by decide +kernel)
def n524 := cc 8 [w0,w1,w2,w3,w4,w239,w5] [q73,q412,q524] [] (by decide +kernel)
def n525 := cc 8 [w240,w0,w1,w2,w3,w4,w5] [q73,q261,q293,q407,q462,q549] [] (by decide +kernel)
def n526 := cc 8 [w26,w0,w1,w2,w3,w4,w19] [q80,q393,q506,q524] [] (by decide +kernel)
def n527 := cc 9 [w26,w0,w1,w2,w3,w4,w5] [q138,q229,q348,q400,q506,q524] [n525,n11,n21,n523,n526,n522,n524] (by decide +kernel)
def n528 := cc 8 [w241,w0,w1,w2,w3,w4,w5] [q134,q254,q506] [] (by decide +kernel)
def n529 := cc 8 [w25,w232,w0,w1,w2,w3,w4,w5] [q137,q168,q257,q506,q547] [] (by decide +kernel)
def n530 := cc 9 [w25,w0,w1,w2,w3,w4,w41,w5] [q86,q254,q291,q293,q385,q506] [n528,n529] (by decide +kernel)
def n531 := cc 8 [w242,w0,w1,w2,w3,w4,w5] [q0,q134,q293,q399,q413] [] (by decide +kernel)
def n532 := cc 8 [w25,w0,w1,w2,w3,w4,w5,w19,w173] [q73,q80,q168,q213,q261,q419,q536] [] (by decide +kernel)
def n533 := cc 8 [w25,w202,w0,w1,w2,w3,w4,w5] [q54,q263,q293,q524,q536] [] (by decide +kernel)
def v163 : Closed T 8 := rotateClosed n526 auto1 auto1ok
def n534 := cc 9 [w25,w0,w1,w2,w3,w4,w5,w19] [q73,q213,q261,q354,q385,q400,q460,q506,q536] [n525,n526,v163,n12,n531,n22,n533,n532,n347,n346,v97] (by decide +kernel)
def v164 : Closed T 9 := rotateClosed n527 auto1 auto1ok
def v165 : Closed T 9 := rotateClosed n348 auto1 auto1ok
def v166 : Closed T 9 := rotateClosed n530 auto1 auto1ok
def n535 := cc 10 [w25,w0,w1,w2,w3,w4,w5] [q0,q86,q229,q293,q385,q400] [n527,v164,n13,n23,n270,n348,v165,n530,v166,n534] (by decide +kernel)
def n536 := cc 10 [w243,w0,w1,w2,w3,w4,w5] [q86,q229,q293,q385,q400] [] (by decide +kernel)
def n537 := cc 6 [w0,w1,w74,w3,w4,w65,w30] [q88,q90,q95] [] (by decide +kernel)
def v167 : Closed T 6 := rotateClosed n537 auto1 auto1ok
def n538 := cc 7 [w0,w1,w2,w74,w3,w4,w66,w5] [q73,q110,q134,q144,q239] [v167] (by decide +kernel)
def n539 := cc 7 [w0,w1,w64,w74,w3,w4,w24,w5] [q136,q145,q376] [v167,v99] (by decide +kernel)
def n540 := cc 6 [w245,w0,w1,w64,w2,w3,w4] [] [] (by decide +kernel)
def n541 := cc 7 [w0,w1,w64,w2,w3,w4,w244,w5] [q13,q104,q191,q345] [n540] (by decide +kernel)
def n542 := cc 7 [w180,w0,w1,w64,w2,w3,w4,w5] [q80,q194,q378] [n350] (by decide +kernel)
def v168 : Closed T 7 := rotateClosed n542 auto1 auto1ok
def v169 : Closed T 7 := rotateClosed n541 auto1 auto1ok
def v170 : Closed T 7 := rotateClosed n539 auto1 auto1ok
def v171 : Closed T 7 := rotateClosed n538 auto1 auto1ok
def v172 : Closed T 7 := rotateClosed n351 auto1 auto1ok
def n543 := cc 8 [w0,w1,w64,w2,w74,w3,w4,w5] [q136,q145,q194,q239,q546] [n542,v168,n541,v169,n539,v170,n538,v171,n351,v172] (by decide +kernel)
def n544 := cc 8 [w246,w0,w1,w2,w3,w4,w5] [q80,q125,q187,q363,q419] [] (by decide +kernel)
def n545 := cc 6 [w0,w1,w2,w3,w66,w65,w19] [q91,q93,q111] [] (by decide +kernel)
def n546 := cc 7 [w0,w1,w2,w3,w4,w66,w5,w65] [q73,q80,q144,q191] [n545] (by decide +kernel)
def n547 := cc 7 [w0,w1,w64,w2,w3,w4,w65,w30] [q136,q243,q381] [n537,n82] (by decide +kernel)
def n548 := cc 7 [w67,w0,w1,w64,w2,w3,w4,w5] [q134,q242,q319] [n83] (by decide +kernel)
def n549 := cc 7 [w0,w1,w64,w2,w3,w4,w65,w19] [q136,q146,q382] [n545,n352] (by decide +kernel)
def n550 := cc 6 [w248,w0,w1,w64,w3,w4,w5] [] [] (by decide +kernel)
def n551 := cc 7 [w0,w1,w64,w2,w3,w4,w5,w247] [q13,q118,q239,q359] [n550] (by decide +kernel)
def n552 := cc 7 [w181,w0,w1,w64,w2,w3,w4,w5] [q80,q195,q380] [n353] (by decide +kernel)
def v173 : Closed T 7 := rotateClosed n547 auto1 auto1ok
def v174 : Closed T 7 := rotateClosed n549 auto1 auto1ok
def v175 : Closed T 7 := rotateClosed n354 auto1 auto1ok
def n553 := cc 8 [w0,w1,w64,w2,w3,w4,w66,w5] [q136,q144,q195,q242,q540] [n552,n548,n541,n551,v173,v174,n538,n546,n84,v175] (by decide +kernel)
def n554 := cc 8 [w249,w0,w1,w2,w3,w4,w5] [q124,q134,q229,q366,q519] [] (by decide +kernel)
def n555 := cc 7 [w1,w64,w2,w3,w4,w24,w59,w5] [q144,q268,q334,q417,q540] [] (by decide +kernel)
def n556 := cc 7 [w250,w0,w1,w64,w2,w3,w4,w5] [q308] [] (by decide +kernel)
def n557 := cc 7 [w0,w1,w64,w2,w3,w4,w30,w19] [q76,q135,q144,q239,q420,q517] [n355,n90,n359,n85] (by decide +kernel)
def n558 := cc 6 [w251,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n559 := cc 7 [w0,w1,w64,w2,w3,w4,w5,w31] [q73,q80,q134,q136,q165,q209,q261] [n558,n91,n356,v102,n86] (by decide +kernel)
def n560 := cc 6 [w252,w1,w64,w2,w3,w4,w5] [q80] [] (by decide +kernel)
def n561 := cc 7 [w33,w0,w1,w64,w2,w3,w4,w5] [q73,q80,q86,q172,q275,q421] [n357,n87,n560] (by decide +kernel)
def v176 : Closed T 7 := rotateClosed n557 auto1 auto1ok
def v177 : Closed T 7 := rotateClosed n360 auto1 auto1ok
def n562 := cc 8 [w0,w1,w64,w2,w3,w4,w24,w5] [q73,q134,q136,q144,q191,q209,q239,q334,q417,q519] [n561,n556,n541,n559,v173,v176,n539,v177,n555,n93,v106,n88] (by decide +kernel)
def n563 := cc 7 [w1,w64,w2,w3,w4,w5,w19,w173] [q144,q191,q354,q517,q540] [] (by decide +kernel)
def n564 := cc 7 [w253,w0,w1,w64,w2,w3,w4,w5] [q325] [] (by decide +kernel)
def n565 := cc 6 [w254,w1,w64,w2,w3,w4,w5] [q134] [] (by decide +kernel)
def n566 := cc 6 [w0,w1,w255,w2,w3,w4,w5] [q73] [] (by decide +kernel)
def v178 : Closed T 6 := rotateClosed n361 auto1 auto1ok
def n567 := cc 7 [w34,w0,w1,w64,w2,w3,w4,w5] [q13,q73,q80,q134,q136,q181,q225,q261] [n361,v178,n566,n565] (by decide +kernel)
def n568 := cc 8 [w0,w1,w64,w2,w3,w4,w5,w19] [q73,q80,q136,q144,q191,q239,q261,q354,q419,q517] [n567,n564,n551,n559,n549,v174,n557,v176,n98,n563,n365,n362,v107] (by decide +kernel)
def v179 : Closed T 8 := rotateClosed n554 auto1 auto1ok
def v180 : Closed T 8 := rotateClosed n553 auto1 auto1ok
def v181 : Closed T 8 := rotateClosed n562 auto1 auto1ok
def v182 : Closed T 8 := rotateClosed n368 auto1 auto1ok
def v183 : Closed T 8 := rotateClosed n366 auto1 auto1ok
def n569 := cc 9 [w0,w1,w64,w2,w3,w4,w5] [q86,q136,q144,q191,q239,q293] [n554,v179,n544,n543,n553,v180,n562,v181,n568,n101,n368,v182,n99,n366,v183] (by decide +kernel)
def n570 := cc 8 [w256,w0,w1,w2,w3,w4,w5] [q373,q524,q546] [] (by decide +kernel)
def n571 := cc 7 [w0,w88,w28,w3,w4,w5] [q134,q291,q341,q429] [] (by decide +kernel)
def n572 := cc 8 [w0,w1,w28,w3,w4,w24,w5] [q134,q334,q391,q421] [n571] (by decide +kernel)
def n573 := cc 8 [w0,w1,w2,w3,w4,w257,w5] [q73,q80,q134,q187,q336,q391] [] (by decide +kernel)
def n574 := cc 8 [w258,w0,w1,w2,w3,w4,w5] [q80,q369,q525] [] (by decide +kernel)
def n575 := cc 8 [w0,w1,w2,w28,w3,w4,w5,w19] [q73,q261,q354,q421,q517,q524] [] (by decide +kernel)
def v184 : Closed T 8 := rotateClosed n574 auto1 auto1ok
def v185 : Closed T 8 := rotateClosed n573 auto1 auto1ok
def v186 : Closed T 8 := rotateClosed n572 auto1 auto1ok
def n576 := cc 9 [w0,w1,w2,w28,w3,w4,w5] [q138,q229,q293,q406,q524,q525] [n574,v184,n24,n570,n575,n271,n101,n573,v185,n100,n572,v186] (by decide +kernel)
def n577 := cc 8 [w259,w0,w1,w2,w3,w4,w5] [q379,q529,q540] [] (by decide +kernel)
def n578 := cc 8 [w0,w1,w2,w3,w4,w182,w30] [q259,q293,q350,q528] [] (by decide +kernel)
def n579 := cc 8 [w260,w0,w1,w2,w3,w4,w5] [q87,q134,q398,q421] [] (by decide +kernel)
def n580 := cc 7 [w0,w1,w2,w3,w29,w30,w19] [q255,q351,q420,q529] [] (by decide +kernel)
def n581 := cc 8 [w0,w1,w2,w3,w4,w29,w5,w30] [q80,q254,q348,q393,q420,q529] [n580] (by decide +kernel)
def n582 := cc 7 [w34,w0,w1,w2,w3,w4,w182] [q360,q528] [] (by decide +kernel)
def v187 : Closed T 7 := rotateClosed n580 auto1 auto1ok
def n583 := cc 8 [w0,w1,w2,w3,w4,w182,w19] [q138,q354,q357,q419,q528] [n582,v187] (by decide +kernel)
def n584 := cc 8 [w0,w1,w2,w3,w4,w5,w261] [q0,q73,q134,q229,q354,q410,q528] [] (by decide +kernel)
def n585 := cc 8 [w262,w0,w1,w2,w3,w4,w5] [q372,q520,q528] [] (by decide +kernel)
def v188 : Closed T 8 := rotateClosed n578 auto1 auto1ok
def v189 : Closed T 8 := rotateClosed n583 auto1 auto1ok
def n586 := cc 9 [w0,w1,w2,w3,w4,w29,w5] [q187,q254,q293,q424,q529,q533] [n585,n579,n25,n577,n109,n581,n368,n573,n584,v120,v188,v189] (by decide +kernel)
def n587 := cc 8 [w263,w0,w2,w4,w5] [q86,q229,q293,q385] [] (by decide +kernel)
def n588 := cc 9 [w0,w27,w2,w81,w4,w5] [q86,q229,q293,q385] [n587] (by decide +kernel)
def n589 := cc 7 [w79,w0,w1,w2,w3,w4,w24,w5] [q34,q149,q266] [] (by decide +kernel)
def n590 := cc 8 [w0,w27,w1,w2,w3,w4,w24,w59,w5] [q73,q134,q144,q267,q334,q531,q533,q537] [n589,n555] (by decide +kernel)
def n591 := cc 6 [w265,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n592 := cc 7 [w0,w27,w1,w2,w3,w4,w264,w5] [q0,q73,q134,q209,q286,q293,q394,q519] [n591] (by decide +kernel)
def n593 := cc 6 [w77,w87,w0,w1,w2,w3,w5] [] [] (by decide +kernel)
def n594 := cc 7 [w87,w0,w27,w1,w2,w3,w5,w19] [q43,q135,q191,q209,q283,q417,q528,q545] [n593] (by decide +kernel)
def v190 : Closed T 7 := rotateClosed n592 auto1 auto1ok
def n595 := cc 8 [w87,w0,w27,w1,w2,w3,w4,w5] [q98,q134,q191,q291,q345,q528,q529,q531] [n594,v190] (by decide +kernel)
def n596 := cc 6 [w0,w266,w1,w2,w3,w5,w19] [q187] [] (by decide +kernel)
def n597 := cc 7 [w0,w266,w1,w2,w3,w4,w5] [q0,q80,q104,q187,q417] [n596] (by decide +kernel)
def n598 := cc 6 [w76,w202,w0,w1,w2,w3,w5] [] [] (by decide +kernel)
def n599 := cc 7 [w76,w0,w1,w2,w3,w5,w19] [q39,q192,q409,q417] [n598,n369,n377,n110,n596] (by decide +kernel)
def n600 := cc 8 [w76,w0,w1,w2,w3,w4,w5] [q80,q104,q334,q409,q417] [n378,n370,n599,n111,n597] (by decide +kernel)
def n601 := cc 7 [w0,w27,w196,w2,w3,w4,w5] [q134,q308,q309,q534] [] (by decide +kernel)
def n602 := cc 8 [w0,w27,w88,w2,w3,w4,w5] [q229,q334,q337,q426,q534] [n601,n571] (by decide +kernel)
def v191 : Closed T 6 := rotateClosed n598 auto1 auto1ok
def n603 := cc 7 [w202,w0,w27,w1,w2,w3,w4,w30] [q135,q263,q517,q528,q529] [v191] (by decide +kernel)
def n604 := cc 6 [w0,w267,w1,w2,w3,w4,w30] [q229] [] (by decide +kernel)
def v192 : Closed T 6 := rotateClosed n593 auto1 auto1ok
def n605 := cc 7 [w77,w0,w1,w2,w3,w4,w30] [q234,q264,q517] [v192,n122,n379,n112,n604] (by decide +kernel)
def v193 : Closed T 7 := rotateClosed n599 auto1 auto1ok
def v194 : Closed T 7 := rotateClosed n594 auto1 auto1ok
def n606 := cc 8 [w0,w27,w1,w2,w3,w4,w30,w19] [q80,q108,q261,q351,q419,q457,q533,q538,q539] [v193,n605,n26,v194,n603,n372,n123,n380,n113,n557,n580] (by decide +kernel)
def n607 := cc 7 [w32,w0,w27,w1,w2,w3,w4,w5] [q0,q73,q80,q134,q165,q209,q263,q293,q542] [n558,n44,n27,n301] (by decide +kernel)
def n608 := cc 6 [w0,w268,w1,w2,w3,w4,w5] [q0,q86] [] (by decide +kernel)
def v195 : Closed T 6 := rotateClosed n373 auto1 auto1ok
def n609 := cc 7 [w78,w0,w1,w2,w3,w4,w5] [q0,q86,q264,q395,q409] [n558,n373,v195,n114,n608] (by decide +kernel)
def n610 := cc 7 [w78,w0,w1,w2,w3,w4,w5,w31] [q80,q165,q262,q552] [] (by decide +kernel)
def n611 := cc 7 [w0,w27,w269,w2,w3,w4,w5,w31] [q73,q134,q342,q343,q458] [] (by decide +kernel)
def n612 := cc 8 [w0,w27,w1,w2,w3,w4,w5,w31] [q73,q80,q86,q134,q261,q291,q342,q407,q457,q531,q532,q536] [n609,n610,n28,n607,n611,n126,n374,v113,n115,n559] (by decide +kernel)
def n613 := cc 7 [w78,w0,w1,w2,w3,w4,w24,w5] [q34,q38,q209,q258,q264,q392] [] (by decide +kernel)
def n614 := cc 8 [w0,w27,w1,w2,w3,w4,w24,w5,w31] [q73,q134,q209,q290,q342,q399,q457,q519,q531,q533,q537] [n613] (by decide +kernel)
def n615 := cc 7 [w0,w252,w27,w1,w2,w3,w4,w5] [q276,q421,q520,q528] [n560] (by decide +kernel)
def n616 := cc 8 [w33,w0,w27,w1,w2,w3,w4,w5] [q105,q346,q407,q421,q467,q520,q531] [n29,n375,n116,n561,n615] (by decide +kernel)
def v196 : Closed T 8 := rotateClosed n381 auto1 auto1ok
def v197 : Closed T 8 := rotateClosed n606 auto1 auto1ok
def v198 : Closed T 8 := rotateClosed n581 auto1 auto1ok
def n617 := cc 9 [w0,w27,w1,w2,w3,w4,w24,w5] [q73,q98,q229,q334,q407,q424,q537] [n616,n600,n30,n595,n602,v196,n590,n614,n128,n612,v118,v197,n117,n562,v198,n573,v188,n572] (by decide +kernel)
def n618 := cc 7 [w183,w0,w1,w2,w3,w4,w5,w19] [q44,q150,q187] [] (by decide +kernel)
def n619 := cc 8 [w0,w27,w1,w2,w3,w4,w5,w19,w173] [q73,q80,q144,q191,q354,q533,q536,q539] [n618,n563] (by decide +kernel)
def n620 := cc 6 [w271,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n621 := cc 7 [w0,w27,w1,w2,w270,w3,w4,w5] [q134,q263,q291,q293,q528,q529] [n620] (by decide +kernel)
def v199 : Closed T 7 := rotateClosed n603 auto1 auto1ok
def n622 := cc 8 [w202,w0,w27,w1,w2,w3,w4,w5] [q114,q263,q291,q359,q524,q528,q529,q536] [n603,v199,n621] (by decide +kernel)
def v200 : Closed T 6 := rotateClosed n604 auto1 auto1ok
def n623 := cc 7 [w0,w267,w1,w2,w3,w4,w5] [q0,q118,q134,q229,q517] [n604,v200] (by decide +kernel)
def v201 : Closed T 7 := rotateClosed n382 auto1 auto1ok
def v202 : Closed T 7 := rotateClosed n605 auto1 auto1ok
def n624 := cc 8 [w77,w0,w1,w2,w3,w4,w5] [q118,q134,q264,q354,q517] [n134,n382,v201,n605,v202,n623] (by decide +kernel)
def n625 := cc 7 [w0,w27,w63,w2,w3,w4,w5] [q193,q325,q326,q327,q433,q542] [n135] (by decide +kernel)
def n626 := cc 8 [w0,w27,w62,w2,w3,w4,w5] [q114,q261,q291,q354,q355,q357,q400,q432] [n136,n625] (by decide +kernel)
def n627 := cc 7 [w78,w0,w1,w2,w3,w4,w5,w19] [q44,q47,q261,q395,q396,q411] [] (by decide +kernel)
def n628 := cc 8 [w0,w27,w1,w2,w3,w4,w5,w19,w31] [q73,q80,q261,q354,q393,q397,q412,q419,q533,q536,q539] [n627] (by decide +kernel)
def n629 := cc 7 [w0,w254,w27,w1,w2,w3,w4,w5] [q0,q117,q134,q293,q528,q529] [n566,n565] (by decide +kernel)
def n630 := cc 6 [w272,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def v203 : Closed T 6 := rotateClosed n383 auto1 auto1ok
def n631 := cc 7 [w0,w1,w35,w2,w3,w4,w5] [q148,q256,q360,q414,q482] [n31,n630,n383,v203,n566] (by decide +kernel)
def v204 : Closed T 7 := rotateClosed n384 auto1 auto1ok
def v205 : Closed T 7 := rotateClosed n582 auto1 auto1ok
def n632 := cc 8 [w34,w0,w27,w1,w2,w3,w4,w5] [q117,q261,q360,q480,q536] [n32,n384,v204,n567,n582,v205,n629,n631] (by decide +kernel)
def n633 := cc 9 [w0,w27,w1,w2,w3,w4,w5,w19] [q73,q191,q261,q354,q400,q424,q539] [n632,n624,n33,n622,n626,n137,n619,n628,n391,n612,n385,v119,n606,v197,n568,n575,n584,n583,v189] (by decide +kernel)
def v206 : Closed T 9 := rotateClosed n392 auto1 auto1ok
def v207 : Closed T 9 := rotateClosed n617 auto1 auto1ok
def v208 : Closed T 9 := rotateClosed n586 auto1 auto1ok
def n634 := cc 10 [w0,w27,w1,w2,w3,w4,w5] [q86,q229,q293,q385,q400] [n34,n138,n392,v206,n617,v207,n633,n272,n588,n569,n576,n586,v208] (by decide +kernel)
def n635 := cc 10 [w0,w1,w2,w3,w81,w4,w5] [q0,q86,q229,q385,q400] [n588] (by decide +kernel)
def n636 := cc 9 [w82,w273,w0,w2,w4,w5] [q0,q86,q229,q385] [n587] (by decide +kernel)
def n637 := cc 10 [w82,w0,w1,w2,w3,w4,w5] [q86,q229,q293,q424,q484] [n636,n139] (by decide +kernel)
def n638 := cc 10 [w273,w0,w1,w2,w3,w4,w5] [q86,q229,q293,q385,q400] [n636] (by decide +kernel)
def n639 := cc 7 [w0,w1,w275,w3,w30,w19] [q165,q261,q407,q457] [] (by decide +kernel)
def n640 := cc 8 [w0,w1,w275,w3,w4,w5,w30] [q165,q407,q457,q555] [n639] (by decide +kernel)
def n641 := cc 8 [w0,w1,w2,w3,w4,w278,w5] [q0,q73,q209,q261,q293] [] (by decide +kernel)
def n642 := cc 8 [w279,w0,w1,w2,w3,w4,w5] [q80,q172,q407,q467] [] (by decide +kernel)
def n643 := cc 8 [w0,w1,w2,w275,w3,w5,w19] [q138,q261,q407,q417,q424,q552] [n639] (by decide +kernel)
def v209 : Closed T 8 := rotateClosed n641 auto1 auto1ok
def n644 := cc 9 [w0,w1,w2,w275,w3,w4,w5] [q134,q138,q229,q407,q417,q424] [n642,n643,v209,n640] (by decide +kernel)
def n645 := cc 8 [w0,w1,w2,w3,w4,w280,w30] [q10,q80,q165,q261] [] (by decide +kernel)
def n646 := cc 8 [w282,w0,w1,w2,w3,w4,w5] [q73,q225,q261,q360,q461] [] (by decide +kernel)
def v210 : Closed T 8 := rotateClosed n645 auto1 auto1ok
def n647 := cc 9 [w0,w1,w2,w3,w4,w281,w5] [q73,q187,q261,q385,q484,q517] [n646,n641,v210] (by decide +kernel)
def n648 := cc 8 [w283,w0,w1,w2,w3,w4,w5] [q209,q346,q397,q435] [] (by decide +kernel)
def n649 := cc 8 [w0,w274,w1,w2,w3,w30,w19] [q165,q261,q400,q419,q457] [n639] (by decide +kernel)
def v211 : Closed T 8 := rotateClosed n648 auto1 auto1ok
def n650 := cc 9 [w0,w274,w1,w2,w3,w4,w5,w30] [q165,q229,q400,q419,q457] [v211,n649,v209,n645,n640] (by decide +kernel)
def n651 := cc 9 [w0,w274,w1,w2,w3,w5,w19] [q138,q261,q385,q400,q424,q517,q519] [n649,n643] (by decide +kernel)
def v212 : Closed T 9 := rotateClosed n647 auto1 auto1ok
def n652 := cc 10 [w0,w274,w1,w2,w3,w4,w5] [q138,q229,q385,q400,q424] [n650,n651,n644,v212] (by decide +kernel)
def n653 := cc 10 [w0,w1,w2,w3,w4,w284,w5] [q86,q229,q293,q385,q400] [] (by decide +kernel)
def n654 := cc 8 [w0,w285,w1,w2,w3,w4,w5] [q73,q114,q134,q216,q229,q359,q465,q549] [] (by decide +kernel)
def n655 := cc 8 [w37,w0,w62,w2,w3,w4,w5] [q291,q385,q400,q549] [] (by decide +kernel)
def n656 := cc 8 [w0,w1,w2,w286,w3,w4,w5] [q0,q134,q293,q399,q413] [] (by decide +kernel)
def n657 := cc 9 [w37,w0,w1,w2,w3,w4,w5] [q216,q261,q354,q385,q400,q464,q536,q549] [n525,n16,n35,n655,n140,n654,n656] (by decide +kernel)
def n658 := cc 8 [w287,w0,w1,w2,w3,w4,w5] [q80,q105,q275,q346,q397,q430,q544] [] (by decide +kernel)
def n659 := cc 7 [w36,w87,w0,w1,w2,w3,w19] [q57,q77,q283,q408,q528] [] (by decide +kernel)
def n660 := cc 8 [w36,w87,w0,w1,w2,w3,w4,w5] [q37,q56,q134,q170,q345,q408,q417,q421] [n659] (by decide +kernel)
def n661 := cc 7 [w36,w0,w62,w2,w3,w24,w19] [q58,q517,q528] [] (by decide +kernel)
def n662 := cc 8 [w36,w0,w1,w2,w3,w24,w19] [q261,q340,q407,q417,q464,q525,q528,q536] [n17,n36,n659,n661,n143,n141] (by decide +kernel)
def n663 := cc 9 [w36,w0,w1,w2,w3,w4,w24,w5] [q170,q229,q334,q385,q407,q417,q464,q525] [n525,n18,n658,n37,n660,n144,n393,n662,n142] (by decide +kernel)
def n664 := cc 8 [w36,w0,w62,w2,w3,w4,w19] [q261,q292,q354,q517,q528] [n661] (by decide +kernel)
def n665 := cc 9 [w36,w0,w1,w2,w3,w4,w19] [q261,q354,q385,q400,q484,q528,q536] [n526,n19,n38,n664,n147,n394,n662] (by decide +kernel)
def n666 := cc 10 [w36,w0,w1,w2,w3,w4,w5] [q86,q229,q293,q385,q400,q484] [n657,n527,n20,n39,n148,n395,n663,n665] (by decide +kernel)
def n667 := cc 9 [w0,w1,w2,w3,w4,w289] [q86,q138,q229,q293] [] (by decide +kernel)
def n668 := cc 9 [w0,w291,w1,w2,w3,w5] [q86,q138,q187,q229] [] (by decide +kernel)
def n669 := cc 9 [w36,w290,w0,w2,w3,w4] [] [] (by decide +kernel)
def v213 : Closed T 9 := rotateClosed n669 auto1 auto1ok
def v214 : Closed T 9 := rotateClosed n668 auto1 auto1ok
def n670 := cc 10 [w288,w0,w1,w2,w3,w4,w5] [q86,q138,q229,q293,q400] [v213,v214,n667] (by decide +kernel)
def n671 := cc 6 [w0,w1,w2,w3,w188,w187,w19] [q154,q199] [] (by decide +kernel)
def n672 := cc 7 [w0,w1,w2,w3,w4,w188,w5,w187] [q73,q80,q157,q199] [n671] (by decide +kernel)
def n673 := cc 7 [w0,w1,w2,w186,w3,w4,w187,w19] [q133,q157,q287] [n671,n396] (by decide +kernel)
def n674 := cc 6 [w0,w293,w2,w186,w3,w4,w5] [] [] (by decide +kernel)
def n675 := cc 7 [w0,w1,w2,w186,w3,w4,w5,w292] [q20,q183,q263,q293] [n674] (by decide +kernel)
def n676 := cc 7 [w189,w0,w1,w2,w186,w3,w4,w5] [q80,q200,q284] [n397] (by decide +kernel)
def v215 : Closed T 7 := rotateClosed n673 auto1 auto1ok
def v216 : Closed T 7 := rotateClosed n398 auto1 auto1ok
def n677 := cc 8 [w0,w1,w2,w186,w3,w4,w188,w5] [q133,q154,q200,q320,q547] [n676,n675,v215,n672,v216] (by decide +kernel)
def n678 := cc 8 [w294,w0,w1,w2,w3,w4,w5] [q73,q80,q138,q199,q269,q366] [] (by decide +kernel)
def n679 := cc 7 [w1,w2,w186,w3,w4,w5,w19,w173] [q154,q199,q261,q354,q517] [] (by decide +kernel)
def n680 := cc 7 [w295,w0,w1,w2,w186,w3,w4,w5] [q248] [] (by decide +kernel)
def n681 := cc 8 [w0,w1,w2,w186,w3,w4,w5,w19] [q73,q80,q133,q154,q199,q261,q354,q517] [n680,n675,n673,v215,n679,n401,n399,v123] (by decide +kernel)
def v217 : Closed T 8 := rotateClosed n461 auto1 auto1ok
def v218 : Closed T 8 := rotateClosed n678 auto1 auto1ok
def v219 : Closed T 8 := rotateClosed n677 auto1 auto1ok
def v220 : Closed T 8 := rotateClosed n404 auto1 auto1ok
def v221 : Closed T 8 := rotateClosed n402 auto1 auto1ok
def n682 := cc 9 [w0,w1,w2,w186,w3,w4,w5] [q133,q154,q199,q229,q293] [n461,v217,n678,v218,n677,v219,n681,n404,v220,n402,v221] (by decide +kernel)
def n683 := cc 8 [w297,w0,w1,w2,w3,w4,w5] [q154,q281,q529] [] (by decide +kernel)
def n684 := cc 8 [w0,w1,w2,w3,w4,w190,w19] [q261,q457,q528] [] (by decide +kernel)
def n685 := cc 8 [w0,w1,w2,w3,w4,w5,w298] [q261,q354,q528] [] (by decide +kernel)
def n686 := cc 8 [w299,w0,w1,w2,w3,w4,w5] [q80,q275,q467,q520] [] (by decide +kernel)
def v222 : Closed T 8 := rotateClosed n684 auto1 auto1ok
def n687 := cc 9 [w0,w1,w2,w3,w4,w296,w5] [q187,q229,q424,q529] [n686,n683,n404,n685,v125,v222] (by decide +kernel)
def n688 := cc 9 [w0,w1,w185,w8,w4,w5] [q229,q424,q484] [] (by decide +kernel)
def n689 := cc 7 [w192,w0,w1,w2,w3,w4,w5,w19] [q45,q158,q187] [] (by decide +kernel)
def n690 := cc 7 [w175,w0,w1,w185,w3,w4,w5,w19] [q43,q73,q80,q183] [] (by decide +kernel)
def n691 := cc 8 [w0,w1,w185,w2,w3,w4,w5,w19,w173] [q73,q80,q154,q199,q261,q354,q539] [n690,n689,n679] (by decide +kernel)
def n692 := cc 8 [w202,w0,w1,w185,w2,w3,w4,w5] [q154,q263,q528,q529,q539] [] (by decide +kernel)
def n693 := cc 7 [w0,w300,w1,w2,w3,w4,w5] [q0,q178,q185,q248,q517] [] (by decide +kernel)
def v223 : Closed T 7 := rotateClosed n405 auto1 auto1ok
def n694 := cc 8 [w191,w0,w1,w2,w3,w4,w5] [q86,q261,q354,q517] [n405,v223,n693] (by decide +kernel)
def n695 := cc 9 [w0,w1,w185,w2,w3,w4,w5,w19] [q73,q199,q261,q424,q484,q539] [n694,n692,n691,n411,n406,v124,n681,n685,n684,v222] (by decide +kernel)
def v224 : Closed T 9 := rotateClosed n462 auto1 auto1ok
def v225 : Closed T 9 := rotateClosed n412 auto1 auto1ok
def v226 : Closed T 9 := rotateClosed n687 auto1 auto1ok
def n696 := cc 10 [w0,w1,w185,w2,w3,w4,w5] [q86,q229,q293,q424,q484] [n462,v224,n412,v225,n695,n688,n682,n687,v226] (by decide +kernel)
def n697 := cc 8 [w301,w0,w1,w2,w3,w4,w5] [q94,q279,q374,q425,q485] [] (by decide +kernel)
def n698 := cc 9 [w84,w0,w1,w2,w3,w4,w5] [q94,q134,q279,q293,q424,q484,q546] [n234,n40,n149,n697] (by decide +kernel)
def n699 := cc 8 [w0,w1,w303,w2,w3,w4,w5] [q94,q239,q438,q493,q540] [] (by decide +kernel)
def n700 := cc 8 [w0,w302,w1,w303,w2,w3,w4,w5] [q94,q239,q291,q438,q493] [] (by decide +kernel)
def n701 := cc 9 [w0,w302,w1,w2,w3,w4,w5] [q94,q229,q291,q293,q295,q424,q484] [n40,n700,n699] (by decide +kernel)
def n702 := cc 10 [w0,w1,w2,w3,w8,w4,w5] [q86,q229,q293,q424,q484] [n235,n41,n297,n698,n3,n701,n688,n150] (by decide +kernel)
def n703 := cc 9 [w0,w305,w1,w2,w3,w4,w5] [q229,q424,q484] [] (by decide +kernel)
def n704 := cc 10 [w304,w0,w1,w2,w3,w4,w5] [q86,q229,q424,q484] [n703] (by decide +kernel)
def n705 := cc 8 [w306,w0,w1,w2,w3,w4,w5] [q73,q80,q134,q138,q366] [] (by decide +kernel)
def n706 := cc 8 [w0,w86,w1,w2,w3,w4,w5,w19] [q73,q80,q134,q135,q177,q222,q354,q415,q416,q419,q517] [] (by decide +kernel)
def v227 : Closed T 8 := rotateClosed n705 auto1 auto1ok
def v228 : Closed T 8 := rotateClosed n413 auto1 auto1ok
def n707 := cc 9 [w0,w86,w1,w2,w3,w4,w5] [q0,q86,q134,q177,q222,q293,q415] [n705,v227,n236,n706,n413,v228,n151] (by decide +kernel)
def n708 := cc 8 [w308,w0,w1,w2,w3,w4,w5] [q177,q379,q529] [] (by decide +kernel)
def n709 := cc 8 [w0,w1,w2,w3,w4,w309,w30] [q134,q222,q348,q419] [] (by decide +kernel)
def n710 := cc 8 [w0,w1,w2,w3,w4,w309,w19] [q138,q354,q419,q421,q528] [] (by decide +kernel)
def n711 := cc 8 [w0,w1,w2,w3,w4,w5,w310] [q354,q415,q528] [] (by decide +kernel)
def n712 := cc 8 [w311,w0,w1,w2,w3,w4,w5] [q372,q419,q457,q520] [] (by decide +kernel)
def v229 : Closed T 8 := rotateClosed n709 auto1 auto1ok
def v230 : Closed T 8 := rotateClosed n710 auto1 auto1ok
def n713 := cc 9 [w0,w1,w2,w3,w4,w307,w5] [q187,q254,q293,q419,q424,q529] [n712,n708,n413,n711,v229,v230] (by decide +kernel)
def n714 := cc 9 [w85,w0,w1,w2,w3,w4,w24,w5] [q134,q229,q293,q421,q424] [v229] (by decide +kernel)
def n715 := cc 7 [w0,w1,w2,w313,w3,w4,w5] [q179,q325,q415] [] (by decide +kernel)
def n716 := cc 8 [w0,w1,w2,w312,w3,w4,w5] [q179,q224,q354,q415] [n715] (by decide +kernel)
def n717 := cc 8 [w85,w0,w1,w2,w3,w4,w5,w19,w173] [q73,q80,q177,q222,q419,q537,q539] [] (by decide +kernel)
def n718 := cc 8 [w85,w202,w0,w1,w2,w3,w4,w5] [q135,q177,q359,q415,q539] [] (by decide +kernel)
def n719 := cc 9 [w85,w0,w1,w2,w3,w4,w5,w19] [q73,q222,q261,q354,q419,q421,q424,q484,q539] [n718,n717,n417,n414,v126,n706,n716,n711,n710,v230] (by decide +kernel)
def v231 : Closed T 9 := rotateClosed n464 auto1 auto1ok
def v232 : Closed T 9 := rotateClosed n418 auto1 auto1ok
def v233 : Closed T 9 := rotateClosed n714 auto1 auto1ok
def v234 : Closed T 9 := rotateClosed n713 auto1 auto1ok
def n720 := cc 10 [w85,w0,w1,w2,w3,w4,w5] [q86,q229,q293,q424,q484] [n464,v231,n237,n152,n418,v232,n714,v233,n719,n276,n707,n713,v234] (by decide +kernel)
def n721 := cc 9 [w0,w1,w2,w3,w4,w315] [q138,q229,q424] [] (by decide +kernel)
def n722 := cc 9 [w0,w1,w2,w3,w4,w317,w5] [q187,q229,q484] [] (by decide +kernel)
def n723 := cc 9 [w318,w0,w1,w2,w3,w5] [q138,q187,q229] [] (by decide +kernel)
def n724 := cc 8 [w319,w0,w1,w3,w4] [q187,q229,q555] [] (by decide +kernel)
def n725 := cc 8 [w319,w0,w1,w3,w4,w30] [q187,q229,q484,q555] [] (by decide +kernel)
def n726 := cc 7 [w0,w1,w314,w3,w320,w31] [q160,q238,q437,q552,q555] [] (by decide +kernel)
def n727 := cc 8 [w0,w1,w314,w3,w320,w24,w5] [q73,q172,q204,q237,q436,q552] [n726] (by decide +kernel)
def n728 := cc 8 [w0,w1,w314,w3,w24,w5,w31] [q73,q165,q172,q261,q457,q552] [n726] (by decide +kernel)
def n729 := cc 8 [w33,w0,w1,w314,w3,w24,w5] [q73,q172,q275,q467,q552,q555] [] (by decide +kernel)
def n730 := cc 7 [w0,w1,w322,w3,w24,w5] [q204,q290,q480,q555] [] (by decide +kernel)
def v235 : Closed T 7 := rotateClosed n730 auto1 auto1ok
def n731 := cc 8 [w323,w0,w1,w316,w3,w4,w30] [q80,q160,q275,q437,q552,q555] [v235] (by decide +kernel)
def v236 : Closed T 8 := rotateClosed n731 auto1 auto1ok
def v237 : Closed T 8 := rotateClosed n724 auto1 auto1ok
def v238 : Closed T 8 := rotateClosed n725 auto1 auto1ok
def n732 := cc 9 [w0,w1,w314,w3,w24,w5] [q138,q229,q424] [v236,n729,v237,v238,n727,n728] (by decide +kernel)
def v239 : Closed T 9 := rotateClosed n723 auto1 auto1ok
def v240 : Closed T 9 := rotateClosed n722 auto1 auto1ok
def n733 := cc 10 [w0,w1,w314,w2,w3,w4,w5] [q138,q187,q229,q424] [v239,n732,v240,n721] (by decide +kernel)
def n734 := cc 8 [w0,w88,w1,w2,w3,w4,w59,w5] [q98,q267,q421,q537] [] (by decide +kernel)
def n735 := cc 8 [w0,w68,w1,w2,w3,w4,w24,w5] [q98,q421,q533] [] (by decide +kernel)
def n736 := cc 8 [w0,w1,w2,w90,w3,w4,w59,w5] [q154,q171,q308,q421] [] (by decide +kernel)
def n737 := cc 9 [w0,w1,w2,w3,w4,w24,w59,w5] [q98,q134,q138,q334,q421,q441] [v47,n181,n590,n734,n735,n736] (by decide +kernel)
def n738 := cc 8 [w324,w0,w1,w2,w3,w4,w5] [q285,q293,q515,q524] [] (by decide +kernel)
def n739 := cc 8 [w0,w1,w2,w3,w4,w264,w5] [q103,q134,q165,q209,q293,q459,q540] [n592] (by decide +kernel)
def n740 := cc 8 [w91,w87,w0,w1,w2,w3,w4,w5] [q175,q209,q345,q421,q504] [] (by decide +kernel)
def n741 := cc 8 [w87,w0,w1,w2,w3,w5,w19] [q102,q187,q473,q525,q529,q543] [n659,n594] (by decide +kernel)
def v241 : Closed T 8 := rotateClosed n738 auto1 auto1ok
def v242 : Closed T 8 := rotateClosed n739 auto1 auto1ok
def n742 := cc 9 [w87,w0,w1,w2,w3,w4,w5] [q134,q138,q209,q281,q293,q417,q473] [n433,n660,n740,n42,n595,n741,n164,n181,v241,v242] (by decide +kernel)
def n743 := cc 9 [w87,w0,w1,w2,w3,w4,w24,w5] [q138,q229,q525,q531] [n181,n419,n153] (by decide +kernel)
def n744 := cc 7 [w0,w1,w196,w2,w3,w4,w5,w325] [q80,q543] [] (by decide +kernel)
def n745 := cc 6 [w197,w0,w1,w196,w2,w3,w19] [q101,q540] [] (by decide +kernel)
def n746 := cc 7 [w197,w0,w1,w196,w2,w3,w4,w5] [q80,q210,q540] [n745,n427] (by decide +kernel)
def n747 := cc 7 [w0,w1,w196,w2,w3,w5,w19] [q139,q198,q221,q247,q534] [n745,n428] (by decide +kernel)
def n748 := cc 8 [w0,w1,w196,w2,w3,w4,w5] [q80,q98,q139,q210,q245,q308,q427,q540] [n746,n601,n744,n747,n429] (by decide +kernel)
def n749 := cc 8 [w0,w88,w1,w196,w2,w3,w4,w5] [q98,q139,q534,q549] [] (by decide +kernel)
def n750 := cc 8 [w0,w1,w2,w3,w4,w326,w5] [q73,q189,q261,q275,q342,q393,q488,q540] [] (by decide +kernel)
def n751 := cc 8 [w0,w88,w1,w2,w3,w5,w19] [q139,q221,q261,q529,q534] [n430,n747] (by decide +kernel)
def v243 : Closed T 8 := rotateClosed n523 auto1 auto1ok
def v244 : Closed T 8 := rotateClosed n750 auto1 auto1ok
def n752 := cc 9 [w0,w88,w1,w2,w3,w4,w5] [q0,q98,q187,q229,q334,q385,q534] [v243,n658,n42,n602,n749,n431,n751,n748,v244] (by decide +kernel)
def n753 := cc 8 [w0,w1,w196,w2,w3,w4,w24,w5] [q245,q525,q537] [] (by decide +kernel)
def n754 := cc 8 [w0,w1,w2,w3,w4,w326,w5,w30] [q41,q348,q420,q520,q524] [] (by decide +kernel)
def n755 := cc 8 [w0,w88,w1,w2,w3,w24,w5,w19] [q407,q525,q537] [] (by decide +kernel)
def n756 := cc 8 [w0,w88,w1,w2,w3,w4,w5,w31] [q134,q407,q537] [] (by decide +kernel)
def v245 : Closed T 8 := rotateClosed n754 auto1 auto1ok
def n757 := cc 9 [w0,w88,w1,w2,w3,w4,w24,w5] [q98,q229,q407,q525,q537] [v243,n734,n756,n420,n755,n154,n753,v245] (by decide +kernel)
def n758 := cc 9 [w26,w0,w1,w2,w3,w4,w5,w30] [q134,q229,q348,q400,q419,q506] [n523] (by decide +kernel)
def n759 := cc 7 [w0,w1,w2,w122,w3,w24,w30,w19] [q262,q288,q289,q339,q457] [] (by decide +kernel)
def n760 := cc 8 [w0,w1,w2,w3,w24,w30,w19] [q76,q135,q138,q261,q457] [n759] (by decide +kernel)
def n761 := cc 7 [w33,w327,w0,w1,w2,w3] [q134,q278,q562] [] (by decide +kernel)
def n762 := cc 8 [w33,w0,w1,w2,w3,w4,w30] [q134,q275,q555] [n761] (by decide +kernel)
def n763 := cc 8 [w0,w1,w2,w3,w4,w5,w31] [q0,q73,q165,q209,q261,q293] [] (by decide +kernel)
def v246 : Closed T 8 := rotateClosed n762 auto1 auto1ok
def n764 := cc 9 [w0,w1,w2,w3,w4,w24,w5,w30] [q134,q138,q187,q229,q334,q348,q419,q421,q503] [n762,v246,n763,n760] (by decide +kernel)
def n765 := cc 8 [w0,w1,w2,w3,w4,w329,w30] [q71,q80,q165,q261] [] (by decide +kernel)
def n766 := cc 8 [w328,w0,w1,w2,w3,w30,w19] [q165,q261,q420,q457,q552] [] (by decide +kernel)
def n767 := cc 9 [w328,w0,w1,w2,w3,w4,w5,w30] [q165,q187,q229,q421,q457,q552] [n766,n763,n765] (by decide +kernel)
def n768 := cc 8 [w0,w1,w2,w3,w330,w4,w24,w5] [q154,q334,q417,q525] [] (by decide +kernel)
def n769 := cc 7 [w0,w1,w2,w3,w24,w331,w19] [q340,q417,q525] [] (by decide +kernel)
def n770 := cc 8 [w0,w1,w2,w3,w4,w24,w5,w331] [q334,q417,q457,q525] [n769] (by decide +kernel)
def n771 := cc 8 [w0,w1,w2,w90,w3,w24,w5,w19] [q340,q417,q503,q525] [n769] (by decide +kernel)
def n772 := cc 8 [w0,w1,w2,w90,w3,w4,w5,w31] [q73,q134,q342,q503] [] (by decide +kernel)
def n773 := cc 9 [w0,w1,w2,w90,w3,w4,w24,w5] [q154,q334,q417,q424,q503,q525] [n736,n772,n422,n771,n768,n770,n157] (by decide +kernel)
def n774 := cc 9 [w332,w0,w1,w2,w3,w4,w5,w30] [q134,q348,q419,q484] [n709] (by decide +kernel)
def n775 := cc 8 [w0,w1,w2,w3,w4,w30,w334] [q80,q165,q181,q229,q348] [] (by decide +kernel)
def n776 := cc 8 [w0,w1,w2,w3,w4,w336,w5] [q73,q209,q225,q235,q334] [] (by decide +kernel)
def n777 := cc 8 [w337,w0,w1,w2,w3,w4,w5] [q162,q209,q236,q334] [] (by decide +kernel)
def v247 : Closed T 8 := rotateClosed n777 auto1 auto1ok
def v248 : Closed T 8 := rotateClosed n776 auto1 auto1ok
def n778 := cc 9 [w0,w1,w2,w333,w3,w4,w5,w30] [q165,q348,q419,q484] [v247,v248,n775] (by decide +kernel)
def n779 := cc 9 [w91,w0,w1,w2,w3,w4,w24,w5] [q175,q274,q334,q424,q503,q525] [n248,n740,n185,n421,n158] (by decide +kernel)
def n780 := cc 8 [w202,w0,w1,w2,w3,w4,w30] [q108,q229,q478,q524,q528] [n603] (by decide +kernel)
def v249 : Closed T 7 := rotateClosed n661 auto1 auto1ok
def n781 := cc 8 [w0,w62,w1,w2,w3,w4,w30,w19] [q187,q261,q528,q539] [v249] (by decide +kernel)
def n782 := cc 8 [w0,w1,w203,w3,w4,w30,w19] [q261,q491,q517,q528] [] (by decide +kernel)
def n783 := cc 8 [w34,w0,w1,w3,w4,w30,w19] [q229,q516,q524,q536] [] (by decide +kernel)
def n784 := cc 8 [w0,w1,w2,w122,w3,w4,w30,w19] [q261,q351,q457,q467,q484,q517,q528] [n759] (by decide +kernel)
def n785 := cc 8 [w0,w1,w2,w3,w338,w30,w19] [q80,q165,q181,q187,q393,q457] [] (by decide +kernel)
def n786 := cc 8 [w33,w0,w1,w2,w3,w24,w19] [q73,q187,q525,q531] [] (by decide +kernel)
def v250 : Closed T 8 := rotateClosed n662 auto1 auto1ok
def v251 : Closed T 8 := rotateClosed n786 auto1 auto1ok
def v252 : Closed T 8 := rotateClosed n741 auto1 auto1ok
def v253 : Closed T 8 := rotateClosed n755 auto1 auto1ok
def v254 : Closed T 8 := rotateClosed n751 auto1 auto1ok
def v255 : Closed T 8 := rotateClosed n771 auto1 auto1ok
def n787 := cc 9 [w0,w1,w2,w3,w4,w30,w19] [q138,q229,q261,q393,q457,q484,q524,q528] [n526,v250,v251,n766,n783,n43,n249,n299,n479,v252,n780,n606,n649,v253,v254,n781,n782,v255,n784,n785,n423,n187,n432,n760,n160] (by decide +kernel)
def n788 := cc 8 [w34,w0,w1,w3,w4,w24,w5] [q73,q181,q399,q480,q555] [] (by decide +kernel)
def n789 := cc 8 [w33,w0,w1,w2,w3,w4,w19] [q73,q172,q397,q467,q555] [] (by decide +kernel)
def n790 := cc 9 [w0,w1,w2,w3,w4,w24,w5,w19] [q73,q80,q138,q187,q229,q261,q385,q419,q424] [n789,n788,n763] (by decide +kernel)
def n791 := cc 8 [w0,w1,w2,w3,w340,w4,w30] [q187,q237,q484,q555] [] (by decide +kernel)
def n792 := cc 8 [w0,w1,w2,w3,w4,w30,w19] [q42,q80,q165,q261] [] (by decide +kernel)
def v256 : Closed T 8 := rotateClosed n791 auto1 auto1ok
def v257 : Closed T 8 := rotateClosed n792 auto1 auto1ok
def n793 := cc 9 [w341,w0,w1,w2,w3,w24,w5] [q138,q209,q275,q385,q417,q419,q424] [v256,v257] (by decide +kernel)
def n794 := cc 8 [w0,w1,w342,w3,w4,w5,w30] [q80,q165,q209,q393,q457] [] (by decide +kernel)
def n795 := cc 8 [w341,w327,w0,w1,w2,w3,w5] [q165,q278,q393,q457,q552] [] (by decide +kernel)
def n796 := cc 9 [w341,w0,w1,w2,w3,w4,w5,w30] [q187,q229,q393,q419,q457] [n795,n763,n792,n794] (by decide +kernel)
def n797 := cc 8 [w33,w0,w1,w2,w3,w4,w5] [q40,q73,q172,q275,q346] [] (by decide +kernel)
def v258 : Closed T 7 := rotateClosed n726 auto1 auto1ok
def n798 := cc 8 [w0,w1,w2,w3,w338,w5,w31] [q80,q165,q238,q457,q552] [v258] (by decide +kernel)
def v259 : Closed T 8 := rotateClosed n797 auto1 auto1ok
def v260 : Closed T 8 := rotateClosed n727 auto1 auto1ok
def n799 := cc 9 [w0,w1,w2,w3,w338,w4,w5,w30] [q80,q165,q172,q187,q203,q229,q393,q419,q457] [v259,v260,n798,n785] (by decide +kernel)
def n800 := cc 8 [w32,w0,w1,w2,w3,w4,w5] [q103,q134,q165,q209,q293,q459,q540] [n45,n302,n607] (by decide +kernel)
def n801 := cc 7 [w0,w1,w343,w2,w3,w4,w5] [q103,q105,q109,q117,q291] [] (by decide +kernel)
def n802 := cc 8 [w0,w269,w1,w2,w3,w4,w5] [q166,q210,q261,q291] [n801] (by decide +kernel)
def n803 := cc 8 [w0,w269,w1,w2,w3,w4,w5,w31] [q80,q134,q342,q393,q458] [n611] (by decide +kernel)
def n804 := cc 8 [w34,w0,w1,w2,w3,w4,w5] [q48,q73,q181,q225,q261,q360] [] (by decide +kernel)
def n805 := cc 8 [w34,w0,w1,w3,w4,w5,w31] [q0,q134,q536,q552,q555] [] (by decide +kernel)
def n806 := cc 8 [w0,w1,w2,w344,w3,w4,w5,w31] [q80,q134,q342,q457] [] (by decide +kernel)
def n807 := cc 8 [w33,w0,w1,w2,w3,w4,w31] [q0,q134,q531,q555] [n761] (by decide +kernel)
def v261 : Closed T 8 := rotateClosed n807 auto1 auto1ok
def v262 : Closed T 8 := rotateClosed n475 auto1 auto1ok
def n808 := cc 9 [w0,w1,w2,w3,w4,w5,w31] [q73,q80,q86,q134,q261,q293,q393,q503] [n525,n797,v259,n807,v261,n804,n805,n46,n250,n303,n475,v262,n800,n612,n802,n803,n806,n188,n424,v137,n161] (by decide +kernel)
def n809 := cc 8 [w0,w269,w1,w2,w3,w4,w24,w5] [q134,q407,q533] [] (by decide +kernel)
def v263 : Closed T 8 := rotateClosed n798 auto1 auto1ok
def n810 := cc 9 [w0,w1,w2,w3,w4,w24,w5,w31] [q73,q80,q134,q334,q407,q417,q419,q503] [v246,n807,n788,n614,n756,n809,n728,n772,v263] (by decide +kernel)
def n811 := cc 8 [w0,w252,w1,w2,w3,w4,w5] [q105,q172,q293,q421,q468,q550] [n615] (by decide +kernel)
def n812 := cc 8 [w0,w345,w1,w2,w3,w4,w5] [q291,q412,q524] [] (by decide +kernel)
def v264 : Closed T 8 := rotateClosed n795 auto1 auto1ok
def v265 : Closed T 8 := rotateClosed n812 auto1 auto1ok
def n813 := cc 9 [w33,w0,w1,w2,w3,w4,w5] [q80,q138,q172,q229,q275,q293,q397,q417,q421,q467,q555] [n433,n658,v264,n47,n251,n304,n476,n616,n762,n789,n807,n425,n162,n811,v265,n763] (by decide +kernel)
def n814 := cc 9 [w33,w0,w1,w2,w3,w4,w24,w5] [q138,q187,q229,q525,q531,q555] [n729,n807,n786] (by decide +kernel)
def n815 := cc 9 [w323,w0,w1,w2,w3,w4,w5,w30] [q80,q134,q393,q457,q552] [n731,n763,n765,n794] (by decide +kernel)
def v266 : Closed T 9 := rotateClosed n758 auto1 auto1ok
def v267 : Closed T 9 := rotateClosed n774 auto1 auto1ok
def v268 : Closed T 9 := rotateClosed n815 auto1 auto1ok
def v269 : Closed T 9 := rotateClosed n796 auto1 auto1ok
def v270 : Closed T 9 := rotateClosed n767 auto1 auto1ok
def v271 : Closed T 9 := rotateClosed n480 auto1 auto1ok
def v272 : Closed T 9 := rotateClosed n650 auto1 auto1ok
def v273 : Closed T 9 := rotateClosed n778 auto1 auto1ok
def v274 : Closed T 9 := rotateClosed n799 auto1 auto1ok
def v275 : Closed T 9 := rotateClosed n434 auto1 auto1ok
def v276 : Closed T 9 := rotateClosed n787 auto1 auto1ok
def n816 := cc 10 [w0,w1,w2,w3,w4,w24,w5] [q138,q187,q229,q293,q385,q424] [v164,v266,v267,v268,n663,n779,v269,n793,n814,n813,n714,v270,n48,n252,n305,v271,n477,n743,n742,n617,v272,n757,n752,n732,n167,v273,n773,v274,v275,n737,n764,n790,n810,n190,n808,v142,v276,n163] (by decide +kernel)
def n817 := cc 8 [w347,w0,w1,w2,w3,w4,w5] [q0,q80,q172,q269,q293] [] (by decide +kernel)
def n818 := cc 8 [w91,w0,w346,w1,w2,w3,w4,w5] [q175,q217,q274,q368,q509] [] (by decide +kernel)
def v277 : Closed T 8 := rotateClosed n817 auto1 auto1ok
def v278 : Closed T 8 := rotateClosed n818 auto1 auto1ok
def n819 := cc 9 [w0,w348,w1,w2,w3,w4,w5] [q133,q172,q187,q229,q293,q421,q495] [v277,v278,n436] (by decide +kernel)
def n820 := cc 8 [w349,w0,w1,w2,w3,w4,w5] [q0,q209,q281,q293,q555] [] (by decide +kernel)
def n821 := cc 8 [w0,w1,w2,w3,w4,w200,w19] [q73,q165,q261,q457] [] (by decide +kernel)
def n822 := cc 8 [w341,w0,w1,w2,w3,w95,w5] [q172,q209,q237,q275,q561] [] (by decide +kernel)
def v279 : Closed T 8 := rotateClosed n821 auto1 auto1ok
def n823 := cc 9 [w0,w1,w2,w3,w4,w95,w5] [q73,q209,q229,q293,q467,q503,q555] [n822,n797,n307,n482,n820,n436,n763,v138,v279,n168] (by decide +kernel)
def n824 := cc 9 [w0,w1,w2,w3,w4,w24,w5] [q33,q73,q138,q209,q229,q334,q417] [n797,n763,v257] (by decide +kernel)
def n825 := cc 9 [w94,w350,w0,w1,w3,w4] [q187,q229,q484] [n724] (by decide +kernel)
def n826 := cc 8 [w0,w1,w2,w351,w3,w4,w5] [q172,q232,q503,q555] [] (by decide +kernel)
def n827 := cc 8 [w94,w0,w1,w2,w3,w4,w334] [q80,q172,q233,q369,q555] [] (by decide +kernel)
def n828 := cc 9 [w94,w0,w1,w2,w333,w3,w4,w5] [q172,q232,q484] [n827,n826] (by decide +kernel)
def n829 := cc 9 [w94,w96,w0,w1,w2,w3,w4,w5] [q123,q273,q369,q467,q484] [n169,v278] (by decide +kernel)
def n830 := cc 9 [w94,w0,w1,w2,w3,w4,w5,w19] [q73,q80,q138,q187,q261,q484,q555] [n763,v279,n792] (by decide +kernel)
def n831 := cc 8 [w94,w0,w1,w342,w3,w4,w5] [q80,q159,q209,q275,q467] [] (by decide +kernel)
def n832 := cc 9 [w94,w341,w0,w1,w2,w3,w4,w5] [q172,q187,q275,q467] [n831,n822,n797] (by decide +kernel)
def v280 : Closed T 9 := rotateClosed n824 auto1 auto1ok
def n833 := cc 10 [w94,w0,w1,w2,w3,w4,w5] [q138,q187,q229,q293,q484] [n832,n829,n825,n308,n483,n828,n437,n830,n170,n819,n823,v280] (by decide +kernel)
def n834 := cc 8 [w328,w0,w1,w2,w3,w352,w5] [q73,q181,q203,q225,q261,q480] [] (by decide +kernel)
def v281 : Closed T 8 := rotateClosed n765 auto1 auto1ok
def n835 := cc 9 [w0,w1,w2,w3,w4,w352,w5] [q73,q187,q261,q400,q484,q555] [n834,n804,n763,v281] (by decide +kernel)
def n836 := cc 8 [w328,w350,w0,w1,w2,w3,w19] [q159,q181,q203,q261,q480,q552] [] (by decide +kernel)
def v282 : Closed T 8 := rotateClosed n834 auto1 auto1ok
def n837 := cc 9 [w328,w350,w0,w1,w2,w3,w4,w5] [q70,q72,q181,q225,q229,q383,q384] [n836,n834,v282,n804] (by decide +kernel)
def n838 := cc 8 [w0,w1,w2,w353,w3,w4,w19] [q187,q386,q417,q436] [] (by decide +kernel)
def v283 : Closed T 8 := rotateClosed n838 auto1 auto1ok
def n839 := cc 9 [w328,w0,w1,w2,w3,w5,w19] [q138,q187,q261,q385,q421,q424] [n836,n766,v283,v257] (by decide +kernel)
def v284 : Closed T 9 := rotateClosed n825 auto1 auto1ok
def v285 : Closed T 9 := rotateClosed n835 auto1 auto1ok
def n840 := cc 10 [w328,w0,w1,w2,w3,w4,w5] [q138,q187,q229,q385,q424] [v284,n837,n767,n839,v285,n824] (by decide +kernel)
def n841 := cc 8 [w355,w0,w1,w2,w3,w4,w5] [q80,q172,q369,q503] [] (by decide +kernel)
def n842 := cc 9 [w0,w1,w2,w3,w354,w4,w5] [q134,q138,q293,q417,q503] [n841,v248] (by decide +kernel)
def n843 := cc 7 [w0,w1,w357,w3,w336,w5] [q204,q235,q299,q552] [] (by decide +kernel)
def n844 := cc 8 [w0,w1,w357,w2,w3,w356,w5] [q73,q203,q225,q235,q298,q424] [n843] (by decide +kernel)
def v286 : Closed T 7 := rotateClosed n843 auto1 auto1ok
def n845 := cc 8 [w0,w1,w2,w3,w4,w334,w358] [q80,q165,q181,q233,q348] [v286] (by decide +kernel)
def n846 := cc 8 [w359,w0,w1,w2,w3,w4,w334] [q80,q172,q233,q369,q555] [] (by decide +kernel)
def n847 := cc 8 [w360,w0,w1,w2,w3,w356,w5] [q73,q203,q225,q383,q552] [] (by decide +kernel)
def v287 : Closed T 8 := rotateClosed n847 auto1 auto1ok
def v288 : Closed T 8 := rotateClosed n844 auto1 auto1ok
def n848 := cc 9 [w0,w1,w2,w3,w4,w334] [q138,q293] [n846,v287,v288,n845] (by decide +kernel)
def n849 := cc 8 [w360,w0,w1,w2,w3,w4,w5] [q11,q73,q225,q383,q552] [] (by decide +kernel)
def v289 : Closed T 8 := rotateClosed n827 auto1 auto1ok
def v290 : Closed T 8 := rotateClosed n775 auto1 auto1ok
def n850 := cc 9 [w0,w1,w2,w3,w4,w356,w5] [q73,q187,q229,q293,q424,q517] [v289,n849,n776,v290] (by decide +kernel)
def n851 := cc 9 [w361,w0,w1,w2,w3,w5] [q138,q187,q293] [] (by decide +kernel)
def n852 := cc 8 [w362,w0,w1,w2,w4] [q187,q293,q424,q484] [] (by decide +kernel)
def v291 : Closed T 8 := rotateClosed n852 auto1 auto1ok
def n853 := cc 9 [w0,w1,w2,w333,w41,w5] [q138,q293,q484] [v291] (by decide +kernel)
def v292 : Closed T 9 := rotateClosed n851 auto1 auto1ok
def v293 : Closed T 9 := rotateClosed n850 auto1 auto1ok
def n854 := cc 10 [w0,w1,w2,w333,w3,w4,w5] [q138,q229,q293,q484] [n828,v292,n778,n853,n842,v293,n848] (by decide +kernel)
def n855 := cc 8 [w364,w0,w1,w2,w3,w4,w5] [q62,q134,q215,q260,q425,q550] [] (by decide +kernel)
def n856 := cc 8 [w0,w1,w2,w365,w3,w4,w5] [q86,q134,q164,q291,q505] [] (by decide +kernel)
def v294 : Closed T 8 := rotateClosed n855 auto1 auto1ok
def n857 := cc 9 [w232,w0,w1,w2,w3,w4,w5] [q110,q137,q138,q229,q484,q547] [n210,n529,n49,n508,v294,n856] (by decide +kernel)
def n858 := cc 6 [w366,w1,w107,w2,w3,w4,w5] [q134] [] (by decide +kernel)
def n859 := cc 6 [w111,w0,w1,w107,w2,w3,w4] [] [] (by decide +kernel)
def n860 := cc 7 [w0,w1,w107,w2,w110,w3,w4,w5] [q13,q134,q242,q529] [n859,n858] (by decide +kernel)
def n861 := cc 7 [w108,w0,w1,w107,w2,w3,w4,w5] [q134,q242,q540] [n200] (by decide +kernel)
def n862 := cc 8 [w0,w1,w107,w2,w3,w4,w5] [q134,q144,q242,q493,q540] [n861,n860,n201] (by decide +kernel)
def n863 := cc 7 [w0,w1,w107,w2,w109,w3,w4,w5] [q19,q110,q134,q254,q322,q323] [n858,n202] (by decide +kernel)
def n864 := cc 7 [w108,w0,w106,w1,w2,w3,w4,w5] [q4,q51,q134,q242] [] (by decide +kernel)
def n865 := cc 8 [w0,w106,w1,w107,w2,w3,w4,w5] [q110,q144,q242,q254,q291,q493] [n864,n206,n863,n203] (by decide +kernel)
def n866 := cc 8 [w0,w1,w2,w109,w3,w4,w5] [q134,q335,q391,q502] [] (by decide +kernel)
def n867 := cc 7 [w366,w0,w106,w1,w2,w3,w4,w5] [q19,q62,q96,q110] [n858] (by decide +kernel)
def n868 := cc 8 [w0,w106,w1,w2,w109,w3,w4,w5] [q145,q254,q291,q334,q367,q502] [n867,n206,n204,n863] (by decide +kernel)
def n869 := cc 9 [w0,w106,w1,w2,w3,w4,w5] [q110,q254,q291,q293,q294,q295,q385,q484] [n528,n49,n865,n208,n868,n862,n866] (by decide +kernel)
def n870 := cc 8 [w0,w367,w1,w2,w3,w4,w5] [q86,q134,q177,q512,q540] [] (by decide +kernel)
def n871 := cc 8 [w0,w369,w1,w2,w3,w4,w5] [q259,q291,q426,q535] [] (by decide +kernel)
def v295 : Closed T 8 := rotateClosed n871 auto1 auto1ok
def n872 := cc 9 [w43,w0,w1,w2,w3,w4,w5] [q86,q134,q254,q415,q424,q484] [n210,n528,n50,n309,n870,v295] (by decide +kernel)
def n873 := cc 10 [w0,w1,w2,w3,w4,w41,w5] [q138,q229,q293,q424,q484] [n530,n872,n51,n254,n310,n857,n510,n869,n211,n853] (by decide +kernel)
def n874 := cc 9 [w91,w370,w0,w1,w2,w4] [q187,q293,q424] [n852] (by decide +kernel)
def v296 : Closed T 9 := rotateClosed n829 auto1 auto1ok
def n875 := cc 10 [w91,w0,w1,w2,w3,w4,w5] [q187,q293,q424,q484] [v296,n874,n255,n212,n438,n779] (by decide +kernel)
def n876 := cc 9 [w0,w1,w2,w372,w3,w4,w5] [q138,q385,q484] [] (by decide +kernel)
def v297 : Closed T 9 := rotateClosed n874 auto1 auto1ok
def n877 := cc 10 [w371,w0,w1,w2,w3,w4,w5] [q138,q229,q385,q484] [v297,n876] (by decide +kernel)
def n878 := cc 7 [w0,w1,w203,w3,w374,w19] [q159,q172,q181,q238,q436,q560] [] (by decide +kernel)
def n879 := cc 7 [w34,w0,w1,w3,w374,w19] [q159,q181,q399,q480,q552] [] (by decide +kernel)
def n880 := cc 8 [w0,w1,w2,w3,w374,w19] [q135,q138,q385,q417,q424,q558] [n879,n878] (by decide +kernel)
def n881 := cc 9 [w0,w1,w2,w3,w4,w374,w5] [q138,q187,q385,q424] [n880] (by decide +kernel)
def n882 := cc 6 [w375,w0,w1,w203,w3] [q160,q387,q563] [] (by decide +kernel)
def n883 := cc 7 [w0,w1,w203,w3,w373,w31] [q73,q160,q238,q437,q552] [n882] (by decide +kernel)
def n884 := cc 8 [w0,w1,w203,w2,w3,w373,w19] [q73,q159,q181,q238,q436,q558,q559] [n883,n878] (by decide +kernel)
def n885 := cc 7 [w375,w0,w1,w2,w3,w19] [q73,q165,q393,q417,q562] [n882] (by decide +kernel)
def n886 := cc 8 [w0,w1,w2,w3,w373,w19,w31] [q73,q135,q165,q181,q238,q393,q457,q561] [n885,n883] (by decide +kernel)
def n887 := cc 7 [w0,w1,w2,w3,w377,w19] [q172,q238,q467,q552] [] (by decide +kernel)
def n888 := cc 8 [w376,w0,w1,w2,w3,w373,w19] [q73,q172,q238,q467,q552,q562] [n887] (by decide +kernel)
def n889 := cc 8 [w34,w0,w1,w2,w3,w373,w19] [q73,q135,q159,q181,q399,q480,q552,q564] [n879] (by decide +kernel)
def n890 := cc 9 [w0,w1,w2,w3,w373,w19] [q138,q385,q424,q558] [n888,n889,n884,n886,n880] (by decide +kernel)
def n891 := cc 10 [w0,w1,w2,w3,w373,w4,w5] [q138,q187,q229,q385,q424] [n890,n881] (by decide +kernel)
def n892 := cc 7 [w175,w0,w62,w1,w2,w3,w4,w5] [q115,q117,q248,q553] [] (by decide +kernel)
def n893 := cc 8 [w0,w62,w1,w2,w3,w4,w5,w173] [q73,q80,q114,q248,q261,q524,q539] [n892] (by decide +kernel)
def n894 := cc 8 [w0,w174,w1,w2,w3,w4,w5,w19] [q73,q80,q114,q261,q419,q533,q536] [] (by decide +kernel)
def n895 := cc 8 [w0,w1,w203,w2,w3,w4,w5,w173] [q31,q45,q73,q80,q181,q203,q248,q325,q358] [] (by decide +kernel)
def n896 := cc 8 [w34,w0,w1,w2,w3,w4,w5,w173] [q73,q80,q159,q181,q261,q325,q360,q483,q536] [] (by decide +kernel)
def n897 := cc 7 [w175,w0,w1,w2,w122,w3,w4,w5] [q48,q248,q454,q501,q554] [] (by decide +kernel)
def n898 := cc 8 [w175,w0,w1,w2,w3,w4,w5,w19] [q73,q80,q117,q159,q225,q354,q419,q454,q533] [n512,n892,n690,n897] (by decide +kernel)
def n899 := cc 8 [w0,w1,w2,w122,w3,w4,w5,w173] [q73,q80,q161,q186,q205,q248,q262,q325,q524] [n897] (by decide +kernel)
def n900 := cc 9 [w0,w1,w2,w3,w4,w5,w19,w173] [q73,q80,q114,q138,q187,q261,q354,q448] [n532,n717,n896,n898,n446,n513,n619,n893,n894,n691,n895,n899] (by decide +kernel)
def n901 := cc 8 [w378,w0,w1,w2,w3,w4,w5] [q114,q134,q170,q216,q229,q359,q479,q549] [] (by decide +kernel)
def n902 := cc 8 [w0,w1,w2,w270,w3,w4,w5] [q103,q134,q165,q209,q291,q293,q477] [n621] (by decide +kernel)
def v298 : Closed T 8 := rotateClosed n780 auto1 auto1ok
def n903 := cc 9 [w202,w0,w1,w2,w3,w4,w5] [q114,q138,q187,q229,q293,q476,q517,q528] [n226,n533,n718,n52,n514,n622,n692,n780,v298,n446,n901,n902] (by decide +kernel)
def v299 : Closed T 8 := rotateClosed n439 auto1 auto1ok
def n904 := cc 9 [w202,w0,w1,w2,w3,w4,w5,w19] [q138,q187,q528,q529,q536,q539] [n446,n439,v299] (by decide +kernel)
def n905 := cc 6 [w379,w1,w63,w2,w3,w4,w5] [q134] [] (by decide +kernel)
def n906 := cc 7 [w0,w1,w63,w2,w119,w3,w4,w5] [q134,q173,q218,q248,q325,q433,q540] [n905] (by decide +kernel)
def n907 := cc 7 [w117,w0,w1,w63,w2,w3,w4,w5] [q134,q248,q540] [n213] (by decide +kernel)
def n908 := cc 8 [w0,w1,w63,w2,w3,w4,w5] [q114,q134,q151,q198,q248,q325,q433,q540] [n907,n625,n906,n214] (by decide +kernel)
def n909 := cc 7 [w0,w1,w63,w2,w118,w3,w4,w5] [q114,q134,q261] [n905,n215] (by decide +kernel)
def n910 := cc 7 [w117,w0,w62,w1,w2,w3,w4,w5] [q115,q134,q248] [] (by decide +kernel)
def n911 := cc 8 [w0,w62,w1,w63,w2,w3,w4,w5] [q114,q151,q248,q261,q291,q549] [n910,n218,n909,n216] (by decide +kernel)
def n912 := cc 8 [w0,w1,w2,w118,w3,w4,w5] [q134,q293,q393,q407,q434] [] (by decide +kernel)
def n913 := cc 7 [w379,w0,w62,w1,w2,w3,w4,w5] [q103,q114,q120] [n905] (by decide +kernel)
def n914 := cc 8 [w0,w62,w1,w2,w118,w3,w4,w5] [q152,q261,q291,q393,q397] [n913,n218,n217,n909] (by decide +kernel)
def n915 := cc 9 [w0,w62,w1,w2,w3,w4,w5] [q0,q198,q261,q291,q354,q385,q400] [n655,n531,n52,n626,n911,n220,n914,n908,n912] (by decide +kernel)
def n916 := cc 8 [w0,w1,w63,w2,w3,w4,w5,w19] [q114,q151,q261,q419,q528,q529,q539] [n221] (by decide +kernel)
def n917 := cc 8 [w0,w1,w2,w118,w3,w4,w5,w19] [q172,q217,q261,q342,q354,q434,q490,q517,q524] [] (by decide +kernel)
def n918 := cc 8 [w0,w62,w1,w2,w3,w4,w5,w31] [q261,q528,q539] [] (by decide +kernel)
def v300 : Closed T 8 := rotateClosed n664 auto1 auto1ok
def v301 : Closed T 8 := rotateClosed n440 auto1 auto1ok
def v302 : Closed T 8 := rotateClosed n781 auto1 auto1ok
def n919 := cc 9 [w0,w62,w1,w2,w3,w4,w5,w19] [q198,q261,q385,q539] [n655,n664,v300,n223,n893,n918,n440,v301,n781,v302,n916,n917] (by decide +kernel)
def n920 := cc 9 [w37,w0,w1,w2,w3,w4,w5,w19] [q73,q354,q385,q400,q508,q528,q536] [n655] (by decide +kernel)
def n921 := cc 8 [w0,w1,w2,w380,w3,w4,w5,w19] [q203,q261,q354,q492,q517,q528,q529] [] (by decide +kernel)
def n922 := cc 8 [w0,w1,w203,w3,w4,w5,w31] [q73,q261,q437,q528,q552] [n883] (by decide +kernel)
def v303 : Closed T 8 := rotateClosed n441 auto1 auto1ok
def v304 : Closed T 8 := rotateClosed n782 auto1 auto1ok
def n923 := cc 9 [w0,w1,w203,w2,w3,w4,w5,w19] [q138,q159,q187,q261,q539] [n804,n884,n895,n441,v303,n922,n782,v304,n921] (by decide +kernel)
def n924 := cc 8 [w0,w269,w1,w2,w3,w4,w5,w19] [q73,q261,q528,q533] [] (by decide +kernel)
def n925 := cc 8 [w0,w1,w2,w122,w3,w4,w5,w31] [q261,q342,q360,q467,q503,q528] [] (by decide +kernel)
def v305 : Closed T 8 := rotateClosed n789 auto1 auto1ok
def n926 := cc 9 [w0,w1,w2,w3,w4,w5,w19,w31] [q261,q354,q419,q457,q517,q520,q528] [n789,v305,n805,n628,n918,n924,n922,n925,n886] (by decide +kernel)
def n927 := cc 9 [w376,w0,w1,w2,w3,w4,w5,w19] [q73,q261,q354,q467,q528,q530,q552] [n888,n763,n821,v279] (by decide +kernel)
def n928 := cc 8 [w0,w254,w1,w2,w3,w4,w5] [q117,q134,q181,q225,q293,q481,q540] [n629] (by decide +kernel)
def n929 := cc 8 [w0,w381,w1,w2,w3,w4,w5] [q261,q291,q536] [] (by decide +kernel)
def v306 : Closed T 8 := rotateClosed n484 auto1 auto1ok
def v307 : Closed T 8 := rotateClosed n442 auto1 auto1ok
def v308 : Closed T 8 := rotateClosed n788 auto1 auto1ok
def n930 := cc 9 [w34,w0,w1,w2,w3,w4,w5] [q134,q138,q181,q187,q225,q261,q293,q480,q536,q539,q552,q555] [n226,n531,n53,n312,n484,v306,n632,n442,v307,n788,v308,n805,n928,n929,n763] (by decide +kernel)
def n931 := cc 8 [w0,w254,w1,w2,w3,w4,w5,w19] [q354,q481,q517,q524,q528,q529,q540] [] (by decide +kernel)
def v309 : Closed T 8 := rotateClosed n443 auto1 auto1ok
def v310 : Closed T 8 := rotateClosed n783 auto1 auto1ok
def n932 := cc 9 [w34,w0,w1,w2,w3,w4,w5,w19] [q73,q138,q181,q187,q261,q419,q421,q536,q539,q552] [n889,n896,n443,v309,n805,n783,v310,n931] (by decide +kernel)
def n933 := cc 8 [w0,w1,w2,w3,w123,w4,w5,w19] [q261,q354,q419,q499,q517,q528,q529] [n227] (by decide +kernel)
def n934 := cc 8 [w0,w1,w2,w3,w382,w4,w5,w19] [q172,q209,q354,q517,q524] [] (by decide +kernel)
def v311 : Closed T 8 := rotateClosed n444 auto1 auto1ok
def v312 : Closed T 8 := rotateClosed n784 auto1 auto1ok
def n935 := cc 9 [w0,w1,w2,w122,w3,w4,w5,w19] [q161,q261,q354,q424,q484,q517,q530] [n257,n229,n899,n925,n444,v311,n784,v312,n933,n934] (by decide +kernel)
def n936 := cc 9 [w383,w0,w1,w2,w3,w4,w5,w19] [q73,q354,q424,q484,q528,q539] [] (by decide +kernel)
def v313 : Closed T 9 := rotateClosed n665 auto1 auto1ok
def v314 : Closed T 9 := rotateClosed n830 auto1 auto1ok
def v315 : Closed T 9 := rotateClosed n839 auto1 auto1ok
def v316 : Closed T 9 := rotateClosed n485 auto1 auto1ok
def v317 : Closed T 9 := rotateClosed n651 auto1 auto1ok
def v318 : Closed T 9 := rotateClosed n790 auto1 auto1ok
def n937 := cc 10 [w0,w1,w2,w3,w4,w5,w19] [q138,q187,q229,q293,q385,q400,q424,q484] [n657,n920,n927,n936,n665,v313,n830,v314,n534,n719,n839,v315,n930,n932,n54,n258,n313,n485,v316,n903,n904,n517,n633,n651,v317,n915,n919,n695,n923,n230,n935,n890,n790,v318,n900,n926,n456,n808,n445,v143,n787,v276] (by decide +kernel)
def n938 := cc 9 [w0,w1,w2,w342,w3,w4,w5] [q134,q138,q209,q385,q417,q424] [n831,n797,n763,n794] (by decide +kernel)
def n939 := cc 9 [w0,w1,w2,w3,w4,w5,w19] [q43,q73,q138,q187,q261,q354,q385,q517] [n804,n763,n792,v257] (by decide +kernel)
def n940 := cc 10 [w341,w0,w1,w2,w3,w4,w5] [q138,q187,q229,q385,q424,q558] [n832,n796,n793,n938,n939] (by decide +kernel)
def v319 : Closed T 10 := rotateClosed n465 auto1 auto1ok
def v320 : Closed T 10 := rotateClosed n666 auto1 auto1ok
def v321 : Closed T 10 := rotateClosed n833 auto1 auto1ok
def v322 : Closed T 10 := rotateClosed n875 auto1 auto1ok
def v323 : Closed T 10 := rotateClosed n940 auto1 auto1ok
def v324 : Closed T 10 := rotateClosed n877 auto1 auto1ok
def v325 : Closed T 10 := rotateClosed n840 auto1 auto1ok
def v326 : Closed T 10 := rotateClosed n670 auto1 auto1ok
def v327 : Closed T 10 := rotateClosed n486 auto1 auto1ok
def v328 : Closed T 10 := rotateClosed n325 auto1 auto1ok
def v329 : Closed T 10 := rotateClosed n652 auto1 auto1ok
def v330 : Closed T 10 := rotateClosed n733 auto1 auto1ok
def v331 : Closed T 10 := rotateClosed n854 auto1 auto1ok
def v332 : Closed T 10 := rotateClosed n457 auto1 auto1ok
def v333 : Closed T 10 := rotateClosed n653 auto1 auto1ok
def v334 : Closed T 10 := rotateClosed n816 auto1 auto1ok
def v335 : Closed T 10 := rotateClosed n873 auto1 auto1ok
def n941 := cc 11 [w0,w1,w2,w3,w4,w5] [] [n465,v319,n666,v320,n833,v321,n875,v322,n940,v323,n284,n637,n704,n877,v324,n238,n535,n720,n840,v325,n8,n536,n638,n670,v326,n55,n259,n314,n486,v327,n4,n62,n263,n325,v328,n518,n634,n652,v329,n5,n696,n733,v330,n231,n521,n854,v331,n279,n635,n702,n891,n457,v332,n653,v333,n816,v334,n873,v335,n937] (by decide +kernel)
theorem independentlyEnumeratedBound : Lower true R T 12 :=
  fromClosed n941 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 5, 4), (0xcccccccccccccccc, 11, 9), (0xf0f0f0f0f0f0f0f0, 5, 1), (0xff00ff00ff00ff00, 11, 3), (0xffff0000ffff0000, 17, 1), (0xffffffff00000000, 33, 1)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide +kernel)
end B51

def fullRoots : List Sig := inputs
def fullWord : Sig := 0xfeeefeeafeeae8a0
theorem fullBound : Lower true fullRoots fullWord 12 := by
  intro p bank h hit
  have hlow := B51.independentlyEnumeratedBound p bank h hit
  omega
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276807840)
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
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_46966.Model.Repr at out
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

def mono : List Gate := [⟨.or, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [14, 17]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 18⟩ (List.ofFn x) = posted x := by decide +kernel

theorem solve (low : Lower true fullRoots fullWord 12) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 18⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 13 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_46966

open PEqualNP.Outside.L_meta_46966 in
theorem PEqualNP.Outside.L_meta_46966 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276807840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact solve fullBound

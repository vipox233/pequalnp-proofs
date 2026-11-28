import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_34652.Model
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
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

end PEqualNP.Outside.L_meta_34652.Model

namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
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

def SBf (j : Nat) : Nat := [7, 8, 7, 7, 8, 8].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

def mirrorSteps : List Move := []

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
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
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

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
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

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

end PEqualNP.Outside.L_meta_34652

namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2424e8d1c00f062ea40234a6822a2604008561521900005003e08610406141106553943684022005930f00005873804300018400018304f241ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x530a0e4f2b0015002113352800003e015800540f00020c48003025002e003d474129081f07560300003300102c55262419573c37431d120d34444b32364a2d18453f00405017062038002f005204091e1a14314c4923002a0051393a1b115a421c0b5900224e460027003b054d160e020808d02286010000281063828b200c10000141800600090033e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x24000b8e00001c09a280b30788a8602802241462600030000400002001648000004010903255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc0500081445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2667+((h/30+packedAt s0K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 2 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x40118004220208008204820901304088105045
  | 2 => 0x52228891414810a0521244248449414612512
  | 3 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_34652
namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
def s1Pos : Nat → Bits
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 2 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 3 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 2 => 0xc4148944492854085064292124849286314512
  | 3 => 0x1a912289244a801ac80524849212530c28a28
  | 4 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
end PEqualNP.Outside.L_meta_34652
namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2018f0056000153071401002cb02320000000006054a24b8f1a8c9130e000000000000147c18000000000000e8000010241045080009c00454000003450da252987008206001800030202000c100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1b080005968006a98e888a9b90232289a0a2121fa1910ca59f131eac02818010802923ad929c9627a104801914800a2b000f0028952400272d178b118000000d00001702001a8024838b9a0107a68c0f801880958407000e261d94182b9c09002ca51d031e0d93a02a060519802aa80093021018004141011060002002468c020468b04040870004593b7294876d5290edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290656e52d06daa5a0eb94b41d6a9683ae32d075a65a0cf55241d719283ad325076ea2a0cf95041b7296636d52cc79a6598cf952319eaa463b5418c79a6498ed505319f2a0633d540c6dca418db54831bd2806379500c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af298815d53102dca4205b54840bb288817551102dca5985b54b30e6996613f544c278a898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a83885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xf1800000889081456000e401a75985180808d586548caa56195232a3993534cac56110d32b2580434ca4d6394b41a358e52d062d658cb41a998b51507853250531c554d410873141540218d584544c30c544c9309358c52443245250510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x99090ae3326a6994857398b5150682b88a899261415cc5250510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 75)*7) 7
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s2K3 (633+((h/5+packedAt s2K3 (608+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf3c78f3ffc7c7f1f8c470c7fe3f1f0f80f4cf
  | 1 => 0xf03f80fc63f9f8fe3f0780f8e3c7e7f1934b33
  | 3 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1040110004008020000100120090100001045
  | 1 => 0x10882222049101404204844848428241114112
  | 3 => 0x22035449492492a00dc80a92129054ac628c28
  | 4 => 0x44111009120080249151220003245024240e80
  | 5 => 0x88a26082403524c926a64ce4980080c95be000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_34652
namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xaa500009801e280284c782170aac01f062441c001cc23000068120450a92c743000049000000002200501194e0060036a8700486800b0010404004a003002203040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8c586200b67a72002c220000000000001c00004400004c00001e3a6a000050005a880070003400001800a6a84e00000000a40000520090000000ac000c206400000000040000000000001000a200688e38606c007c5600006e0046ae322e00001412000600660000b4000084000078005400000000004a000000000000b00074762a00b2002800080000000000008a0000000a009200005c02005ea03c000000000e98009c0000269400869a9e0000000000960024000048003e001a000000000000aa30407e000080160000004200820036000000000500000402000002000000000100050000010001000000000001000800b7294876d5290edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290656e52d06daa5a0eb94b41d6a9683ae32d075a65a0cf55241d719283ad325076ea2a0cf95041b7296636d52cc79a6598cf952319eaa463b5418c79a6498ed505319f2a0633d540c6dca418db54831bd2806379500c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af298815d53102dca4205b54840bb288817551102dca5985b54b30e6996613f544c278a898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a83885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8d02c08280c00000778020501c3600490000308028d586548caa56195232a3993534cac56110d32b2580434ca4d6394b41a358e52d062d658cb41a998b51507853250531c554d410873141540218d584544c30c544c9309358c52443245250510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x10d0090ae3326a6994857398b5150682b88a899261415cc5250510
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2724+((h/30+packedAt s3K4 (2484+(h % 30)*8) 8) % 213)*8) 8
  | 3 => packedAt s3K3 (633+((h/5+packedAt s3K3 (608+(h % 5)*5) 5) % 28)*5) 5
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf3c78f3ffc7c7f1f8c470c7fe3f1f0f80f4cf
  | 1 => 0xf03f80fc63f9f8fe3f0780f8e3c7e7f1934b33
  | 2 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1040110004008020000100120090100001045
  | 1 => 0x10882222049101404204844848428241114112
  | 2 => 0x22035449492492a00dc80a92129054ac628c28
  | 4 => 0x44111009120080249151220003245024240e80
  | 5 => 0x88a26082403524c926a64ce4980080c95be000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_34652
namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
def s4Pos : Nat → Bits
  | 0 => 0xc3cf3f9fff0e38fc7e318f8ffc71c7c784f0cf
  | 1 => 0xfc0fc7e38ff03f1f8fc1f1f1c381f9f99b4333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 5 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x410080010041008000020240104040001045
  | 1 => 0x44221108122090281040909088809091094112
  | 2 => 0x8880a201244402500292012411240124228428
  | 3 => 0x11040052488820012525240022492400540a80
  | 5 => 0xe228b45b00ed349a49f9c9c9380c34357fe000
  | _ => 0
end PEqualNP.Outside.L_meta_34652
namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
def s5Pos : Nat → Bits
  | 0 => 0x77c3de7e7c7f1c63e3f311e3f1c71cf9c530cf
  | 1 => 0xbbfc1f9f9f8fe07c7c7c1e3c7e381f3e4ac333
  | 2 => 0x3cffe01fe00fff807f8fe03f803fe03fb30c3c
  | 3 => 0xc0ffffe0000fffff800fffc0003fffc03c0fc0
  | 4 => 0xfffffffff00000000fffffffc000003ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4202008100840400004090010408001045
  | 1 => 0x40404001201008080020420080810004112
  | 2 => 0xc1488148092448094015202904924025130428
  | 3 => 0x1e91080152489040092a5480092492802c0a80
  | 4 => 0xefe211515800da52524f99324d80c2853fa000
  | _ => 0
end PEqualNP.Outside.L_meta_34652
namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12454f12967a3178f428dc2c00d40000001c8012890006c0402b3c2c0283218fb06e21a2e36485334c1c83b06000322a0002d289cbba1ac42803a60e04263889a520698a011830000240cc0006081800c00a0002ffd500bfe5402ff5500bfc54037fd4c09fe53037f54c09fc5302ffd0c09fe4302ff50c09fc43037fd4807fe52037f54807fc5202ffd0807fe4202ff50807fc42027fcc807fe32007f4c807fc32017fd44057f51017f94405fd51015f54405fc51017fd0405fe41017f50405fc41017fcc405fe31017f4c405fc31017fc8405fe21017f48405fc21037fd4003fe50037f54003fc5002ffd0003fe4002ff50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10017f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826410ff4413207ff8209903bff654c01d7fb2a600eff99530035fcca9803bfd654c01d7eb2a600eff19530035f8ca98037ff644c01b7fb22600dff9913002dfcc898037fd644c01b7eb22600dff1913002df8c898037ff544c01bff2a2600dff5513006ff8a898006ff634c009ffa9a6004ff94d30027bca698013fd534c01deea9a6004ff14d30027fe8698013fe434c009ef21a6004ff50d3006fba8698013fc434c001ffb126000bfd8930067fcc49800efe624c001feb12600cff1893001df8c49803bff524c019ff292600eff54930067f8a498037ff424c019ff212600dff50930067f88498013ff324c009ef9926004ff8c930027fa6498003dd324c009fe192600bffd853005dfec29802ffe614c0057f30a600bff5853005dfac29802ffc614c0057e30a600bffd453005efea29802ffe514c017fea8a600bdf5453005ff8a29802fff414c017ff20a600bff5053005ff88298013ff314c009ef98a6004ff8c530027fa629802fdd314c009fe18a600bffc853005ffc429802ffd214c017fe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe6098013fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fa204c003fe1026001ffc413000ffc2098007fa104c003fe882600bfe4413000ff82098027ff65480137fb2a4009ff99520035fcca90027fd65480137eb2a4009ff19520035f8ca90023ff64480117fb224008ff9912002dfcc890023fd64480117eb224008ff1912002df8c890023ff5448011ff2a24008ff55120047f8a890003ff63480017fb1a400aff98d20025fcc690003fd63480017eb1a400aff18d20025f8c690027ff5348015ff29a4009ff54d20057f8a690023ff4348015ff21a4008ff50d20057f88690006ff6248007ffa924003ff9492001fdca49000ffd5248013f6a924003ff1492001ffe849000ffe4248007f72124003ff50920047da849000ffc4248007ff9924003ff8c92001fdc649000ffd3248001f69924003ff0c92003ffec29001eff614800fff30a4002bf9852003ffac29001efd614800ffe30a4002bf1852003ffea29001f7f514800fff28a4007ff5452003efaa29001ffc514800fffa0a4007ff9052003ffa829001ffc414800fff98a4007ff8c52003ffa629001ffc3148007ff90a4003fbc852001ffc429000ffd214800ff690a4003ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001fe8c12000ffa6090003f93048003fe1824001ffc812001ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff42090007fd104800ffc8824001ff04120
  | 1 => 0x14364692b3e411000131e8f3418af300ac0014030c7623429278ff000fa48c1e40541068b61f930338914bc26450000b00015c950cc043bd3a0ac000f8740b93b1a42f00023120ec0ec003c0000e000000c720d330004642456264594c84a19454200351f40903c142e86421c0d030961cd0d3444e0082a144104312d2e01f2703928503104d81bd3d261194f0930dc2417025228d54d8203809b124882ac5d4a8074dca332c9f00d2623ca52c400000c133ceb160004c4e6000b51b4c44907b0602d49c664b11e364d42ecf7204b01a83f038783b47146c012fd1f02cfb17c8b37c303f4b32f4672409225c003a40000000000a9184001686b09c0045915000b2000002743c29910324fc00072000c847400000003840000050001112dd200000a000d200017214001310f000f643800048000005e268004112944900134003d0790f4424d0520006e1c0f54d419000cd10cea0743a0840031800054a24b8081809400031114e7000a811cde1a125330e43e00000000000d62113e44c622b4c21fcbc4fcb946102291051dc7c13c4036d1c280d7329083b82234c4437432314551b0d041cbe000000001c45c0042cfe488e242828368050102c10031201428230080000080000c0a061182c0e100002c000702800160900018080b1981c18000107c4a13090182a031981406050900000050000400020188016000180c3e33130401003000900202068400603000000206000142221050000c000604c000800818220d0982000000000c02050380c25ffb2a6412bfd9532097fcca9901afe654c825feb2a6412bf59532097f8ca9901afc654c823ffb226411bfd913208ffcc899016fe644c823feb226411bf5913208ff8c899016fc644c823ffaa26411ff9513208ffaa899047fc544c8077fb1a6404ffd4d32027fca699013fd534c809fe29a6404ffd0d32027fc8699013fd434c809fe21a6403bfd893201ffea49900ffe524c807fea926403ff1493201ffe849900ffe424c807fea126403ff1093201ffe6499013ef324c807ff1926403f78c93201ff8649900fdc324c807f61926403f30c932087fec299042ff614c821ff30a6402bf98532087fac299042fd614c821fe30a6402bf18532087fea2990437f514c821ff28a6410ff54532086faa299043fc514c821ffa0a6410ff90532087fa8299043fc414c809ff98a6404f7cc532027fc6299013fd314c821ee98a6404ff0c53201ffe429900fef214c807ff10a6403ff48532087da429900ffc214c801ffb026400bfd813207ffcc099006fe604c801feb02640fff1813200df8c09904bff504c81fff2826412ff5413207ff8a099047ff404c81fff2026411ff5013207ff88099013ff304c809ef9826404ff8c132027f8609900fff204c807f79026403ff8813201ff84099043ff104c81fff0
  | 2 => 0x218aa4e0342b88c238630005348475000f10581b0188229ce838d392d05b000003944b000dc000004a0003c8890
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb705893000ddc764c93001edc764c93000cdc764c930115df754c930115dd754c93010ddf744c93010ddd744c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930067cc624c93001ecc624c930105df714c930105dd714c9300fedf614c9300fedd614c9300ff5f514c9300ff5d514c930067cf214c9300ffcd214c930007db704c93000dde704c93000ddc704c93007fd8704c930026df604c930027db604c93007fcf204c93007fda204c93007fda104c9300ffd9104c930024fe76d8d20056de63d8d20004ff75d8d20034fe75d8d20004fd75d8d20034fc75d8d20004ff74d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2007cfd73d8d20056de43d8d20006dd43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d200f6df32d8d200f6dd32d8d20004ff71d8d20014fe71d8d20004fd71d8d20014fc71d8d200067f51d8d200067d51d8d20006de31d8d20056dc31d8d200f6ef21d8d20006ed21d8d2001cff70d8d2000cfe70d8d2001cfd70d8d2000cfc70d8d200e6df30d8d200e6dd30d8d200e6fa10d8d20006f910d8d20024ff7658d20056dc6358d200ddef7258d200edfb7058d20004ff7558d20034fe7558d20004fd7558d20034fc7558d20004ff7458d2002cfe7458d20004fd7458d2002cfc7458d200e4ff7358d20006df7358d200dcff7258d20006ef7258d20004ff7158d20014fe7158d20004fd7158d20014fc7158d200067f5158d200067d5158d20056df3158d20006dd3158d20066ef2158d20006ed2158d2007cff7058d20006fb7058d2007efa1058d20006f91058d2000dec764c920026ec764c92000cec764c9200d5ef754c9200d5ed754c9200cdef744c9200cded744c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920057cc634c920026cc634c9200c5ef714c9200c5ed714c9200beef614c9200beed614c9200bf6f514c9200bf6d514c920057cf314c9200bfcd314c920007eb704c92000dee704c92000dec704c92007fe8704c92001eef604c92001feb604c92007fcf304c92007fea304c92007fcd304c92007fea104c9200bfe9104c92001df8764c120026f8764c12001cf8764c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120057d8634c120057da534c1200b7d9534c120057da434c1200afd9434c120007eb724c12001dfa724c12001df8724c120067e8724c12000efb624c12000feb624c120067ea524c1200b7e9524c120067ea424c1200afe9424c120067db324c120067ea324c120067d9324c120057e9324c120007c9324c1200a5fb714c1200a5f9714c12009efb614c12009ef9614c12009f7b514c12009f79514c120057db314c12009fd9314c120067eb214c12009fe9214c120
  | 1 => 0x7f661540000000000062528007a00248000063680000061128000000228013000002497200001487e00000016c7c68b1400002e80000823db71081b730000094001dc000c2b0015e9f690c4000005998484655000009e002553a5e091a4f2bb672257a0000099642967b6106006395c0a724700000320012da6a70000000001b2fc006f00000000000064fa8c6200098ab0022800e10000000dd001cc000000000000000144d00438af838000013400000019c000000000000000024b000002043000431b000ca0990c8e2100000001d0032c00000008800a8208349c0000001ca00000000000000000000530000000002c1683c000018440000000000000414800000002800000000000002b00000000183c080000000002c801c6d65ab7c000007800a6a3000000000000e0002000000000000000da0000001421700000000046b20720000005ce1654854006e1600000000000000004d8004e00002e000003200000003ab8000000036404000000000001b98068e200354000000000b800088b8ca000022c006b0020000000000000000037800000000000033b00000002d028009a03a5c00a2118cd9a2a6ba45a800603253800000a000ae74368004800000000000000002d250ac0000001511070000e860001f00000960014000000000186000023c00443d1a966004800000c14297d0e99002818c5b00001620000001789356ae8007421068fcdb0000000000013c3e000000000001a80000b71d8005e0e3c000000072000000180000020500802000000404010000000000181000030080002010080800000100002030000c00000000000000000004000000000000100406070000c0003000040000000080203020040a0100000020102014000100cfe76d81320efcc32d813207efa60d8132004ff75d8132034fe75d8132004fd75d8132034fc75d8132004ff74d813202cfe74d8132004fd74d813202cfc74d813201cfd73d813200cfc73d8132024fd72d813200cfc72d8132004ff71d8132014fe71d8132004fd71d8132014fc71d81320067f51d81320067d51d813211edf31d8132006dd31d81320eeef21d8132006ed21d813207efa30d813207efa20d8132067cc325813207ef8605813201cfe76d8930066ee62d8930004ff75d8930034fe75d8930004fd75d8930034fc75d8930004ff74d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930066ee42d8930006ed42d8930066ee32d8930126ed32d8930004ff71d8930014fe71d8930004fd71d8930014fc71d89300067f51d89300067d51d8930126df31d8930006dd31d8930006ee21d8930066ec21d893000cfe70d8930024fd70d893000cfc70d89300deef20d89300defa10d8930006f910d8930066ec625893011df
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9006003856c940a00b000000e4d8e00f01a61e088130c0001a6c0121400d0b8b00b402500c508d3a013a238000b560a802e1001b914030b3b0a78c800e019955e0091f08e94a30808400030000200060000c0014100020010162fa1375d81320045ec26ebb02640687e85dd3604c8010fb0bba6c0990031ddc551d81320163a38aa3b026400ec531487604c8010ff0aba6c49801a1f21574d893002c77c3a85b126000ec531887624c001ce2a2886c498003b44c510d89300077110a21b126003ace86d89324c0010ff0aba6c69001a1f21574d8d2002c6fc3a87b1a4000ec6314876348001ce2a2886c690003b48c510d8d200077090a21b1a400087f855d1634800d0f90aba2c6900023de057458d200147a40ae8b1a40008df835c563480011df04b8ac6900031ddc55158d200163a38aa2b1a40028dc874c563480051d90e90ac690003b14c52158d2000c7d43ee0b1a40028f8874416348001ce2a2882c690003b44c51058d200077090a20b1a4004ace86d8d32480037910e992609000f7221d324c12000de5432649824001bc8864c93048009d910c9926090013b2dd9324c12001ee53b2649824003dc8764c93048009d90ec992609000f321d9324c12014de5c2a649824029bc9854c930480517970899260900a2f2611324c12013de5c0a649824027bc9814c9304804db96e2992609009b725c5324c12012f65b0a649824025ec9614c9304804be96a29926090097d2545324c120
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x5870875451058d20
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x98a
  | 8 => 0x98d
  | 9 => 0x98e
  | 10 => 0x98c
  | 11 => 0x9ca
  | 12 => 0x9cb
  | 13 => 0x9cd
  | 14 => 0x9ce
  | 15 => 0xcc9
  | 16 => 0xcca
  | 17 => 0xccd
  | 18 => 0xcce
  | 19 => 0x9c992
  | 20 => 0x989d2
  | 21 => 0x9c995
  | 22 => 0x9c996
  | 23 => 0xcc992
  | 24 => 0x98cd2
  | 25 => 0x98cd5
  | 26 => 0x98cd6
  | 27 => 0x1709
  | 28 => 0x15c9
  | 29 => 0x168b
  | 30 => 0x12cb
  | 31 => 0xcc9d2
  | 32 => 0x9ccd2
  | 33 => 0x9ccd5
  | 34 => 0x9ccd6
  | 35 => 0x150c
  | 36 => 0x128c
  | 37 => 0xcc9c99a
  | 38 => 0xcc989da
  | 39 => 0x9c98cda
  | 40 => 0x9c98cdd
  | 41 => 0x9c98cde
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 322
  | 6 => 233
  | 5 => 61
  | 4 => 1
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (12877+((h/107+packedAt gbK7 (11914+(h % 107)*9) 9) % 387)*10) 10
  | 6 => packedAt gbK6 (11877+((h/77+packedAt gbK6 (11184+(h % 77)*9) 9) % 492)*9) 9
  | 5 => packedAt gbK5 (3739+((h/20+packedAt gbK5 (3599+(h % 20)*7) 7) % 81)*7) 7
  | 4 => packedAt gbK4 (71+((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x88e00c63e3ff311e3f0e38387e1f0013c530cf
  | 1 => 0xf00707c7c70c1e3c7f1c03f8fe3086d0ac333
  | 2 => 0xf0007f807f80fe03f801ffc00ffc318e330c3c
  | 3 => 0x7fff8000fffc0001fffff000c1f03c0fc0
  | 4 => 0xffff80000000fffffffe00000000fe003ff000
  | 5 => 0xffffffffffff0000000000000000ffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x200000809000040900080802000000401045
  | 1 => 0x9041024242200204280401204820825004112
  | 2 => 0x9009248049045202902492800958308a130428
  | 3 => 0x1249490008a548004925256000c1502c0a80
  | 4 => 0xa24300000000f993246c0181204852003fa000
  | 5 => 0x4c9c7e72724e0000008006064192adff800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_34652
namespace PEqualNP.Outside.L_meta_34652
open PEqualNP.Outside.L_meta_34652.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 16 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 16 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 61 := (concat bgb_5_0 bgb_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 233 := (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_128 : Interval gbAtlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_160 : Interval gbAtlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_224 : Interval gbAtlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_256 : Interval gbAtlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_320 : Interval gbAtlas 7 320 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 322 := (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
  · exact allgb_9 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def codeMove (moveMax code : Nat) : Fin (moveMax + 1) := ⟨code % (moveMax + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def packedLinks {moveMax : Nat} (g : Atlas) (moves : Fin (moveMax + 1) → List Move) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / (moveMax + 1)
  if row < count g k then
    [(vals g k row).map (movedWord (moves (codeMove moveMax code)).reverse)]
  else []

theorem packedLinks_sound {moveMax : Nat} {g : Atlas} {moves : Fin (moveMax + 1) → List Move} {k : Nat}
    (aut : ∀ m, autoOK (target g) (moves m) = true)
    (rows : ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset)
    (tag : Nat) (xs : List Sig) (inLink : xs ∈ packedLinks g moves k tag) :
    Impossible true (target g) k xs.toFinset := by
  simp only [packedLinks] at inLink
  split at inLink
  next valid =>
    obtain rfl := List.mem_singleton.mp inLink
    exact rotate_excluded (rows _ valid) _ (aut _)
  next => simp at inLink

def checkPackedRow {moveMax : Nat} (g : Atlas) (moves : Fin (moveMax + 1) → List Move) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  decide vs.Nodup && !vs.contains (target g) &&
    testAll (k,ws.length,ws,preCov true ws,[],packedLinks g moves (k-1)) ws

theorem checkedPackedRow {moveMax : Nat} {g : Atlas} {moves : Fin (moveMax + 1) → List Move} {k i : Nat}
    {r s : Fin 152 → Row} (pairs : properPairs (target g) r s)
    (faith : ∀ a ∈ first g, faithful r s a)
    (aut : ∀ m, autoOK (target g) (moves m) = true)
    (prev : ∀ j < count g (k-1), Impossible true (target g) (k-1) (vals g (k-1) j).toFinset)
    (chk : checkPackedRow g moves k i = true) :
    Impossible true (target g) k (vals g k i).toFinset := by
  simp only [checkPackedRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
    List.contains_eq_mem,decide_eq_false_iff_not] at chk
  apply node_sound (raw:=roots g) pairs _ chk.1.1 chk.1.2 _ _ chk.2
  · intro a ha
    exact decode_faithful _ _ _ _ _ faith _ ((selectLive_sub _ _).subset ha)
  · simp
  · exact packedLinks_sound aut prev

theorem checkedPacked {moveMax : Nat} {g : Atlas} {moves : Fin (moveMax + 1) → List Move} {r s : Fin 152 → Row}
    (pairs : properPairs (target g) r s) (faith : ∀ a ∈ first g, faithful r s a)
    (aut : ∀ m, autoOK (target g) (moves m) = true)
    (noneAtZero : count g 0 = 0) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkPackedRow g moves l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    cases k with
    | zero => exact False.elim (Nat.not_lt_zero _ (noneAtZero ▸ hi))
    | succ k =>
      apply checkedPackedRow pairs faith aut _ (good _ le_rfl i hi)
      simpa only [Nat.succ_sub_one] using ih k (by omega) (fun l le => good l (by omega))

def PackedInterval {moveMax : Nat} (g : Atlas) (moves : Fin (moveMax + 1) → List Move) (k start n : Nat) :=
  ∀ i : Nat, start ≤ i → i < start+n → checkPackedRow g moves k i = true

theorem packed_range {moveMax : Nat} {moves : Fin (moveMax + 1) → List Move} {g k a n} (h : segment (checkPackedRow g moves k) a n = true) :
    PackedInterval g moves k a n := by
  intro i lo hi
  exact segmentRange h i lo hi

theorem packed_concat {moveMax : Nat} {moves : Fin (moveMax + 1) → List Move} {g k a m n}
    (x : PackedInterval g moves k a m) (y : PackedInterval g moves k (a+m) n) :
    PackedInterval g moves k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

theorem frozenPacked {moveMax : Nat} {g : Atlas} {moves : Fin (moveMax + 1) → List Move} {r s : Fin 152 → Row}
    (pairs : properPairs (target g) r s) (faith : ∀ a ∈ first g, faithful r s a)
    (aut : ∀ m, autoOK (target g) (moves m) = true)
    (noneAtZero : count g 0 = 0)
    (good : ∀ l ≤ top g, ∀ i < count g l, checkPackedRow g moves l i = true)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checkedPacked pairs faith aut noneAtZero _ good 0 row

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedMoves : Fin 8 → List Move := ![[], [swapRows 84], [swapRows 50], [swapRows 50, swapRows 84], [swapRows 66, swapRows 83], [swapRows 66, swapRows 83, swapRows 50], [swapRows 82, swapRows 67, swapRows 50], [swapRows 82, swapRows 67]]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedK2 : Nat → Nat
  | 0 => 0x941831d9215402192184dcd2154021
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedI2 : Nat → Nat
  | 0 => 0x1104820
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedK3 : Nat → Nat
  | 0 => 0x382aa26498843295d36348421e0aa8a9a4210cc57318121087a129a42a8043d054d2154021a62e918aa010d61728c550087a099262a8043581d92154021ac6e690aa010d61734855008731a92c010c21835916314910c92c6b00a4886256414a31442b13ac4310221981952148110ca2a6b004208661525802104322a98c488021191d95244010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedI3 : Nat → Nat
  | 0 => 0x9028817019b0803809b04851b058b0b0b08891b0b060b0a00839104018a898002050b012b0b08978592a683001232026932
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedK4 : Nat → Nat
  | 0 => 0x9b98a548c66d6295231cb98a548c72d6295231b998b318c6d66390531a7992314c66e62141319b588504c677654c4318f993538863d64d4e21ab592328863e64d4d218f59353486756194d219798c504865d63141218f993530863d64d4c219e983530867960d4c2197596530871e5494c21d5986530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c219d59631086b5648c421cd55231086e5628c421cd5513108756534c421f14c931086e562884219dd9521086e76548421d9d9521086e76348421b958d21087c65348421f154d21086e46048421d694e50087595394021f848650087652154021d694d50087595354021f848550087723154021dc4c550087722154021dc485500876121540219b98a53c426d6294f109798c52c425d6314b10ad59231c436452487108fd91538423c6454e10d9d4821842f16008610f8086208426e6294d109b58a534426f6254d109b189534425e63149109758c524426e6514910d398c524434d6314910da58052442b5648c510d914a3144364524c5109d99621443645288510d914921443685288110f888620442786548110f8485204436452841108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7951530431d5454c109b988530426d6214c109d984530425e63d48109758f520426d6594810d394e520434d5394810d394d520434d5354810d9185520425e63148109758c520427661148109e980520427565c8410d554f210436552c84109d59421043555308410d954821042f16008410d554f100436552c40109e596100436952840109dd9510043555344010b9189100436552440109ed9510043695244010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedI4 : Nat → Nat
  | 0 => 0xd82102981a4464800e01b09847e2215c0ca1bc2b0662ea0309f2634f414835a1721815442063d080b01687f08e2103c0840461a83981e1082103d88410817c8281b3081fe330840c019c2796169a2102d83e0929780383703a1761cc4a4626102fb7101a1f8c206d0421f20c1364a446035e541081f0420841081548525828a17925044108131b6c3a0750e08e14b63b8553902a08c0490986689e2001401e81c05c19a380964d8270732d01d80085a1082103698409692c1704c0f71dd3f01009885011c744d45901b97001a9f42b9340ae2100c97227e2101205f1041a421025108210078400426104206109c43c9d8310ee0e4010301080204205d0264c085084108210148840640d49986e03b10c0b0841080ac0a135078058930840a20884202f0a65ac1e82b4c6054420563021041380301607c22979012000049620e80108d0342240100305909220c420840a01202c01910821030974c222280001c50036008862a0c780403000900548001604f833c012080818008001000302181050c04782000860000042820004086000020e0600b002208180
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedK5 : Nat → Nat
  | 0 => 0x5f95231df2a4633e548c6faa918ef552319eaa4637d538c6fca518df54a31bf28c63f6418c7ee6318df94231bea84637f524c6f8a498fd90531faa0a63de314c6fea098df14131bf290637d520c6fca218fd8c431fa988637e500c6faa018dfd4e21bf29c437d53886f8a710df54a21f719443ed32886fca310fdc8621bf284437d50886fea690df94d21bea9a437c53487dc4290dfd4121be282437f53086fca610f794c21af298437d53087baa610d754c21be298437e51087ec6210fd4c421fb10843f521087ca4210df94021fd280437a50086faa010fe54021bca80437e53c42faa7885f14f10bf296217d52c42f8a5887d8c710fa98e21f621c43ea43885fd4e10bf29c217d53842fea5085f94a10bea94217d51843ee43087d08610bf28421fa20843ee21087ec4210bfa9a217e53442faa6885f14d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedI5 : Nat → Nat
  | 0 => 0x263730704f432e290df1ae228652641003745105c0a81b1502dc174159542244242a93b0b84c02c81f0721e81886500005c1b9340da0a8a102ac3c4710a07484216c1980648e0642984c0c49a09d0200d412c099260db1882ca4a0205f01540c0846143485c8020282f0441081e41b8850c00f09184d4ce0bc0782506c13c4281510a16e4287429685f0d84d66a01c201172ce57c311512a45ce27916082534b08540aa1984281b4780c14288501a139400850489fc3316850a0ecc288505245e4287209a1ac4283f0e2214428634162143f01429f0f83c08510a2144281110a1602d08503000c428850201584280f50a21432c8510a0548303810a1404284a4ba5b2261040de015428490a641442868044078318850e80380e0850c09d42b81a10a1689411e8ec008090850ee0c5138632c8214140394b82042302c03a13820868cb644c3d83b8d81da089728991313ac481042141580808621441862d0a1589201f30a0b43e8850f31480b1850e0008a0e107008000014041de03542c3810008d8d006448120304070204f020a18104160c083263c10706100804404080001020b0a10103343c19206100060e1c583
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedK6 : Nat → Nat
  | 0 => 0xfe31fd31fc31fe21fd21fc21ff10fe10fd10fc10
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedI6 : Nat → Nat
  | 0 => 0x1228506d425d0a140c4210120d098ec050a009d499a7a816a0683146441c2c86d06409d4123024e4520954280e513ce502316307e042f10
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedK7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedI7 : Nat → Nat
  | 0 => 0x10
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedCount : Nat → Nat
  | 2 => 2
  | 3 => 22
  | 4 => 132
  | 5 => 133
  | 6 => 10
  | 7 => 1
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedRecord (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1PackedK2 (i*60) 60
  | 3 => packedAt s1PackedK3 (i*49) 49
  | 4 => packedAt s1PackedK4 (i*38) 38
  | 5 => packedAt s1PackedK5 (i*27) 27
  | 6 => packedAt s1PackedK6 (i*16) 16
  | 7 => packedAt s1PackedK7 (i*5) 5
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1PackedLocate (k tag : Nat) : Nat :=
  match k with
  | 2 =>
    let d := packedAt s1PackedI2 (tag % 1*1) 1
    packedAt s1PackedI2 (1+((tag/1+d)%5)*5) 5
  | 3 =>
    let d := packedAt s1PackedI3 (tag % 11*4) 4
    packedAt s1PackedI3 (44+((tag/11+d)%44)*8) 8
  | 4 =>
    let d := packedAt s1PackedI4 (tag % 70*7) 7
    packedAt s1PackedI4 (490+((tag/70+d)%253)*11) 11
  | 5 =>
    let d := packedAt s1PackedI5 (tag % 74*7) 7
    packedAt s1PackedI5 (518+((tag/74+d)%267)*11) 11
  | 6 =>
    let d := packedAt s1PackedI6 (tag % 14*4) 4
    packedAt s1PackedI6 (56+((tag/14+d)%55)*7) 7
  | 7 =>
    let d := packedAt s1PackedI7 (tag % 1*1) 1
    packedAt s1PackedI7 (1+((tag/1+d)%1)*4) 4
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s1Packed : Atlas :=
  ⟨7, rawDecor 61 s1Pos s1Neg, 0xfffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0, s1PackedCount, s1PackedRecord, (fun _ _ => 0), s1PackedLocate⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1PackedAuto (m : Fin 8) : autoOK (target s1Packed) (s1PackedMoves m) = true := by
  fin_cases m <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1PackedPairs : properPairs (target s1Packed) (asRow s1Pos) (asRow s1Neg) := by
  unfold properPairs
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_2_0 : PackedInterval s1Packed s1PackedMoves 2 0 2 :=
  packed_range (n:=2) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_level_2 : PackedInterval s1Packed s1PackedMoves 2 0 2 :=
  s1p_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_3_0 : PackedInterval s1Packed s1PackedMoves 3 0 22 :=
  packed_range (n:=22) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_level_3 : PackedInterval s1Packed s1PackedMoves 3 0 22 :=
  s1p_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_4_0 : PackedInterval s1Packed s1PackedMoves 4 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_4_32 : PackedInterval s1Packed s1PackedMoves 4 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_4_64 : PackedInterval s1Packed s1PackedMoves 4 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_4_96 : PackedInterval s1Packed s1PackedMoves 4 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_4_128 : PackedInterval s1Packed s1PackedMoves 4 128 4 :=
  packed_range (n:=4) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_level_4 : PackedInterval s1Packed s1PackedMoves 4 0 132 :=
  (packed_concat (packed_concat s1p_4_0 s1p_4_32) (packed_concat s1p_4_64 (packed_concat s1p_4_96 s1p_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_5_0 : PackedInterval s1Packed s1PackedMoves 5 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_5_32 : PackedInterval s1Packed s1PackedMoves 5 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_5_64 : PackedInterval s1Packed s1PackedMoves 5 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_5_96 : PackedInterval s1Packed s1PackedMoves 5 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_5_128 : PackedInterval s1Packed s1PackedMoves 5 128 5 :=
  packed_range (n:=5) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_level_5 : PackedInterval s1Packed s1PackedMoves 5 0 133 :=
  (packed_concat (packed_concat s1p_5_0 s1p_5_32) (packed_concat s1p_5_64 (packed_concat s1p_5_96 s1p_5_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_6_0 : PackedInterval s1Packed s1PackedMoves 6 0 10 :=
  packed_range (n:=10) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_level_6 : PackedInterval s1Packed s1PackedMoves 6 0 10 :=
  s1p_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_7_0 : PackedInterval s1Packed s1PackedMoves 7 0 1 :=
  packed_range (n:=1) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1p_level_7 : PackedInterval s1Packed s1PackedMoves 7 0 1 :=
  s1p_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1PackedComplete : ∀ k ≤ top s1Packed, ∀ i < count s1Packed k,
    checkPackedRow s1Packed s1PackedMoves k i = true := by
  intro k hk i hi
  have h7 : k ≤ 7 := hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hi)
  · exact False.elim (Nat.not_lt_zero _ hi)
  · exact s1p_level_2 i (by omega) hi
  · exact s1p_level_3 i (by omega) hi
  · exact s1p_level_4 i (by omega) hi
  · exact s1p_level_5 i (by omega) hi
  · exact s1p_level_6 i (by omega) hi
  · exact s1p_level_7 i (by omega) hi

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s1PackedLower : Lower true (roots s1Packed) (target s1Packed) 8 := by
  exact frozenPacked s1PackedPairs (raw_faithful 61 s1Pos s1Neg) s1PackedAuto (by rfl)
    s1PackedComplete (by decide +kernel) (by decide)
    [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedMoves : Fin 6 → List Move := ![[], [swapRows 50], [swapRows 33], [swapRows 33, swapRows 49], [swapRows 49, swapRows 33], [swapRows 49]]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedK2 : Nat → Nat
  | 0 => 0x905879915348421c057654f4348421b01839d12154021b0183191215402192187d0d2154021c05735886254440c057558d2108440a058654d2108440a21854856008440e01534856008440891831c161d0910c82735c86050510c81735c86050510891831c16488510891831c16448510891831d94188110921875484044010d01735484044010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedI2 : Nat → Nat
  | 0 => 0x366c85680b6499963c55b12ec1db0630107894831800149d50307d9a0508902c01
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedK3 : Nat → Nat
  | 0 => 0x83ae6302a5a0e0e635885050706b1ac428283075cc6055221c2cc6b0ca890c1d73181544861c382caa1a43465c05350d2183ae7b2a8290ce170189314860eb9cc9a8243075cc6055021c2aa6b0e8610f0553d092108782a9a8490843495d66448421b0ae73224210d277559121086b0b86a690843515d65348421e0ca8a9a4210f055454d21087833a2a690843c15d15348421e0cc8a9a4210f056454d2108652bb68690843c154f4348421e0aa6a1a4210f4153486500868cb98c928043075cc6454021e44a890aa010f215448550087a129a42a8043d054d2154021a32e6322a010d3171d0d5008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e468690aa010f2143485500860fb9aca90c81895952108640d0ac690843206a121580219028ab9ea528881459cf5254440a2ae7a92a22052575949511038329ca4a8881c194d5254440e0aa6a92a22051673189511028ab98c4a8881895886254440a64e0312a220526721815110292b90c0a88810bdd95214440c1cc6a90a22060d635485110312a94c228881899895114440c4ac4a88a22062952980511020eb9ccb10881075ce650844083aeb318422041f7654c211020ebb2a6108818598d5108440c2ac6a884220525754842110312b2a4210881a158d2108440e0aa69084220619539802110318a8cc0108818654d6008440c62a2b0042206a1215802110390a92a328081075cf65d0b1094ae430283885457314921c4318b0cc1aa4218398d6215210c1ac6b10a908626625845484312b12c22a421075cc65d0a1083ae632a85084a9721814184258382c3a12212a5c860505109c2e430282884a57218141442d0b90c0a0a212c9d46050510c64ea30282886a2721814144258b90c0a0a21a85c86050510942e430282884b0705922144258382c890a21515cc5248510960eca0c40884b076505204433032a4290221685d1214811086eeab0c8008625525864004216b96ca200210d5c5651001085eeab10800842d769484004306b1ca4200210b5d95210010c1ac6a908008626525844004312a92c2200214c5d44044010b42e42022008721521011004298bae8288021c854b4144010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedI3 : Nat → Nat
  | 0 => 0xe53b630c30d86051d86864d24805d6306fa398c6318c630c09cabd5b98c5598c0a82d63150ad0e731b3e3b51b2c58c3938c4398c02460cbc4bd80304517e46941408f03cd05098a82e87b630bd9224b090db5c63f3a46f5caf65358c21e486318c062cc3255903e93588ef4b0d51c8e1624d2e3028630d820618258e41690829551df4f20dcf5048152a56852866b198c288876180327d5c251500943a1985754c5106d8c6311563015939322718c3100f6311104b8c631636318c01a690e61e5e8cd5bb2909e755ad771f82129857916786318c003441e30b1148445d80630ea90099630cfb0f74108ff598c009ccf06f712358c03123314b7631265945ab273557d830aa334e03c0186418d8c13a903a86c2ad1d228f91518c6318c63000378fc4618c204ae1778c026badbec4087000390100340151e00c820a0c00304080040c081091010007040c0002a3c00344102820410482180c29e1a08080001801f0c380800214005
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedK4 : Nat → Nat
  | 0 => 0x951103376254440cd98951103356254440cd18951103366054440cd18151102ae6214440ab588511032d5214440ad98451103355114440ae980511023e65884408f596211031d5388440cb54a211033551884408f595211031d5348440cd545211023e65084408f594211029e6308440a758c211031d5308440cd54421103a52108440ae98021102b96008440cd94650103355194040ce98250103b25194040ec546501023d6295310cd98654c423f62553108f99252c423d6494b108f99052c423d6414b109798c52c425d6314b108fd9742c423d65d0b10ad58742c423f6550b108f59542c43365450710add9541c43376550710add8941c42b46050710ad59221c42b56448710d914921c42ad6210310ad58440c423d62d5210cd587548433a60d52109b988548426d6215210ab588548432e62152108f588548432d62152108b58854843356115210ce980548423e6494a108f592528423f6454a108f191528423e65d0a108f197428423e6550a108f195428432e5250a10cb54942842ba60d0610ae18141842b56190210ab58840842b56110210cdd53108423d62d51108f992544423e65151108f588544433561151108f980544423c60151108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910ad587424423e65509108f195424423e65d0510ae98341442b56490510cd152414423c6550510ae18141442746550510bc18141443376550510cd19541442346550510add8941443b36050510ad18141443b06050510ac18141442b56488510ad591214436452485108f996404423e6510110ab58840442b56110110ec50620442786548110ec50520443e12148110ec50710442b764841109b98b540426d62d50108f596540423d62950108fd89540423f61550108f585540423e64150109b988540426d62150109d984540423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520432e6494810cb592520432e5454810cb551520434e5354810d354d520432e6454810cb591520423e64148108f590520425e63148109758c520427661148109e980520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb549420423e64944108f592510423d65d0410cb94b410432d52d04108fd95410432e5250410cb549410433651504108fd96400423d6590010cb94a400432d5290010ad586400423f65100108f59440042ad6210010cb948400432d5210010ad584400433554c4010d954b10042796584010da54a10042776544010cd55110043655244010ec101100427b6544010da54910043b34144010
  | 1 => 0x72d52d08418fd95421063f65504419dd95411073654504418f58e548863e60952218fd8d548863c60552218f992538863d6494e218fd97438863d65d0e21ab58b438863f6550e218f59543886b561d0a21add85428863f64542218f191508865e63951219758e544869d6395121c798e544863d6395121c758e544861d63951218f586544873561951218f982544863f63551218fd85544873761551218f181544863e64d4d218f593534863e6494d218f592534863e6414d218f590534867a6014d219e580534863f65d0d218f597434863f6550d218f595434871f5350d21c714d43486ad62d05218fd95414863d6550521abd8941486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f58e540863e60950218fd8d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086b561d0c218fd95430863d6550c21c794d430871d5350c218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d554e21086e562884219dd9521087555348421e9d0921087a54248421b9d9521087676548421e999121087a56448421e995121087a55448421d9d4d21087c65348421d954d21087c55348421d154d21087a74348421e950d210873a5494021ce552500875a5394021d654e50087e12194021ced9250087386494021ced0e50087394394021ced06500873941940218fd91500863c6454021d9485500873a5454021ce551500875a5354021d654d50087e12154021ced9150087386454021ced0d50087394354021ced0550087394154021dc88550087712154021d8485500873551d0740cd94541903355150640ae983519033751946408fd8951902ae6214640ab58851902ba60146408f996219023d6588640cd546219023d6548640cd545219023e65086408f594219029e6308640a758c21903a52108640ae98021902b960086408f99741503375150540d994a51103665254440d954951103366454440cb94b411032d52d0440cd547411023d6590440cb54a41103355190440cb949411032d5250440cd945411032d5210440cd544411033551d00408fd95401033551500409ed9540102ae62d4440ab58b51102ba60d4440ad59651103375294440e994a511032e52544408fd8951103376554440cdd4951103365254440e994951103265254440cd54951103a55254440c954
  | 2 => 0xa798f52d069d63d4b41ad58752d063f6354b418f18152d063d6294341ab98850d06ad62143419b988505066d62141418f58f525063e60d4941ad58652506b76154941ad58351506ae6214141ab588505072e62141418f588505072d62141418b588505
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedI4 : Nat → Nat
  | 0 => 0x1782a98a98a98a98a98a98a9835aa98a98a98a98a98a98a98a98798a985aa810a98a98a98a9895aa98a98a98a98a98a98a98a98a98a98a98a697bc690a98a98a98a98a98a98a98a98a98a98906a98a98a98a98a98a98a98619a98a98a98a98a98a98960a988fa18ca98a980cca9834c64ea98a98a98a98a98a98a98a98a98a98a98a98882a98a983b5a98a98a98a98a9830c312a98a98a98a98a98a98a98a98a98a98a98186204a98a98a98a98a98a98a98a98a98a98a98a20a98a98169a98a98a98a98a9843949ba98a98a98a98366a98a98a98a98a98a98a981e0636114a98a98a98a98a98a98618a98a9896ea98a98a98a2161fa98a98a98a98a16a98a98a98a9896ca98a988dda98a98a98a98a98301a98316a988e84d09124b59dea2d2efa985d05c2a98a98a98a98a98a98a9825ea98290a98614139a98a98a982d6a98a98a98a987cb6de4c2942a980543ba042a98a98a98a982582dc08b25aa98a98a98a989d8a98a98600a98a98a98a9813e28ea9882ea98a98a9839638aa98a98a98a9867a196a98a98a9846f313a98a98a987c87a6a980cda98a98a98a98a986aea98a98744270a9870ea98a98a98a98a98a98a98a98a98a9850aa80a98a980d3a98a98a98822a98a980d849ea98a98a98a98a985c004ea98a980eba98a989a26a8a9851da98a98468246a98a98804a98a98a989249480b4594a626e46d4a98a9888ea98a98a98a98a98a98a98a98a98a987f2613a98a98a98a98a98a98a9859b402a98a98a98a98a98a98a98a981f409d006a98a98a98a98a98a989a80fd306a98a98a98a98a98390a98360055a98a98a98a98a9825ca98a98a98a98a98a98a98a984f9a98a988b2a98a98864a98a98a98145504a98a98a98a98a98a98a98a98a98a46a983249b0a98a98a9890fa98a98a980de7daa380a8a98516a98a98a98a98a98606a98a98a98a98a98a98a98a98a98a98a9850ba98a98a98a98a98a9895ea98a98a98a98a989b6a988525b25b87b0a98a98a98a98a98a98a98a98a98a98a98a98a98a98a98a9852fa98595a6ea9854ea98a985bfa98a98a98a98a98a98a98a987e0a98a98a9803705aa08a9847aa98a981c2a98a985d6a98a98a98a98a98a98a98a9865aa98a98a98060a98a9895ca98a98a98a98a98a98a98a98a98a98a98a98a98a98642a98a98a98a98a98192a98a98a98a98a98a5ca98a98a9833da98a98a98a98a982892883c006da98a98a98974373102a98a98a98a9804fa98a98788a98a98a98a9815ca981bd2011010507006202200100101503001300009000010003000004100503a4002101020003000080830111000060020100010202504000000300000000220000010000300050420101a420427010400011041000300011000010001201400001020010010020000100000000000220200000000000
  | 1 => 0xa98a98870a98a1b1561f3a98a98a98a980199c06ce90048658c5a8a4c330a98a98a98a98a980912e23f6a98a56a98a98a9810e672a98702876a98a98a98174a98a98a98a98379108a98a98a98a98a98a98a98199a98a98a98a987566c60843482aca98078444049a88976a985a7a98a98a98a98a982166fc8eea98a988a0a988d67d4a98a98840a98a98492a98494a98978792930a98a98a98a980fc1ec07233c268a98a98a98a98a98a260baa9857e57ca983145f4a98a98150a9832aa98a98a98a98a98a98a9873e6484a4598a984aa522637a9885890c8c4a98202846a98a984743384b3a9831e3971b6a98a98a98a984c8a98a984d4a98a9805875076aa980a354074a5caa986c0552554a98a98a98a98a98a98a98888318a98000a98a98a988a6a98a98a9800c5c456469c4d2a98a985d179a6ea336a98264a98678a987aca98163a98a98a98a98a98a98a98a98a98a98a987aaa98a98a9863da98342a982faa98a98a98a98a98a98a98a9819ea98a98a98062a98a98a984f8a98a98a98a98a98a98498a98a98a98a98a98a98a98a98a98a98a0e4aea98a98a98a9879e9cba98a9889a20aa98a98a985808e9a98a98a98a98a98a98a98a98a98a98a9833aa98222a98a98a984b0a98a98a98a98a98a98a984f2a980665faa98a98a98a277caa98a9802aa98a982c4a98a988164d5a98a98a98a9855ea98a9838ba98a98a98556a985cba98a98a983b634ea98a98a98a9867ea98a9823ba98a98a98a98a981c8408a9813fa98a98576a98a98a98a98a9881ca98a98a9885ea98a98a98a98a98a98a98a98073a98a98a981aca98a98a98a986a2a98a98a6fa98a98a98a98a98a98a98a98a98a9822e984894a98a9801e9d2a98a98a98654a98a982ee12066ea98a98a98a98446a98a9823aa982caa98a98a98a98a987e6a98a98a98a98a98a98a98a98a98a98a98a98a987f6a98a98a9819fa98a98a984e6a98a98a9859e44aa980c08df391546a98a989c6a98a98a98180218570a9836c57275c5301988ca6d8007918a98a98a98a98a98a98a98a98a984bc94ea9838473884c5d25584cea98a98550a98a98a98295624a98a98a98a98a98a98a98a98a98a98132a98a98a98a98462a98a985d7a98a98a98a985bca98a98a98a9886aa9872ca74a98a98a98a98a980eaa98a98a98786a98a98990a98a9827e5e8a98a2ca98a98a98a98a98a98a98018a98a98a14a86a9860ca986b4a98a98a98a98a988e42a00c7a98a98a98a98a98a98a98a98a98a98a983ae3b4696a983fca98a981e6a98a989fc4d6a98432a98a98a98a984d88efa98a98a98a98a98a9895404816aa989aea98a98a98a98a9841aa98378a98a98a98a98a98a98a98574532a98a98a98a98a98a98a98a985baa983a9a98a9821ca9807e73291ea98a98a98080505a985d4a98a98a983c
  | 2 => 0x5a9eaa98a98280a9853ba98a98a98a98a98684a98a98a98a982f4a98a98a98a39a983a2a98a98a98a98a98a98234a984a5a98a98a983c2a98a98a98a98a98a98a98a98426a98a98a98a98a98a9845c542517a98a98a98a987a4a98a98a98a98a98a98a9808aa985201ce200a98a980e4a98915a9829480a477a98a9887c9e4762a98a98a4aa98a98a98a98a98a98a98a98a98a9817a1f892a5651fea98a98a9854d438a446d29cc7f4a98a983dea98a98a98a98126354a98a98a98510a98a98a98a98a98a98a98a98a98a98a98a75a984548e23d3a9856aa98a98a98a98a98a98a98523a98a98a986f6518a98a98a9883aa98a98a987ce15da98a7aa98a98a98217a982b8a98a98a989562e8252a9861237f541a988f44f31b7a98a987fe4e03cca9252ea98a988f603ca98a98a98a98a98a989baa98194a98a98a98a9809ca98a98a983d2a98a98a98835a98493a98a8ca9861ea98a983f0a983a80c6a982d07f8a98a98a98a98a989b4a98030a98a98a98a98a98a98a98210a98a98a98a98144a98a98a98a98a98a98660a98a9871aa9851c1ff4ffa98a98a98a98a98a98a98a98414a98a98a98794a98a98a98228a98a98511a98a98a98a98a98a98a98a98a9827ca98a98a98a98a98456240242a9859aa98a98972a98a98a98a98a98a98a98a98a9851aa9810aa98138a98a98a98a985eea98a98a98a98774a9824c5962824aca98a98708a98a981aaa98a981c9a98a98a984200f0343a98a98a987b6036a9834aa98a98a98a98a98a98a98a98a98a98a981e8a98a98a9858aa98a98a98a98a98544a98a98a98a98a98a98300a98a98a985ac0d2a98a98a98a98480a98024a98a98a982b2a984e138577c52844043e76855f49f68aa980903e4a981da53a0f6096a98a9806ca98a985882764daa98582a983f8a9875e448a989f01cf02ba98a98a98a98a98a985bea98266a983c652483777aa9898a372a98a98a98a98a98a98a98a98a9824416ea98a98a98a98a98a98643547a9852aa9893c5341b0a3e9f642c5e2a98a98a98a98a9897ea02a98a98a98a98a9812ca98064a988d0a98a98a98a98a98a98a98a98a98666a98a98a98a98a9854c3d8a98a984fea981a4a98834a10a98a98a9868076ea98a98a9863ca98a98a98a98a98a98a98a98a98a98a98a9814aa98a98a98a981d4a98a98a98a98a98a98a98a98a980a2a98a98a98a98a50a98764a98a98a98442726a98a98a985a05a6a98a98a98a98a98a98a98a98a98a98a98403a98a98a98589a9810ca98a98a98a98a9837e26a1624eca98a98a98a98a983eba987c2526a98720a98a98a98a98a98a98a986baa98780a98a98a98a98a98a98a98a98a1aa9878ca98a98a98a98a988b8a98a9852ca98a98a98a98a98a98a9847046e7eca98a98a9845829a66c59c4b66743eaa98a98a98a98a98
  | 3 => 0x62aa98a98a5da9840e082012a98a98a98a98a98a98a98a98a98a98a98a98828a9851e42da98a98a98a98a98a98a68630529a98a98a63a98a985b9a98a98a98a98a98a98a98a98a98a988be11a056a982a6a98a98a98a98a98a981f2a9896658ea9899ca98a98a98a98a32a98a980f1a98a988dc0ae6f0a98a98a98168a981bc7148ac1e76cc936450a98452a98a98a98a98a98996a985dca98a982bea981b23b8a98a9848ca33a9839ca98a98a98a984db4
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedK5 : Nat → Nat
  | 0 => 0x2fca5a0df54b41dfa16837e50d06faa1a0efd4b41df29683bd52d067aa5a0ef14b41dfa8683be50d067ca1a0ef54341de286837d549067aa920df94a41bea9483bf42906fca320efd0641fba0c837e50906faa120dfd4941be29283bf425077c84a0ef50941fba0a83be41506fea0a0df14141dfa92833f525077ca4a0ef54941de29283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437e53886faa710efd0e21dea1c437d528877e8510ef50a21bf28c43bf418877a8310fd8c621fb90c437e50886faa110dfd5121bf2a243be544867ca890df55121deaa2433d54486f8a890dfd4d21bf29a437d53486f8a690efd0d21dea1a43bf414877a8290fd8c521fa98a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843bd43086fca210efd0421dea0843f621087ea4210f948421bf28043fa50086f4a010df54021fca80437950086fca3a05f54740dfa0e81bd41d02faa9205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa8c81be519037aa3204f54640de28c81be219037a43206f086409f284817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf28881f651102eca2205f54440faa888175511037e82206f90440dea0881bc41102fca0206fd0040fd20081bd40103f280206fd4440df28881b6511037aa2204f54440daa8881355110378a2206f88440de90881bc211037ca0204f94040dd280817f54c42fca9886f953109f2a6217d54c437aa9884f55310be2a6217e52c42faa5885f14b10dfa1621bd42c437e83887d90710dea0e21f541c436a83887d88710fa90e21be40c437881885fd5210dfaa4213f54842fca9085f55210be2a421bc5484278a9085fd4a10bf294217d528437e85086f50a10bea8c21bf418437a83085f94210df20421bc40843f441087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f52442fca4885f54910be29221bf424437a84886fd0510fb20a21bd41443ea82886d50510fb10a21f5214437c80886f10110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedI5 : Nat → Nat
  | 0 => 0xb640d0587a5107284b672700dc9f5b1cd98738896cc53c6f24f15090d2daa0275b11a71ffad44b0ab32b5701d4e48c6324c44a12cd52874c1ca3e3e6c4bb1f660c4270452d62701c921f662064a4b2b661d0570b1b2d35e48d3c9e9234d3b4ec1e9ae930559b054cd99758301824ca01b663527287636618a5d112b5433952c9aa82bb22cd81a85054aa4de9070a493699e679c88ed985f633d8d0d0887626d99b307e999d980f9bb2da57c6054926b3312c06021d5c9b33666cca6967b665b275c939594396181b6be3fc5044b36627ed98a6b666ccd99a42dc4269e82a348c56b0457b0f34a19c454531446412f733463210069a427a64d98366184360dfb662f64084caaf1e66a9b3366134c90f93662a09b6f18c6e186298d80f495b364b86465453184ab2ac406c3f9cb39e5fd69c1815765482027da66f97a28805ac010cc573ba5a4b79533de4ed9b1462e2c51b33664ff085352f7874bf4cf93e1c2d99661c63f6091b1a55432600d73666cca3130a64dfb240ea85a9e0910589ab6cc858363666ccd987b17c6ccd99b33666cc2e9b336640888843f661d24da8147b38ad47470c36cc2c0199782ccbc578f66386d9867b2de7ed98a1938e0c3b5b3241316a45b30bd696018b220a3585d9b318f3e08dcdb05e6cc0c3b335735ad99b31516cc3b6b707c290054d11132fad98e809b6ccd99865946ccd99b3240ecc9790e3276cc67fb3069384761a5c5d6557e41f198340b2846ab552ba24378e02d020524b664ce698fc117240529b307beb4444154d56ccd99468b7346086bc9735a053830b5d6ccd99b3167018d981e1e06c0d98332766ccd151eb66280ba01fa8b6cc36c1b0115cabddb336641ad99b3354c743417d656df47589c8230cd6e86490b1d4398a2a522f4705082286c130fb33666cc3fc1d98315c71c32b66126d9864ebb09041536b2c341a8cc626433c63539b662176a0b82d0eccd99b31bc525a5ad99125c42018c152073a09a8acaa1c7d5671d1067bb9b33660bb663b30516ccad0ccf665147498f13c642c48845911e166cd39e63f14998c4d61dc3491897548eab0a3b1053e115232468498b8758df0f02c8942028c6768e20273374c95927c09ca7810201273c5497b5dbd8295b33159f8a74425891f2a5c0f0882d6d9963b3c0fc72149f661684184c1776cc27cb613a6ccc3fb33666ccd99b31d416097ae05103d0841c1018214001080000206165811db20058000d8280120c0062cc000f201810600cc004100d19202a889d00141940a0872e0000501161030606000030078400024820500081810e107022c0011c0004102000070448040050a04200001c0070a00188026c1833e00b800004a0c000010200740010804a80041c0090664280040020504000000e186820008280020001c042009d0a14082060c007
  | 1 => 0x3660bed997a57e6cc9008a0c45beacdb311d4fe34409069c0e1f4fe1ce020169b3108000b2c2100918087db32706cc039b3022684
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedK6 : Nat → Nat
  | 0 => 0xff41bf41fe41fd41bd41fc41fe21fd21fc21ff40fe40be40fd40fc40bc40ff10fe10fd10fc10
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedI6 : Nat → Nat
  | 0 => 0x72d56b95ce5c8f54915b972e514c52e5cb972e5cb972e5cb972e5cb972e4f3972e5cb900c1c8b3de5cb97220fc372e5cb97211c8972e5cb672e5cb966992b90ae5cb90ee5cb972e543964e5caf72e5cb95805ca1eee527968e5c98149bcb172e5cb92ae5cb972e5c864be5cb9726dcb9729c93972e5cb972e413970e5ca172c0818405
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedK7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedI7 : Nat → Nat
  | 0 => 0xc
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedCount : Nat → Nat
  | 2 => 18
  | 3 => 132
  | 4 => 452
  | 5 => 290
  | 6 => 19
  | 7 => 1
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedRecord (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s4PackedK2 (i*60) 60
  | 3 => packedAt s4PackedK3 (i*49) 49
  | 4 => packedAt s4PackedK4 (i*38) 38
  | 5 => packedAt s4PackedK5 (i*27) 27
  | 6 => packedAt s4PackedK6 (i*16) 16
  | 7 => packedAt s4PackedK7 (i*5) 5
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4PackedLocate (k tag : Nat) : Nat :=
  match k with
  | 2 =>
    let d := packedAt s4PackedI2 (tag % 9*5) 5
    packedAt s4PackedI2 (45+((tag/9+d)%31)*7) 7
  | 3 =>
    let d := packedAt s4PackedI3 (tag % 67*7) 7
    packedAt s4PackedI3 (469+((tag/67+d)%241)*10) 10
  | 4 =>
    let d := packedAt s4PackedI4 (tag % 232*4) 4
    packedAt s4PackedI4 (928+((tag/232+d)%2089)*12) 12
  | 5 =>
    let d := packedAt s4PackedI5 (tag % 185*7) 7
    packedAt s4PackedI5 (1295+((tag/185+d)%665)*11) 11
  | 6 =>
    let d := packedAt s4PackedI6 (tag % 16*2) 2
    packedAt s4PackedI6 (32+((tag/16+d)%145)*7) 7
  | 7 =>
    let d := packedAt s4PackedI7 (tag % 1*1) 1
    packedAt s4PackedI7 (1+((tag/1+d)%1)*3) 3
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s4Packed : Atlas :=
  ⟨7, rawDecor 47 s4Pos s4Neg, 0xfeeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8, s4PackedCount, s4PackedRecord, (fun _ _ => 0), s4PackedLocate⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4PackedAuto (m : Fin 6) : autoOK (target s4Packed) (s4PackedMoves m) = true := by
  fin_cases m <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4PackedPairs : properPairs (target s4Packed) (asRow s4Pos) (asRow s4Neg) := by
  unfold properPairs
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_2_0 : PackedInterval s4Packed s4PackedMoves 2 0 18 :=
  packed_range (n:=18) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_level_2 : PackedInterval s4Packed s4PackedMoves 2 0 18 :=
  s4p_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_3_0 : PackedInterval s4Packed s4PackedMoves 3 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_3_32 : PackedInterval s4Packed s4PackedMoves 3 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_3_64 : PackedInterval s4Packed s4PackedMoves 3 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_3_96 : PackedInterval s4Packed s4PackedMoves 3 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_3_128 : PackedInterval s4Packed s4PackedMoves 3 128 4 :=
  packed_range (n:=4) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_level_3 : PackedInterval s4Packed s4PackedMoves 3 0 132 :=
  (packed_concat (packed_concat s4p_3_0 s4p_3_32) (packed_concat s4p_3_64 (packed_concat s4p_3_96 s4p_3_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_0 : PackedInterval s4Packed s4PackedMoves 4 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_32 : PackedInterval s4Packed s4PackedMoves 4 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_64 : PackedInterval s4Packed s4PackedMoves 4 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_96 : PackedInterval s4Packed s4PackedMoves 4 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_128 : PackedInterval s4Packed s4PackedMoves 4 128 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_160 : PackedInterval s4Packed s4PackedMoves 4 160 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_192 : PackedInterval s4Packed s4PackedMoves 4 192 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_224 : PackedInterval s4Packed s4PackedMoves 4 224 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_256 : PackedInterval s4Packed s4PackedMoves 4 256 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_288 : PackedInterval s4Packed s4PackedMoves 4 288 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_320 : PackedInterval s4Packed s4PackedMoves 4 320 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_352 : PackedInterval s4Packed s4PackedMoves 4 352 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_384 : PackedInterval s4Packed s4PackedMoves 4 384 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_416 : PackedInterval s4Packed s4PackedMoves 4 416 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_4_448 : PackedInterval s4Packed s4PackedMoves 4 448 4 :=
  packed_range (n:=4) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_level_4 : PackedInterval s4Packed s4PackedMoves 4 0 452 :=
  (packed_concat (packed_concat (packed_concat s4p_4_0 (packed_concat s4p_4_32 s4p_4_64)) (packed_concat (packed_concat s4p_4_96 s4p_4_128) (packed_concat s4p_4_160 s4p_4_192))) (packed_concat (packed_concat (packed_concat s4p_4_224 s4p_4_256) (packed_concat s4p_4_288 s4p_4_320)) (packed_concat (packed_concat s4p_4_352 s4p_4_384) (packed_concat s4p_4_416 s4p_4_448))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_0 : PackedInterval s4Packed s4PackedMoves 5 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_32 : PackedInterval s4Packed s4PackedMoves 5 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_64 : PackedInterval s4Packed s4PackedMoves 5 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_96 : PackedInterval s4Packed s4PackedMoves 5 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_128 : PackedInterval s4Packed s4PackedMoves 5 128 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_160 : PackedInterval s4Packed s4PackedMoves 5 160 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_192 : PackedInterval s4Packed s4PackedMoves 5 192 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_224 : PackedInterval s4Packed s4PackedMoves 5 224 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_256 : PackedInterval s4Packed s4PackedMoves 5 256 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_5_288 : PackedInterval s4Packed s4PackedMoves 5 288 2 :=
  packed_range (n:=2) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_level_5 : PackedInterval s4Packed s4PackedMoves 5 0 290 :=
  (packed_concat (packed_concat (packed_concat s4p_5_0 s4p_5_32) (packed_concat s4p_5_64 (packed_concat s4p_5_96 s4p_5_128))) (packed_concat (packed_concat s4p_5_160 s4p_5_192) (packed_concat s4p_5_224 (packed_concat s4p_5_256 s4p_5_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_6_0 : PackedInterval s4Packed s4PackedMoves 6 0 19 :=
  packed_range (n:=19) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_level_6 : PackedInterval s4Packed s4PackedMoves 6 0 19 :=
  s4p_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_7_0 : PackedInterval s4Packed s4PackedMoves 7 0 1 :=
  packed_range (n:=1) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4p_level_7 : PackedInterval s4Packed s4PackedMoves 7 0 1 :=
  s4p_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4PackedComplete : ∀ k ≤ top s4Packed, ∀ i < count s4Packed k,
    checkPackedRow s4Packed s4PackedMoves k i = true := by
  intro k hk i hi
  have h7 : k ≤ 7 := hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hi)
  · exact False.elim (Nat.not_lt_zero _ hi)
  · exact s4p_level_2 i (by omega) hi
  · exact s4p_level_3 i (by omega) hi
  · exact s4p_level_4 i (by omega) hi
  · exact s4p_level_5 i (by omega) hi
  · exact s4p_level_6 i (by omega) hi
  · exact s4p_level_7 i (by omega) hi

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s4PackedLower : Lower true (roots s4Packed) (target s4Packed) 8 := by
  exact frozenPacked s4PackedPairs (raw_faithful 47 s4Pos s4Neg) s4PackedAuto (by rfl)
    s4PackedComplete (by decide +kernel) (by decide)
    [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedMoves : Fin 4 → List Move := ![[], [swapRows 50], [swapRows 16], [swapRows 16, swapRows 50]]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedK2 : Nat → Nat
  | 0 => 0xc09725806054f42c11715806054f42b01844ca5154032b01844c95154032c05645c4534cb20c05645c4534c920c08655d1324c1209098754f4248020b0183d095148020909831d5424811091183dc95444010b01839d15244010921871915244010b018319152440109118754f4244010d017354b4244010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedI2 : Nat → Nat
  | 0 => 0x62034800164080d8614810041c41018405100d2620f02094901c0d0b03200
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedK3 : Nat → Nat
  | 0 => 0x286b90c0a9e85459c46054f42a2ae2302a7a16196018153d0b0aa9cc2286858554d6114342a1aeb31a841950f7558d420ca17baac899065235d3654c832a1aeb322641950f75591320ca47baac89906583dd5644c83291aecaa26419589744ca500ca8cb9e8528065435d13254032a56eaa12a019589744c9500cb852a264a8065c25513254032e428528aa01974132945500cb90a12a2a8065d04c95154032a32e7a12a01954973909500cb8521a84a8065c250d4254032a56e6a12a01970a73509500cb84b9a84a80654a5d23254032e1287192a019529744c9500cb85a1a64a8065c250d3254032a96e8992a01970a744c9500caa4ba264a8065c25d13254032a12e8992a01950d73991521020ebb4a7a10818358d52d0840a2ae7a14a22051573d095110306b1aa4208818a5496010440c1ac7314a99050e7395142c8246b9ecaa1641439cf6550b20a4ae229a859060d6414d32c82a2b88a699641075cc6454620a2ae229a86904c9731814248270b88c0a1241439cf6550920a4ae229a84905897318142482d0b88c0a124183590534c920a8ae229a649062865509304832432a6498241625d1324c12085ae4b2e861060e5358b4308306a9ac5a1841075ce649482083aed29e841041d7654f4208292b968728841455cf4294420a4ae5a1aa21051573d095108294bae8490041625cf4248020e12a7a12401072342545200820eb9cc92942107dcd62d5110c1cc6b10a88860d635885444314b12c02a2218c585601511083ae7324a48841d73197424420eb98caa12210b1d95250910a18e6a9284884e17218540442943aa84902212c5d061481109a2e630a408841d73d89540420eb9cc929021435ce6494810a1ae7322a40841d73d97420420fbaac7a1021075da53d081083aeca9e840860d6394b4204306b1aa5a1021685c86444010ac2e5aa220085317595110042993b2a8880214c1d95444010a66e4aa2200853174d4910042a8b9ea488021585d65244010e42a92922008722545491004390aa2a488021d094d5244010e82a6a922008722745491004390ba2a488021c8d915244010e40c8a92200853175d0910042c8b9e8488021c454f4244010e42a5a122008531755091004388a9a8488021c85494244010
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedI3 : Nat → Nat
  | 0 => 0x1bd86096860287f0805e8bd051c4390306f9505f2182d12c86114151a5571b8252184a2182861886008862180904841992002188605d8610c862188620486218862186621886218372186e888140f8272142a0ac4007c63984862101861846078862188619e86218862188621868a18862188621886218860312d5e02d938211ca860055121886164862188615886108861c23b60c4421886218821092f21811218860d40e21886178480e07f6188621869a1886218031765220086182862186ba18411d064218086183b14c8618a862181b218861da0d61807218861ce8601886218861603621886070860f486218632188602c65841862188621886218670c82913c60618682188616e862188621886218861c88621886090861aa8613d75a188621886218792183f218861c013618624047b218860b8026184d1f5860e85c9d286218860d01a218692180f2185d2183e58086218862185521863618861ac862188621862218861c63c6185f9f07d2183c05c861cc8621804618860c0862186d218311dc862188619486218861d88621886218262187e1858619a6d4cc862188616c0e6181313a86218862182c21828218619a886218266186c21886020862185a05823151040fd860341921886218862185c12486060861bc074748603d86218752187e5e842840862184c1408621847218260e10200311603c102230000210100010002020010004000000006211050200000
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedK4 : Nat → Nat
  | 0 => 0xe32482ad644c920d314d324832d42d45208f990514823d64145209798c514825d6314520ab59321483a9428c1209e19530483a9424c120f24c930483a942c81209798f540825d63d50209d987540827561d50208f596540823d63950208fd8d540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530823e6494c208f592530825d6594c20c7952530831d5494c20c7992530831d6494c20c7951530831d5454c20c7991530831d6454c208f990530823d6414c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c20ab58b430823f6550c208f595430831e5350c20c754d430823e64948208f592520823d65d0820a758f420831e53d0820c754f420823f6550820c794d420831d5350820cb94942083365494420cd55251083565394420d554e51083374394420cd50e51083374294420cd50a51083365454420cd55151083565354420d554d51083374354420cd50d51083374254420cd509510832d54c8020d354f200836551c8020d654e200837151880209bd95200832d5448020d354d200836551480209ed9520083595348020ead09200837151480209b988548426d62152108f992528423d6494a108f990528423d6414a109798c528425d6314a10a758f428432e5250a10cb54942843a942482108f58b544423e64951109b988544426d62151108f99454442ad6215110cb988544423d6215110cb588544422d6215110ce580544423e64949108f592524423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c524423e65d09108f197424429d63d09108f995424423c6550910cb949424432d5250910ce15240443b241901109e19540442f06150110ec50540442786548110ea50920442f06148110f8485204426e62d50109b58b540423d65950108f58a540423f62550108f990540426e62150109b588540427a60150108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810cb992520432d6494810cb951520432d5454810d394d520434d5354810cb991520432d64548108f990520423d64148109798c520425d63148109b988520427a60148108fd97420423d65d0810a758f420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb54942042796584010ce55210043695284010bc586100427b6544010ce55110043695244010bcd9510043736544010ecd9110043b06444010dcd5110043b25444010dc55110043b15444010cc55110043735244010f894910043715244010f854910043615244010ecd0910043b14244010
  | 1 => 0xaad60d4942a798c5050a9d6314142ad9845050ab56114142c798e5410b1d6395042c754f4310aad62d0c428fd954310a9d63d08428fd954210a6f6550842cb9514210b1d6395232ab58b438cb1e5490e32abd89438cb1f6550e32c7195438ca9f6250e32e3d89438cb8c6250e32a758f428cb2d54cca32c750d508ca6d62951328f58a544cb2d62951328b58a544ca3f6255132cbd89544ca9d63d09328fd95424ca3d6550932a7d8d424cb1d548c9328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329e983540ca7960d50328f596540cb2e62950328f990540ca7a60150329e580540ca3e64948328f592520ca3d65d0832a758f420ca6d6590832ab592420cacd63908328fd95420cb2e5450832e390d420cb8d4350832abd95420cb2f6550832abd8d420cb8e6350832e358d420cb2e5350832ab592320cacd638c832e350e320ca6f654c832ab591320cb8f434c832e350d320cacf654c832d3d95320cacf644c832e3991320cacd644c832e3591320ca8d644c832e3951320cb8d544c832ce952500cb395494032ea50a500cbc93294032dc946500cb3b4294032ce50a500cb2d4254032d34c9500cb3a5454032ce551500cba94254032f24c9500cb725154032dc545500cb3b4254032da909500cb394254032da509500cb294254032da8c9500cb693254032d24c9500ca9d63d0b40cb54b42d029d63d0a40cb949429032d5250a40a758f425032f52509409b988515026d6214540d394e521034e5354840d354d521032e6454840a758f421031e53d0840c754f421032d52d0840c794d421031d5350840cb94942103665294440d954a51103374294440cd50a51103665254440d954951103374254440cd509511023d6590440cb54a41103355190440cb54841102b96010440cb54b401033551d0040dc546401023f6550040cb549401033551500409ed95401037151500409798e54c825d6395320a758e54c831e63953208f58e54c831d63953208758e54c832e62953208fd8d54c823e6494f208f59253c823e6414f208f59053c82766114f209d58453c823f65d0f208f59743c82ad62d0f208fd9543c823d6550f20a758f42c832e5450b20abd9542c832f6550b20abd8d42c832e5350b20cb14d42c82ad648cb20e350e32c82ad644cb20d314d32c832d4254720cb55321c825e63152209758c548827661152209d584548823e6494e208f59253882ad62d0e20c794d438831d5350e20a758f428823f64546208f191518825e63951209758e544823e6494d208f592534823e6414d208f59053482766114d209d58453482ad62d0d20c7d4d434831c5350d20a758f42482ad64909209b19542482e86050920cbd95424832c6550920abd8d424832e5350920cb14d42483ab6050920ea18142482ad648c920e350
  | 2 => 0xc799153d0aad62d4f42c7d9553d0b1d6254f42c7d8153d0b1e6054f42c758153d0b1c6054f42c754c53d0a9e63d4342a758f50d0b1d53d4342c754e50d0b1d5354342a798c50d0a9d6314342c754c50d0ab66114342ad58450d0aad62d0e42a758f4290ace63d0a42ab98b4350aac6250d42b398f4250a5e63141429758c5050a7661141429d5845050b2d62d4d42ab58a5350aaf6254d42c754c5350a9e63d4942a758f5250aae63d4942e398f5250a8e63d4942e358f525
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedI4 : Nat → Nat
  | 0 => 0xa6bac3f402b47584cfece3cd3485bc8317904267481d1531ed00a85078c24e9469941c24a0721733ac1c04c8922f4758eb1921b172a1818e24a594be3d63ac758673481b4758eb14b3ac758c0928b36f58a35773ac0d81889f272405eb093bac758d191e2141058536c5b8138241bf7ac497540677445484c1222600484497d1dc37e891d108c0201b8f5066ca8bf56a29f1101e1d63ac758eb06063a3d1459ba023758b2b560bf0bd238479ae7581253e2c24b9571cb308514879d63ac758ce1d62e2069cf1d634002c179ab03e9807412f3ac300e41449720183a3b4316928eb0cc182f58cc9d6258f58eb1d63ac5e18f9d61fe758be1be4e2758d6988246758390882ad758323a537a6410c0ad2427583a8d6ba83e4bbaf21f0521083bc196578a6392668218e4547295458df99475c6cc71972334336eb1781546249d8e722e040120251ba2d1a1938186178558c126f444258232932f03512587262c7f6a20ba2c00b1aea74470c69009c06956c8672d67581a34e264758cfbd630575800bcc334990eb0e203282831b2d7ac5d8839d601275870bb859f40c870dc7ac09c931d62cc9b0eb03e7ac4f4cacfa24af40a11cf2b624cb60d4118640539d6158540728cc6ea758eb1513847580a2ef162758eb1b608a73e868533ac6d9313b1330dc07b99105ad500c98634e758969d619c050d49d628c3f0eb1b767e7144781706aa28b4bd61439011e48518e0093f0a4164710e31d63933aceb15b856340a2154a15df61a80e1b9f38a79273ac144260023ac344a65d618c758eb0af350758eb09d3ac4bd69901bac7580f1af3ac54c799683ac5293a1d62581fceb0c23ac1b6b39d6000c7d2f9505ec6843418204c0440a46b2283fabd84f0369224cd234585ed4192a6a71cc319ca25635e280050ca6dc5b8d82c655c3abac26a67cb20c900cd349990b170250a5adf2acaf5aa3852347001f1bb0ae2e811a2938e675ca83b39d4607ecb42941e80001d2be3341915d3601a52b15926ce45e181a332f58d33621463d0099491f60953b80f382568eb1962e6f58651831d42d44881f3a31a43d90031475850a22300cb82c86f3ac56a8c998291200219a76970a0ea9d62aaf58eb0dd9887589e33568238eeb1467ac06c3e94282a758201d6218c02187a30245b99060050d1e144035e2c00012fc1100c0c50600141a0060d98126005042a100002000d810204a02240030010380200c442090004000280098128484310e06485003450808100142e78b80005c0010440d130020003000c6000000011109490500300803854734025460c0004c030a4801f00000081e181030ea800c42741841828900000800214081812e1c011001008100103ac00002010c000001a6050130f828100040060008104020c00204342860a30004000408902045021414700
  | 1 => 0xeb0d64ccc404d01c3a11881980467aa04e91d60cc5665b1d615254aac18026e104eb18e67869882130648108eb1021d8758eb10800681c715d6252f58c61d63ac5fceb1d63ac75864145b6a758eb1d612035b21a3d0a43d3420033ac5d0eb1d63ac2cceb12745a4242a94eab11d826cd62ce92e0856d02b1506289e292d659b08e2cc51e249c9142530679d626694dcb8973a636c829693ac5807fcfe3ac61caa8a61365b83c0012404a47698a7ac4c91007c3072f8809d610e030eb05831e7582695c37c2800682e4543f9781d61ccec8925d614a0d0e13d612c2a5eb1c59a4208eb19b0b44305e8d51f70b8dc11b12a3c495a444b60e81eb936625f828bd46ab6a8eb1d61e31e4eb05c0703a45f9b91cc3783706d040d464e061576010c997447e44c736
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedK5 : Nat → Nat
  | 0 => 0x4857e5390afaa7216fd0e42bf29485bf4290bde85215f94242bea84857f5350af8a6a16fd0d42df21a85bd4350bde84a16f90942bfa82857c5050b7ea6a14fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf280857d5010afea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7196fd0e32ef21c65bd438cbba87196750e32bf29465bf428cb7a85197bcca32bf284657d508cafea8995f95132df2a2653e544cafaa8996f551329eaa2657c544cb7e84996f50932ef192657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94832dfa1065ee420cb7a84197b50832d6a1065ee320cbda6419734c832bf28065fa500caf4a0195f54032fca806579500cafca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e817d54902fca5205f54a40dfa1481bd42902fca3205f54640df20c817e509037e81207ed0240bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94840f7290816e52102faa4207b54840b6a9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bf29e417d53c82f8a7906fd0f20dea1e41bf42c83dc85906f50b20f6a1641ad42c83dc65907b4cb20bf28e417d51c83de43905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d538837e87106f50e20bea9441bf428837a85105f94620bea8c417e50883f461107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41bf434837a86906fd0920f721241bd42483da84906b50920f719241ed32482fea2905f14520f790a41ed21483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c530837e86106f50c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa88417e50083de40107e88020f690041f920082fea9085f95210beaa4217c54842fea5085f94a10bea94217c528437e85086f50a10bea8c217e50843f481087e50210fd10421f920843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4910bf292217d52442f8a4886fd0910dea1221fa40443f280887e88110fc90221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810bf28021fa10043f220087c44010
  | 1 => 0x2fca7a17794f42af29e857d53d0bbaa7a15754f42dfa1e857e50d0afaa1a16fd4f42df29e859e53d0b7aa7a14f54f42cea9e851d53d0b78a7a16fd4342df28685bd50d0b78a1a15f552429eaa
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedI5 : Nat → Nat
  | 0 => 0x628c5189114628c518a314628c0a8a314628c51848281667518a314628c518a314628c5189c14628c518a313f28c5180b52b28a474a313da8c518a3146121bf89690a064d188400768c3ac2982d28c518a31460f0518a314628c114a311e28c518a30cb1e03a5a313915cd18a304aa8c518a304868c518a30d74cc2520324118ad18a314628c5185a8ff0425180dabe28c518a307aa8c36da3146128d18a300c68c518a314628c011a314628c518a314628c1cca3092123518a31461e25186108462b5181894628c48ca31461d8518a314628c518a314628c518a314628c518a314628c518a301528c28aa314628c518a314628c518a3146176b3aa3146212518a314628c4e8a31460d5d18a314628c41ea314628c518a314628c518a311328c2400ba4b28c5180c34628c518a314628c2e55b14628c31ca31251cea22a314628c518a301123f5186234628c518a31460032a42b14628c5181b94628c5186e14628c518a314628c208a314628c20ca30ab28c518a314628c518a30a1158be1a31461150f8a30d08bc518a314628c518a303a2643245c54628c518a314628c1c2a31460e3518a314628c33ea310d68c51898ce028c518a30fc51d518a30c2a8c5180154628c518a314628c518a314628c518a3146056518a314628c518a30cb638518a314628c518a314628c518a3062248949a31461a2214a314628c464a314628c518a314628c518a314628c518a3116a8c518a30c128c29ca314628c518a31461ea204a301928c1b804a18dd0b46a31460c81fca314628c518a314628c518a30315c65183c81e68c118368b068c518a310c28c5189814628c5185d3461b28a08a44968c518a300d68c05ea31460d0518a314628c518a3146136414a304e28c518a314607a518a314628c518a314628c5181914628c25ca314628c518a314628c518a309a28c43c690b703e30c0810699c4b1a314628c518a31461a7518a314628c518a31461e8a78a314628c518a31460123b8a314628c518a31460c4b4aa308728c5181793b11e4caa310b1d45181a9460a42e1a314606b5181714628c3e4a31460701b02694628c1b7a3080a8c518a312e2404f0a30e5a8c41ca314628c518a314628c518579460c7518a314628c518a314628c518a314628c518a31461532a8a314628c518a30d5404518a314628c3bca314628c00e1e14628c51893d4628c33ca314628c5184894628c518a314628c518a314628c518a314628c518a31460100785cd4628c290a314628c0caa3146068b900a14628c5188194628c439a314628c5186522903630e000432230261210031130201000201301011103108003220001002315010005103101103041010020013000000031040020510000010100140011110300003101002040101100000101012200100101000114001000
  | 1 => 0x12928c07530921112108a314628c4d228cbb28c518a09460a0518a30bd28c518a314621c518a314628c2231287428c418a314628c5180c5461fa5180314628c51803946168518a314628c518a30720f9d181534628c0ada314628c518a314628c518a314628c1800b0f71c226d6811f28c368382aa5b0518a305f28c518979460e2518a314628c098a303328c37ca31311cc19a4214602e1652214628c5185814628c518a3146156d18a314628c05f4f94628c518a30131a8415260c42541a54a946230518a314628c1f1a314628c518a301a28c260a314628c518a3146053518a308028c1dca314628c15c5554628c2cc5ac62c8e518a30af51a518458e828c518a30c628c5181d94628c518a314628c1c0a314628c518a31461c4518a314628c518940f31f0030a314628c5186c94628c518a306d62c518a314628c518a314628c120530fc28c518a314628c0e6a301c28c1f88a82c28c518a314628c518a314628c5189f40528c1a43e94628c518a314628c49ca30e528c518a314628c46ca314628c518a3146137518a314628c518a30caa8c518a314628c518a314628c518a314628c518a30c24a2518a314628c2c4a100b68c230a314619a518a301228c0c6a300e28c5185c14628c518a314606d2a06b34601645024645a8c154a30ed28c518a314628c4008694623d518a314628c518a314628c2582e146204174a30ac28c518a3062a8c518a30991b093ca300328c034a30ba2023d011889a8c518a314628c518a314628c23da314628c518a314628c51854b2c0725189213628c518a314628c1f7a314628c192a314610c518a194628c2b847f4628c518a314628c060a3146094518a314628c51888851666518a314628c3288b93528c5181026f28c1a29b94628c5184994628c2b5a3146048518a3146288518a314628c5186a91a28c518a314628c1e6a314628c51889c6a68c518a300a4faa8ca314628c5182fd4628c518a314628c518a301c68c3693194628c518a3146060028a309428c5189e8054b035ca31461d2518a305b28c518a314628c168a30f2a8c518a314628c206a30cd68c371881461f43ed7ca8da8c51845d4628c518a31460d3d186d946251518a3088180066a314628c518a314606a9f02cd3428c518a3146066d18a3146010d18a314628c2940014628c06aa314628c518a314628c518a314628c518a314628c2fca314628c0d845146044518a312628c518a314628c518a314628c51865d4628c518a314628c518a30f228c518a314628c5186627628c518640e6a8c518a314628c2381014628c518a314628c3302c946172518a301f4f6518568671e7175328715f49273a846a8c232a309c28c518a3146002518a314628c518a314628c518a314628c10ca30bc28c518a303f28c518a30a228c212500e728c48da314
  | 2 => 0xa314628c518a30b204e3740794628c518a3146008518a30fb092358a314628c5182014628c1aca310428c518a314618a518a314628c518a314628c518a306a28c1b2a314628c518a314628c518a30d328c518a314628c14a9f03068c074a314628c3f9a30f628c518a314628051833c65861518a314628c378a31461869501a14628c518a314628c518a307a28c518a314628c5184e946110c48a3
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedK6 : Nat → Nat
  | 0 => 0xff42bf42fe42fd42bd42fc42fe32fd32fc32ff40fe40fd40fc40ff20fe20fd20fc20fe10fd10fc10
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedI6 : Nat → Nat
  | 0 => 0x28501a12800a07072a9b1682270d200a2a689b9246de24994283050322192e464bd829879ea1428502cb0835114245029428503081800084c0150000061c50c0
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedK7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedI7 : Nat → Nat
  | 0 => 0x8
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedCount : Nat → Nat
  | 2 => 16
  | 3 => 134
  | 4 => 470
  | 5 => 326
  | 6 => 20
  | 7 => 1
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedRecord (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s5PackedK2 (i*60) 60
  | 3 => packedAt s5PackedK3 (i*49) 49
  | 4 => packedAt s5PackedK4 (i*38) 38
  | 5 => packedAt s5PackedK5 (i*27) 27
  | 6 => packedAt s5PackedK6 (i*16) 16
  | 7 => packedAt s5PackedK7 (i*5) 5
  | _ => 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5PackedLocate (k tag : Nat) : Nat :=
  match k with
  | 2 =>
    let d := packedAt s5PackedI2 (tag % 7*4) 4
    packedAt s5PackedI2 (28+((tag/7+d)%31)*7) 7
  | 3 =>
    let d := packedAt s5PackedI3 (tag % 67*4) 4
    packedAt s5PackedI3 (268+((tag/67+d)%399)*10) 10
  | 4 =>
    let d := packedAt s5PackedI4 (tag % 226*7) 7
    packedAt s5PackedI4 (1582+((tag/226+d)%814)*11) 11
  | 5 =>
    let d := packedAt s5PackedI5 (tag % 171*4) 4
    packedAt s5PackedI5 (684+((tag/171+d)%1540)*11) 11
  | 6 =>
    let d := packedAt s5PackedI6 (tag % 15*6) 6
    packedAt s5PackedI6 (90+((tag/15+d)%60)*7) 7
  | 7 =>
    let d := packedAt s5PackedI7 (tag % 1*1) 1
    packedAt s5PackedI7 (1+((tag/1+d)%1)*3) 3
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def s5Packed : Atlas :=
  ⟨7, rawDecor 31 s5Pos s5Neg, 0xfeeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8, s5PackedCount, s5PackedRecord, (fun _ _ => 0), s5PackedLocate⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5PackedAuto (m : Fin 4) : autoOK (target s5Packed) (s5PackedMoves m) = true := by
  fin_cases m <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5PackedPairs : properPairs (target s5Packed) (asRow s5Pos) (asRow s5Neg) := by
  unfold properPairs
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_2_0 : PackedInterval s5Packed s5PackedMoves 2 0 16 :=
  packed_range (n:=16) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_level_2 : PackedInterval s5Packed s5PackedMoves 2 0 16 :=
  s5p_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_3_0 : PackedInterval s5Packed s5PackedMoves 3 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_3_32 : PackedInterval s5Packed s5PackedMoves 3 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_3_64 : PackedInterval s5Packed s5PackedMoves 3 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_3_96 : PackedInterval s5Packed s5PackedMoves 3 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_3_128 : PackedInterval s5Packed s5PackedMoves 3 128 6 :=
  packed_range (n:=6) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_level_3 : PackedInterval s5Packed s5PackedMoves 3 0 134 :=
  (packed_concat (packed_concat s5p_3_0 s5p_3_32) (packed_concat s5p_3_64 (packed_concat s5p_3_96 s5p_3_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_0 : PackedInterval s5Packed s5PackedMoves 4 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_32 : PackedInterval s5Packed s5PackedMoves 4 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_64 : PackedInterval s5Packed s5PackedMoves 4 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_96 : PackedInterval s5Packed s5PackedMoves 4 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_128 : PackedInterval s5Packed s5PackedMoves 4 128 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_160 : PackedInterval s5Packed s5PackedMoves 4 160 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_192 : PackedInterval s5Packed s5PackedMoves 4 192 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_224 : PackedInterval s5Packed s5PackedMoves 4 224 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_256 : PackedInterval s5Packed s5PackedMoves 4 256 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_288 : PackedInterval s5Packed s5PackedMoves 4 288 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_320 : PackedInterval s5Packed s5PackedMoves 4 320 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_352 : PackedInterval s5Packed s5PackedMoves 4 352 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_384 : PackedInterval s5Packed s5PackedMoves 4 384 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_416 : PackedInterval s5Packed s5PackedMoves 4 416 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_4_448 : PackedInterval s5Packed s5PackedMoves 4 448 22 :=
  packed_range (n:=22) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_level_4 : PackedInterval s5Packed s5PackedMoves 4 0 470 :=
  (packed_concat (packed_concat (packed_concat s5p_4_0 (packed_concat s5p_4_32 s5p_4_64)) (packed_concat (packed_concat s5p_4_96 s5p_4_128) (packed_concat s5p_4_160 s5p_4_192))) (packed_concat (packed_concat (packed_concat s5p_4_224 s5p_4_256) (packed_concat s5p_4_288 s5p_4_320)) (packed_concat (packed_concat s5p_4_352 s5p_4_384) (packed_concat s5p_4_416 s5p_4_448))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_0 : PackedInterval s5Packed s5PackedMoves 5 0 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_32 : PackedInterval s5Packed s5PackedMoves 5 32 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_64 : PackedInterval s5Packed s5PackedMoves 5 64 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_96 : PackedInterval s5Packed s5PackedMoves 5 96 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_128 : PackedInterval s5Packed s5PackedMoves 5 128 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_160 : PackedInterval s5Packed s5PackedMoves 5 160 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_192 : PackedInterval s5Packed s5PackedMoves 5 192 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_224 : PackedInterval s5Packed s5PackedMoves 5 224 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_256 : PackedInterval s5Packed s5PackedMoves 5 256 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_288 : PackedInterval s5Packed s5PackedMoves 5 288 32 :=
  packed_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_5_320 : PackedInterval s5Packed s5PackedMoves 5 320 6 :=
  packed_range (n:=6) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_level_5 : PackedInterval s5Packed s5PackedMoves 5 0 326 :=
  (packed_concat (packed_concat (packed_concat s5p_5_0 s5p_5_32) (packed_concat s5p_5_64 (packed_concat s5p_5_96 s5p_5_128))) (packed_concat (packed_concat s5p_5_160 (packed_concat s5p_5_192 s5p_5_224)) (packed_concat s5p_5_256 (packed_concat s5p_5_288 s5p_5_320))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_6_0 : PackedInterval s5Packed s5PackedMoves 6 0 20 :=
  packed_range (n:=20) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_level_6 : PackedInterval s5Packed s5PackedMoves 6 0 20 :=
  s5p_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_7_0 : PackedInterval s5Packed s5PackedMoves 7 0 1 :=
  packed_range (n:=1) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5p_level_7 : PackedInterval s5Packed s5PackedMoves 7 0 1 :=
  s5p_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5PackedComplete : ∀ k ≤ top s5Packed, ∀ i < count s5Packed k,
    checkPackedRow s5Packed s5PackedMoves k i = true := by
  intro k hk i hi
  have h7 : k ≤ 7 := hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hi)
  · exact False.elim (Nat.not_lt_zero _ hi)
  · exact s5p_level_2 i (by omega) hi
  · exact s5p_level_3 i (by omega) hi
  · exact s5p_level_4 i (by omega) hi
  · exact s5p_level_5 i (by omega) hi
  · exact s5p_level_6 i (by omega) hi
  · exact s5p_level_7 i (by omega) hi

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s5PackedLower : Lower true (roots s5Packed) (target s5Packed) 8 := by
  exact frozenPacked s5PackedPairs (raw_faithful 31 s5Pos s5Neg) s5PackedAuto (by rfl)
    s5PackedComplete (by decide +kernel) (by decide)
    [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def fullRoots : List Sig := [inputs.getD 3 zero, inputs.getD 4 zero, inputs.getD 6 zero, inputs.getD 2 zero, inputs.getD 5 zero, inputs.getD 1 zero, inputs.getD 7 zero, inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffffffffffffffffafffffff8fffffeeafeeefeeafffffeeafeeefee8fffffffffffffffffffffffafffffff8fffffeeafeeefeeafffffeeafeeefee8
theorem fullBound (certs0 : Complete s0Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 12 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s1PackedLower
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s4PackedLower
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s5PackedLower
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65), (inputs.getD 7 zero,4,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65), (inputs.getD 7 zero,4,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_34652.Model.Repr at out
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

def mono : List Gate := [⟨.or,[6,7]⟩, ⟨.or,[8,5]⟩, ⟨.or,[0,3]⟩, ⟨.or,[10,1]⟩, ⟨.and,[9,11]⟩, ⟨.and,[2,8]⟩, ⟨.or,[12,13]⟩, ⟨.or,[4,5]⟩, ⟨.or,[7,1]⟩, ⟨.and,[15,16]⟩, ⟨.or,[14,17]⟩, ⟨.and,[0,3]⟩, ⟨.or,[18,19]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,20,monoShape,by change 13 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_34652

open PEqualNP.Outside.L_meta_34652 in
theorem PEqualNP.Outside.L_meta_34652 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  exact solve (fullBound alls0 alls2 alls3 allgb)

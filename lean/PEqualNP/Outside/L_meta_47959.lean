import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47959.Model
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

end PEqualNP.Outside.L_meta_47959.Model
namespace PEqualNP.Outside.L_meta_47959
open PEqualNP.Outside.L_meta_47959.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

namespace B51
def R : List Sig := vars 63
def T : Sig := 0xfee8e8e8ee888880
theorem s0 : Slice true R T 0x5050505050505050 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s1 : Slice true R T 0x5500550055005500 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 83] ++ fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s2 : Slice true R T 0x5555000055550000 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 67, swapRows 84] ++ fixRows 1 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s3 : Slice true R T 0x5555555500000000 5 :=
  slice_correct (ms := [swapRows 64, swapRows 65, swapRows 66, swapRows 67] ++ fixRows 1 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s4 : Slice true R T 0x3030303030303030 5 :=
  slice_correct (ms := [swapRows 65, swapRows 82, swapRows 83, swapRows 84] ++ fixRows 2 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s5 : Slice true R T 0x3300330033003300 5 :=
  slice_correct (ms := [swapRows 65, swapRows 83] ++ fixRows 2 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s6 : Slice true R T 0x3333000033330000 5 :=
  slice_correct (ms := [swapRows 65, swapRows 67, swapRows 84] ++ fixRows 2 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s7 : Slice true R T 0x3333333300000000 5 :=
  slice_correct (ms := [swapRows 65, swapRows 66, swapRows 67] ++ fixRows 2 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s8 : Slice true R T 0xf000f000f000f000 7 :=
  slice_correct (ms := [swapRows 66, swapRows 83] ++ fixRows 0 12) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s9 : Slice true R T 0xf0f00000f0f00000 7 :=
  slice_correct (ms := [swapRows 66, swapRows 67, swapRows 84] ++ fixRows 0 20) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s10 : Slice true R T 0xf0f0f0f00000000 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67] ++ fixRows 4 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s11 : Slice true R T 0xf0f0f0f0 5 :=
  slice_correct (ms := [swapRows 66, swapRows 67] ++ fixRows 32 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s12 : Slice true R T 0xff000000ff0000 5 :=
  slice_correct (ms := [swapRows 67, swapRows 84] ++ fixRows 8 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s13 : Slice true R T 0xff000000ff00 5 :=
  slice_correct (ms := [swapRows 67, swapRows 84] ++ fixRows 16 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
theorem s14 : Slice true R T 0xff00ff0000000000 7 :=
  slice_correct (ms := [swapRows 67] ++ fixRows 0 40) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s15 : Slice true R T 0xffff000000000000 7 :=
  slice_correct (ms := fixRows 0 48) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
theorem s28 : Slice true R T 0x5000500050005000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66, swapRows 83, swapRows 84] ++ fixRows 1 12) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s31 : Slice true R T 0x5050000050500000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66, swapRows 84] ++ fixRows 1 20) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s35 : Slice true R T 0xa0a0a0a 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 66] ++ fixRows 36 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s39 : Slice true R T 0xaa000000aa 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 24 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s42 : Slice true R T 0x5500550000000000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50, swapRows 67] ++ fixRows 1 40) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s45 : Slice true R T 0x5555000000000000 4 :=
  slice_correct (ms := [swapRows 48, swapRows 49, swapRows 50] ++ fixRows 1 48) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s48 : Slice true R T 0x3000300030003000 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66, swapRows 83, swapRows 84] ++ fixRows 2 12) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s51 : Slice true R T 0x3030000030300000 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66, swapRows 84] ++ fixRows 2 20) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s55 : Slice true R T 0xc0c0c0c 4 :=
  slice_correct (ms := [swapRows 49, swapRows 66] ++ fixRows 36 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s59 : Slice true R T 0xcc000000cc 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67, swapRows 84] ++ fixRows 24 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s62 : Slice true R T 0x3300330000000000 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50, swapRows 67] ++ fixRows 2 40) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s65 : Slice true R T 0x3333000000000000 4 :=
  slice_correct (ms := [swapRows 49, swapRows 50] ++ fixRows 2 48) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s68 : Slice true R T 0xf0000000f0 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67, swapRows 84] ++ fixRows 24 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s72 : Slice true R T 0xf000f00 4 :=
  slice_correct (ms := [swapRows 50, swapRows 67] ++ fixRows 36 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s76 : Slice true R T 0xf0f0000 4 :=
  slice_correct (ms := [swapRows 50] ++ fixRows 36 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
theorem s80 : Slice true R T 0xff00000000 4 :=
  slice_correct (ms := fixRows 24 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def Pos : Nat → Bits
  | 0 => ((0xafe69d27b655abdb : BitVec 64) ++ (0xafe69d27b655abdb : BitVec 64))
  | 1 => ((0xd63bd3bb5dcadd4f : BitVec 64) ++ (0xd63bd3bb5dcadd4f : BitVec 64))
  | 2 => ((0xd185f7cac3bb63be : BitVec 64) ++ (0xd185f7cac3bb63be : BitVec 64))
  | 3 => ((0xed7d2b547e2e34fc : BitVec 64) ++ (0xed7d2b547e2e34fc : BitVec 64))
  | 4 => ((0x69d978f5a8ad9db5 : BitVec 64) ++ (0x69d978f5a8ad9db5 : BitVec 64))
  | 5 => ((0x9af66ed9c7f36621 : BitVec 64) ++ (0x9af66ed9c7f36621 : BitVec 64))
  | _ => 0
def Neg : Nat → Bits
  | 0 => ((0x2fa68c249214818b : BitVec 64) ++ (0x2fa68c249214818b : BitVec 64))
  | 1 => ((0x8611d31b0cc2d844 : BitVec 64) ++ (0x8611d31b0cc2d844 : BitVec 64))
  | 2 => ((0xb18557ca412923be : BitVec 64) ++ (0xb18557ca412923be : BitVec 64))
  | 3 => ((0xe87c23447e0a24fc : BitVec 64) ++ (0xe87c23447e0a24fc : BitVec 64))
  | 4 => ((0x51c978b1a0ad1d31 : BitVec 64) ++ (0x51c978b1a0ad1d31 : BitVec 64))
  | 5 => ((0x187228d1c7f36601 : BitVec 64) ++ (0x187228d1c7f36601 : BitVec 64))
  | _ => 0
theorem correctPairs : properPairs T (asRow Pos) (asRow Neg) := by unfold properPairs; decide +kernel
def auto1 : List Move := [swapRows 67]
theorem auto1ok : autoOK T auto1 = true := by decide +kernel
def auto2 : List Move := [swapRows 50, swapRows 84]
theorem auto2ok : autoOK T auto2 = true := by decide +kernel
def auto3 : List Move := [swapRows 50, swapRows 83, swapRows 84]
theorem auto3ok : autoOK T auto3 = true := by decide +kernel
def auto4 : List Move := [swapRows 66, swapRows 67, swapRows 84]
theorem auto4ok : autoOK T auto4 = true := by decide +kernel
def auto5 : List Move := [swapRows 66, swapRows 83]
theorem auto5ok : autoOK T auto5 = true := by decide +kernel
def auto6 : List Move := [swapRows 82]
theorem auto6ok : autoOK T auto6 = true := by decide +kernel
def auto7 : List Move := [swapRows 82, swapRows 67]
theorem auto7ok : autoOK T auto7 = true := by decide +kernel
def auto8 : List Move := [swapRows 16]
theorem auto8ok : autoOK T auto8 = true := by decide +kernel
def auto9 : List Move := [swapRows 16, swapRows 67]
theorem auto9ok : autoOK T auto9 = true := by decide +kernel
def auto10 : List Move := [swapRows 16, swapRows 50, swapRows 84]
theorem auto10ok : autoOK T auto10 = true := by decide +kernel
def auto11 : List Move := [swapRows 16, swapRows 50, swapRows 83, swapRows 84]
theorem auto11ok : autoOK T auto11 = true := by decide +kernel
def auto12 : List Move := [swapRows 16, swapRows 66, swapRows 67, swapRows 84]
theorem auto12ok : autoOK T auto12 = true := by decide +kernel
def auto13 : List Move := [swapRows 16, swapRows 66, swapRows 83]
theorem auto13ok : autoOK T auto13 = true := by decide +kernel
def auto14 : List Move := [swapRows 16, swapRows 82]
theorem auto14ok : autoOK T auto14 = true := by decide +kernel
def auto15 : List Move := [swapRows 16, swapRows 82, swapRows 67]
theorem auto15ok : autoOK T auto15 = true := by decide +kernel
def w0 := inputObserved 63 Pos Neg 0
def w1 := inputObserved 63 Pos Neg 1
def w2 := inputObserved 63 Pos Neg 2
def w3 := inputObserved 63 Pos Neg 3
def w4 := inputObserved 63 Pos Neg 4
def w5 := inputObserved 63 Pos Neg 5
def w6 := combineObserved 0 w0 w1
def w7 := combineObserved 3 w6 w0
def w8 := combineObserved 3 w0 w1
def w9 := combineObserved 1 w7 w8
def w10 := combineObserved 1 w0 w1
def w11 := combineObserved 0 w7 w2
def w12 := combineObserved 3 w8 w2
def w13 := combineObserved 0 w6 w5
def w14 := combineObserved 3 w13 w0
def w15 := combineObserved 3 w13 w1
def w16 := combineObserved 1 w13 w2
def w17 := combineObserved 3 w13 w5
def w18 := combineObserved 0 w6 w2
def w19 := combineObserved 3 w18 w2
def w20 := combineObserved 1 w18 w4
def w21 := combineObserved 1 w18 w5
def w22 := combineObserved 0 w18 w4
def w23 := combineObserved 3 w22 w2
def w24 := combineObserved 0 w6 w4
def w25 := combineObserved 0 w24 w5
def w26 := combineObserved 3 w25 w2
def w27 := combineObserved 0 w18 w3
def w28 := combineObserved 1 w18 w3
def w29 := combineObserved 1 w24 w5
def w30 := combineObserved 3 w13 w2
def w31 := combineObserved 1 w13 w4
def w32 := combineObserved 1 w24 w3
def w33 := combineObserved 0 w6 w3
def w34 := combineObserved 0 w33 w5
def w35 := combineObserved 3 w34 w3
def w36 := combineObserved 3 w24 w5
def w37 := combineObserved 0 w33 w4
def w38 := combineObserved 3 w37 w0
def w39 := combineObserved 3 w37 w2
def w40 := combineObserved 0 w18 w5
def w41 := combineObserved 0 w3 w4
def w42 := combineObserved 0 w2 w5
def w43 := combineObserved 3 w5 w2
def w44 := combineObserved 1 w43 w13
def w45 := combineObserved 1 w33 w42
def w46 := combineObserved 1 w33 w5
def w47 := combineObserved 1 w6 w4
def w48 := combineObserved 0 w32 w47
def w49 := combineObserved 1 w6 w5
def w50 := combineObserved 3 w13 w49
def w51 := combineObserved 3 w13 w10
def w52 := combineObserved 1 w6 w2
def w53 := combineObserved 0 w52 w5
def w54 := combineObserved 1 w9 w18
def w55 := combineObserved 0 w2 w49
def w56 := combineObserved 0 w52 w49
def w57 := combineObserved 3 w9 w2
def w58 := combineObserved 3 w9 w52
def w59 := combineObserved 2 w52 w5
def w60 := combineObserved 0 w10 w2
def w61 := combineObserved 0 w10 w52
def w62 := combineObserved 2 w6 w2
def w63 := combineObserved 3 w62 w0
def w64 := combineObserved 2 w6 w5
def w65 := combineObserved 3 w17 w0
def w66 := combineObserved 3 w24 w4
def w67 := combineObserved 0 w66 w5
def w68 := combineObserved 1 w4 w5
def w69 := combineObserved 3 w67 w68
def w70 := combineObserved 0 w19 w3
def w71 := combineObserved 1 w2 w3
def w72 := combineObserved 3 w17 w4
def w73 := combineObserved 3 w72 w2
def w74 := combineObserved 3 w5 w3
def w75 := combineObserved 3 w6 w3
def w76 := combineObserved 3 w75 w5
def w77 := combineObserved 3 w66 w2
def w78 := combineObserved 0 w75 w4
def w79 := combineObserved 1 w3 w4
def w80 := combineObserved 3 w78 w79
def w81 := combineObserved 0 w19 w5
def w82 := combineObserved 1 w2 w5
def w83 := combineObserved 3 w19 w5
def w84 := combineObserved 3 w17 w2
def w85 := combineObserved 0 w0 w2
def w86 := combineObserved 2 w0 w5
def w87 := combineObserved 2 w2 w3
def w88 := combineObserved 1 w87 w4
def w89 := combineObserved 0 w9 w2
def w90 := combineObserved 1 w9 w2
def w91 := combineObserved 3 w89 w90
def w92 := combineObserved 0 w9 w3
def w93 := combineObserved 3 w9 w3
def w94 := combineObserved 1 w92 w42
def w95 := combineObserved 1 w9 w5
def w96 := combineObserved 2 w9 w5
def w97 := combineObserved 2 w9 w41
def w98 := combineObserved 1 w9 w4
def w99 := combineObserved 2 w9 w2
def w100 := combineObserved 1 w99 w5
def w101 := combineObserved 3 w96 w2
def w102 := combineObserved 3 w9 w5
def w103 := combineObserved 1 w93 w42
def w104 := combineObserved 0 w2 w3
def w105 := combineObserved 0 w9 w71
def w106 := combineObserved 3 w9 w71
def w107 := combineObserved 1 w74 w9
def w108 := combineObserved 3 w2 w4
def w109 := combineObserved 3 w108 w9
def w110 := combineObserved 3 w2 w3
def w111 := combineObserved 1 w110 w5
def w112 := combineObserved 3 w5 w4
def w113 := combineObserved 3 w112 w2
def w114 := combineObserved 3 w3 w5
def w115 := combineObserved 1 w9 w42
def w116 := combineObserved 3 w41 w79
def w117 := combineObserved 1 w42 w41
def w118 := combineObserved 1 w43 w9
def w119 := combineObserved 3 w2 w5
def w120 := combineObserved 3 w119 w9
def w121 := combineObserved 1 w10 w3
def w122 := combineObserved 0 w121 w2
def w123 := combineObserved 2 w121 w5
def w124 := combineObserved 1 w10 w5
def w125 := combineObserved 0 w124 w2
def w126 := combineObserved 1 w10 w2
def w127 := combineObserved 2 w126 w5
def w128 := combineObserved 2 w10 w5
def w129 := combineObserved 3 w10 w2
def w130 := combineObserved 0 w10 w71
def w131 := combineObserved 3 w6 w126
def w132 := combineObserved 0 w126 w3
def w133 := combineObserved 0 w10 w3
def w134 := combineObserved 3 w10 w5
def w135 := combineObserved 1 w128 w134
def w136 := combineObserved 1 w134 w6
def w137 := combineObserved 0 w4 w5
def w138 := combineObserved 3 w137 w68
def w139 := combineObserved 3 w10 w71
def w140 := combineObserved 1 w139 w6
def w141 := combineObserved 1 w6 w3
def w142 := combineObserved 0 w141 w47
def w143 := combineObserved 0 w142 w2
def w144 := combineObserved 3 w142 w2
def w145 := combineObserved 1 w42 w142
def w146 := combineObserved 0 w10 w145
def w147 := combineObserved 3 w41 w56
def w148 := combineObserved 2 w6 w42
def w149 := combineObserved 3 w148 w10
def w150 := combineObserved 2 w6 w41
def w151 := combineObserved 0 w10 w117
def w152 := combineObserved 1 w0 w5
def w153 := combineObserved 0 w152 w2
def w154 := combineObserved 1 w0 w2
def w155 := combineObserved 2 w154 w5
def w156 := combineObserved 3 w1 w2
def w157 := combineObserved 1 w85 w1
def w158 := combineObserved 0 w1 w2
def w159 := combineObserved 1 w158 w0
def w160 := combineObserved 0 w1 w5
def w161 := combineObserved 1 w1 w5
def w162 := combineObserved 3 w160 w161
def w163 := combineObserved 3 w6 w154
def w164 := combineObserved 1 w6 w153
def w165 := combineObserved 1 w86 w1
def w166 := combineObserved 3 w0 w5
def w167 := combineObserved 1 w156 w6
def w168 := combineObserved 0 w156 w5
def w169 := combineObserved 1 w168 w6
def w170 := combineObserved 0 w104 w4
def w171 := combineObserved 1 w6 w170
def w172 := combineObserved 0 w6 w68
def w173 := combineObserved 3 w172 w2
def w174 := combineObserved 0 w6 w71
def w175 := combineObserved 3 w6 w71
def w176 := combineObserved 0 w1 w71
def w177 := combineObserved 1 w176 w0
def w178 := combineObserved 0 w0 w71
def w179 := combineObserved 3 w1 w71
def w180 := combineObserved 1 w74 w6
def w181 := combineObserved 3 w108 w6
def w182 := combineObserved 3 w41 w2
def w183 := combineObserved 1 w0 w42
def w184 := combineObserved 0 w6 w79
def w185 := combineObserved 3 w6 w117
def w186 := combineObserved 3 w184 w2
def w187 := combineObserved 3 w6 w79
def w188 := combineObserved 1 w43 w6
def w189 := combineObserved 3 w119 w6
def w190 := combineObserved 3 w160 w10
def w191 := combineObserved 1 w1 w2
def w192 := combineObserved 0 w0 w191
def w193 := combineObserved 3 w1 w154
def w194 := combineObserved 0 w154 w5
def w195 := combineObserved 2 w1 w2
def w196 := combineObserved 3 w195 w10
def w197 := combineObserved 3 w0 w2
def w198 := combineObserved 1 w197 w1
def w199 := combineObserved 0 w60 w3
def w200 := combineObserved 0 w10 w4
def w201 := combineObserved 3 w200 w2
def w202 := combineObserved 0 w60 w5
def w203 := combineObserved 1 w1 w202
def w204 := combineObserved 0 w133 w4
def w205 := combineObserved 3 w204 w2
def w206 := combineObserved 0 w10 w5
def w207 := combineObserved 3 w206 w2
def w208 := combineObserved 3 w108 w5
def w209 := combineObserved 1 w1 w42
def w210 := combineObserved 1 w133 w42
def w211 := combineObserved 0 w126 w5
def w212 := combineObserved 1 w156 w0
def w213 := combineObserved 0 w129 w3
def w214 := combineObserved 3 w10 w4
def w215 := combineObserved 3 w214 w2
def w216 := combineObserved 0 w129 w5
def w217 := combineObserved 3 w134 w2
def w218 := combineObserved 1 w74 w10
def w219 := combineObserved 3 w108 w10
def w220 := combineObserved 0 w0 w209
def w221 := combineObserved 2 w0 w41
def w222 := combineObserved 2 w1 w42
def w223 := combineObserved 2 w10 w42
def w224 := combineObserved 1 w10 w41
def w225 := combineObserved 0 w224 w2
def w226 := combineObserved 1 w10 w42
def w227 := combineObserved 2 w10 w41
def w228 := combineObserved 2 w227 w42
def w229 := combineObserved 0 w10 w79
def w230 := combineObserved 3 w10 w79
def w231 := combineObserved 1 w43 w10
def w232 := combineObserved 3 w119 w10
def w233 := combineObserved 0 w0 w5
def w234 := combineObserved 1 w233 w1
def w235 := combineObserved 3 w7 w5
def w236 := combineObserved 3 w19 w0
def w237 := combineObserved 3 w7 w2
def w238 := combineObserved 0 w11 w3
def w239 := combineObserved 0 w8 w4
def w240 := combineObserved 3 w239 w2
def w241 := combineObserved 0 w8 w3
def w242 := combineObserved 0 w241 w4
def w243 := combineObserved 3 w242 w2
def w244 := combineObserved 0 w11 w5
def w245 := combineObserved 0 w8 w5
def w246 := combineObserved 3 w245 w2
def w247 := combineObserved 0 w19 w1
def w248 := combineObserved 1 w8 w2
def w249 := combineObserved 3 w247 w248
def w250 := combineObserved 1 w247 w7
def w251 := combineObserved 1 w7 w2
def w252 := combineObserved 1 w11 w8
def w253 := combineObserved 2 w7 w2
def w254 := combineObserved 1 w253 w5
def w255 := combineObserved 2 w8 w2
def w256 := combineObserved 3 w255 w5
def w257 := combineObserved 2 w8 w5
def w258 := combineObserved 3 w257 w2
def w259 := combineObserved 2 w7 w5
def w260 := combineObserved 3 w259 w2
def w261 := combineObserved 1 w257 w7
def w262 := combineObserved 3 w8 w5
def w263 := combineObserved 1 w259 w8
def w264 := combineObserved 3 w8 w3
def w265 := combineObserved 0 w12 w3
def w266 := combineObserved 3 w7 w4
def w267 := combineObserved 3 w266 w2
def w268 := combineObserved 0 w12 w5
def w269 := combineObserved 3 w235 w2
def w270 := combineObserved 3 w7 w3
def w271 := combineObserved 1 w86 w166
def w272 := combineObserved 0 w1 w154
def w273 := combineObserved 3 w62 w1
def w274 := combineObserved 0 w1 w3
def w275 := combineObserved 3 w0 w126
def w276 := combineObserved 0 w161 w2
def w277 := combineObserved 0 w7 w71
def w278 := combineObserved 3 w8 w71
def w279 := combineObserved 1 w179 w0
def w280 := combineObserved 1 w74 w7
def w281 := combineObserved 3 w108 w7
def w282 := combineObserved 1 w7 w41
def w283 := combineObserved 1 w42 w282
def w284 := combineObserved 1 w7 w42
def w285 := combineObserved 2 w7 w41
def w286 := combineObserved 2 w0 w42
def w287 := combineObserved 3 w286 w1
def w288 := combineObserved 3 w8 w79
def w289 := combineObserved 3 w8 w117
def w290 := combineObserved 0 w7 w79
def w291 := combineObserved 1 w43 w7
def w292 := combineObserved 3 w119 w7
def w293 := combineObserved 0 w0 w4
def w294 := combineObserved 1 w0 w4
def w295 := combineObserved 1 w160 w0
def w296 := combineObserved 3 w13 w295
def w297 := combineObserved 3 w13 w152
def w298 := combineObserved 0 w234 w2
def w299 := combineObserved 0 w159 w161
def w300 := combineObserved 1 w274 w0
def w301 := combineObserved 0 w300 w2
def w302 := combineObserved 1 w293 w1
def w303 := combineObserved 3 w302 w2
def w304 := combineObserved 0 w295 w2
def w305 := combineObserved 3 w234 w2
def w306 := combineObserved 0 w157 w3
def w307 := combineObserved 1 w158 w41
def w308 := combineObserved 2 w159 w41
def w309 := combineObserved 3 w245 w161
def w310 := combineObserved 3 w18 w1
def w311 := combineObserved 3 w11 w154
def w312 := combineObserved 3 w85 w154
def w313 := combineObserved 0 w14 w2
def w314 := combineObserved 3 w15 w2
def w315 := combineObserved 3 w24 w0
def w316 := combineObserved 0 w315 w2
def w317 := combineObserved 3 w33 w1
def w318 := combineObserved 3 w317 w2
def w319 := combineObserved 2 w0 w2
def w320 := combineObserved 3 w319 w5
def w321 := combineObserved 3 w18 w0
def w322 := combineObserved 3 w321 w5
def w323 := combineObserved 3 w1 w3
def w324 := combineObserved 1 w315 w42
def w325 := combineObserved 1 w0 w41
def w326 := combineObserved 0 w1 w4
def w327 := combineObserved 3 w160 w3
def w328 := combineObserved 0 w327 w4
def w329 := combineObserved 1 w160 w41
def w330 := combineObserved 3 w197 w5
def w331 := combineObserved 3 w166 w2
def w332 := combineObserved 0 w158 w3
def w333 := combineObserved 1 w332 w0
def w334 := combineObserved 0 w326 w5
def w335 := combineObserved 3 w334 w0
def w336 := combineObserved 0 w158 w4
def w337 := combineObserved 3 w336 w2
def w338 := combineObserved 3 w336 w4
def w339 := combineObserved 0 w85 w3
def w340 := combineObserved 0 w339 w4
def w341 := combineObserved 1 w340 w1
def w342 := combineObserved 0 w160 w3
def w343 := combineObserved 0 w342 w4
def w344 := combineObserved 3 w343 w0
def w345 := combineObserved 0 w332 w4
def w346 := combineObserved 3 w345 w2
def w347 := combineObserved 3 w343 w2
def w348 := combineObserved 3 w334 w2
def w349 := combineObserved 1 w337 w0
def w350 := combineObserved 3 w339 w2
def w351 := combineObserved 3 w350 w1
def w352 := combineObserved 3 w338 w0
def w353 := combineObserved 0 w327 w2
def w354 := combineObserved 3 w342 w5
def w355 := combineObserved 3 w354 w4
def w356 := combineObserved 3 w355 w2
def w357 := combineObserved 3 w339 w3
def w358 := combineObserved 3 w357 w5
def w359 := combineObserved 0 w293 w5
def w360 := combineObserved 3 w359 w4
def w361 := combineObserved 3 w360 w2
def w362 := combineObserved 0 w337 w5
def w363 := combineObserved 0 w233 w3
def w364 := combineObserved 3 w363 w5
def w365 := combineObserved 3 w364 w2
def w366 := combineObserved 0 w85 w4
def w367 := combineObserved 3 w366 w2
def w368 := combineObserved 3 w87 w4
def w369 := combineObserved 3 w332 w3
def w370 := combineObserved 0 w0 w3
def w371 := combineObserved 0 w370 w4
def w372 := combineObserved 1 w371 w1
def w373 := combineObserved 3 w371 w3
def w374 := combineObserved 0 w158 w5
def w375 := combineObserved 3 w374 w2
def w376 := combineObserved 1 w0 w202
def w377 := combineObserved 0 w85 w5
def w378 := combineObserved 1 w377 w4
def w379 := combineObserved 1 w0 w204
def w380 := combineObserved 0 w274 w4
def w381 := combineObserved 1 w380 w5
def w382 := combineObserved 3 w374 w5
def w383 := combineObserved 1 w377 w3
def w384 := combineObserved 3 w380 w5
def w385 := combineObserved 1 w371 w158
def w386 := combineObserved 1 w380 w85
def w387 := combineObserved 1 w371 w374
def w388 := combineObserved 1 w380 w42
def w389 := combineObserved 1 w371 w42
def w390 := combineObserved 1 w160 w2
def w391 := combineObserved 1 w85 w5
def w392 := combineObserved 1 w1 w3
def w393 := combineObserved 1 w326 w3
def w394 := combineObserved 3 w380 w393
def w395 := combineObserved 1 w1 w4
def w396 := combineObserved 1 w233 w2
def w397 := combineObserved 3 w380 w392
def w398 := combineObserved 1 w274 w4
def w399 := combineObserved 2 w85 w5
def w400 := combineObserved 3 w399 w0
def w401 := combineObserved 3 w86 w2
def w402 := combineObserved 3 w377 w5
def w403 := combineObserved 3 w399 w154
def w404 := combineObserved 1 w375 w0
def w405 := combineObserved 3 w377 w2
def w406 := combineObserved 3 w405 w1
def w407 := combineObserved 3 w382 w0
def w408 := combineObserved 3 w402 w3
def w409 := combineObserved 0 w162 w0
def w410 := combineObserved 1 w162 w0
def w411 := combineObserved 2 w271 w1
def w412 := combineObserved 3 w271 w1
def w413 := combineObserved 3 w162 w0
def w414 := combineObserved 1 w413 w2
def w415 := combineObserved 3 w413 w2
def w416 := combineObserved 0 w162 w2
def w417 := combineObserved 1 w162 w2
def w418 := combineObserved 3 w158 w191
def w419 := combineObserved 2 w418 w5
def w420 := combineObserved 3 w162 w2
def w421 := combineObserved 0 w162 w154
def w422 := combineObserved 1 w233 w158
def w423 := combineObserved 3 w160 w191
def w424 := combineObserved 0 w1 w152
def w425 := combineObserved 3 w1 w5
def w426 := combineObserved 1 w425 w158
def w427 := combineObserved 1 w370 w158
def w428 := combineObserved 1 w85 w274
def w429 := combineObserved 1 w323 w85
def w430 := combineObserved 3 w166 w326
def w431 := combineObserved 3 w430 w2
def w432 := combineObserved 3 w1 w4
def w433 := combineObserved 3 w432 w85
def w434 := combineObserved 3 w432 w3
def w435 := combineObserved 1 w0 w3
def w436 := combineObserved 0 w326 w435
def w437 := combineObserved 3 w436 w2
def w438 := combineObserved 0 w85 w161
def w439 := combineObserved 3 w160 w154
def w440 := combineObserved 1 w0 w276
def w441 := combineObserved 2 w1 w5
def w442 := combineObserved 1 w441 w85
def w443 := combineObserved 3 w441 w85
def w444 := combineObserved 3 w441 w2
def w445 := combineObserved 1 w0 w444
def w446 := combineObserved 1 w425 w85
def w447 := combineObserved 3 w425 w85
def w448 := combineObserved 3 w160 w209
def w449 := combineObserved 3 w85 w183
def w450 := combineObserved 0 w1 w183
def w451 := combineObserved 1 w233 w41
def w452 := combineObserved 1 w370 w42
def w453 := combineObserved 1 w43 w0
def w454 := combineObserved 1 w119 w85
def w455 := combineObserved 1 w119 w0
def w456 := combineObserved 0 w1 w451
def w457 := combineObserved 1 w1 w451
def w458 := combineObserved 3 w456 w457
def w459 := combineObserved 1 w274 w42
def w460 := combineObserved 0 w0 w459
def w461 := combineObserved 1 w0 w459
def w462 := combineObserved 1 w1 w452
def w463 := combineObserved 2 w0 w329
def w464 := combineObserved 3 w0 w329
def w465 := combineObserved 3 w1 w452
def w466 := combineObserved 1 w85 w41
def w467 := combineObserved 2 w85 w41
def w468 := combineObserved 2 w1 w41
def w469 := combineObserved 3 w326 w183
def w470 := combineObserved 1 w1 w41
def w471 := combineObserved 1 w468 w85
def w472 := combineObserved 0 w3 w5
def w473 := combineObserved 1 w74 w85
def w474 := combineObserved 3 w114 w326
def w475 := combineObserved 3 w474 w2
def w476 := combineObserved 3 w112 w85
def w477 := combineObserved 1 w0 w113
def w478 := combineObserved 1 w425 w0
def w479 := combineObserved 0 w478 w191
def w480 := combineObserved 3 w259 w0
def w481 := combineObserved 3 w424 w2
def w482 := combineObserved 3 w1 w152
def w483 := combineObserved 0 w482 w2
def w484 := combineObserved 3 w0 w161
def w485 := combineObserved 3 w484 w2
def w486 := combineObserved 0 w191 w5
def w487 := combineObserved 0 w154 w161
def w488 := combineObserved 3 w195 w152
def w489 := combineObserved 3 w166 w191
def w490 := combineObserved 0 w392 w4
def w491 := combineObserved 2 w0 w490
def w492 := combineObserved 3 w0 w4
def w493 := combineObserved 0 w435 w4
def w494 := combineObserved 1 w1 w493
def w495 := combineObserved 3 w436 w494
def w496 := combineObserved 1 w1 w153
def w497 := combineObserved 3 w0 w490
def w498 := combineObserved 1 w441 w0
def w499 := combineObserved 0 w498 w2
def w500 := combineObserved 3 w165 w2
def w501 := combineObserved 3 w64 w1
def w502 := combineObserved 3 w501 w2
def w503 := combineObserved 2 w1 w3
def w504 := combineObserved 3 w503 w4
def w505 := combineObserved 2 w0 w504
def w506 := combineObserved 3 w195 w5
def w507 := combineObserved 3 w0 w42
def w508 := combineObserved 2 w0 w3
def w509 := combineObserved 2 w1 w4
def w510 := combineObserved 1 w508 w509
def w511 := combineObserved 1 w86 w156
def w512 := combineObserved 1 w86 w42
def w513 := combineObserved 1 w166 w1
def w514 := combineObserved 3 w245 w513
def w515 := combineObserved 0 w7 w5
def w516 := combineObserved 3 w515 w478
def w517 := combineObserved 1 w323 w0
def w518 := combineObserved 0 w517 w2
def w519 := combineObserved 1 w492 w1
def w520 := combineObserved 3 w519 w2
def w521 := combineObserved 0 w478 w2
def w522 := combineObserved 3 w513 w2
def w523 := combineObserved 0 w498 w1
def w524 := combineObserved 3 w523 w2
def w525 := combineObserved 3 w75 w1
def w526 := combineObserved 3 w525 w2
def w527 := combineObserved 3 w19 w1
def w528 := combineObserved 0 w156 w3
def w529 := combineObserved 1 w528 w0
def w530 := combineObserved 0 w432 w5
def w531 := combineObserved 3 w530 w0
def w532 := combineObserved 0 w197 w4
def w533 := combineObserved 3 w532 w2
def w534 := combineObserved 3 w532 w4
def w535 := combineObserved 3 w528 w2
def w536 := combineObserved 0 w528 w4
def w537 := combineObserved 0 w492 w5
def w538 := combineObserved 3 w537 w2
def w539 := combineObserved 0 w156 w4
def w540 := combineObserved 3 w539 w2
def w541 := combineObserved 1 w540 w0
def w542 := combineObserved 3 w156 w4
def w543 := combineObserved 3 w542 w0
def w544 := combineObserved 3 w0 w3
def w545 := combineObserved 0 w544 w5
def w546 := combineObserved 3 w545 w3
def w547 := combineObserved 0 w546 w2
def w548 := combineObserved 3 w530 w4
def w549 := combineObserved 3 w548 w2
def w550 := combineObserved 0 w323 w5
def w551 := combineObserved 3 w550 w3
def w552 := combineObserved 0 w551 w4
def w553 := combineObserved 3 w552 w2
def w554 := combineObserved 0 w533 w5
def w555 := combineObserved 3 w550 w5
def w556 := combineObserved 3 w555 w2
def w557 := combineObserved 0 w544 w2
def w558 := combineObserved 3 w557 w3
def w559 := combineObserved 3 w528 w3
def w560 := combineObserved 1 w168 w0
def w561 := combineObserved 0 w323 w4
def w562 := combineObserved 3 w561 w0
def w563 := combineObserved 3 w168 w2
def w564 := combineObserved 0 w544 w4
def w565 := combineObserved 3 w564 w2
def w566 := combineObserved 1 w166 w2
def w567 := combineObserved 3 w507 w566
def w568 := combineObserved 1 w156 w5
def w569 := combineObserved 2 w156 w5
def w570 := combineObserved 1 w569 w1
def w571 := combineObserved 3 w156 w5
def w572 := combineObserved 1 w563 w0
def w573 := combineObserved 3 w571 w0
def w574 := combineObserved 3 w571 w3
def w575 := combineObserved 1 w323 w197
def w576 := combineObserved 1 w425 w197
def w577 := combineObserved 3 w43 w1
def w578 := combineObserved 1 w323 w42
def w579 := combineObserved 2 w156 w41
def w580 := combineObserved 3 w182 w1
def w581 := combineObserved 1 w74 w156
def w582 := combineObserved 3 w112 w156
def w583 := combineObserved 2 w0 w368
def w584 := combineObserved 1 w0 w170
def w585 := combineObserved 0 w472 w4
def w586 := combineObserved 2 w0 w585
def w587 := combineObserved 0 w170 w5
def w588 := combineObserved 1 w1 w587
def w589 := combineObserved 2 w0 w587
def w590 := combineObserved 3 w585 w2
def w591 := combineObserved 1 w178 w1
def w592 := combineObserved 0 w1 w68
def w593 := combineObserved 3 w592 w0
def w594 := combineObserved 3 w1 w68
def w595 := combineObserved 3 w594 w0
def w596 := combineObserved 1 w74 w1
def w597 := combineObserved 0 w596 w0
def w598 := combineObserved 1 w74 w0
def w599 := combineObserved 2 w598 w1
def w600 := combineObserved 0 w598 w2
def w601 := combineObserved 3 w108 w1
def w602 := combineObserved 1 w601 w0
def w603 := combineObserved 3 w74 w1
def w604 := combineObserved 3 w603 w0
def w605 := combineObserved 3 w603 w2
def w606 := combineObserved 3 w108 w0
def w607 := combineObserved 3 w114 w4
def w608 := combineObserved 2 w2 w4
def w609 := combineObserved 3 w608 w3
def w610 := combineObserved 3 w87 w326
def w611 := combineObserved 1 w1 w368
def w612 := combineObserved 3 w610 w611
def w613 := combineObserved 3 w0 w368
def w614 := combineObserved 3 w380 w470
def w615 := combineObserved 3 w380 w79
def w616 := combineObserved 3 w1 w183
def w617 := combineObserved 0 w325 w2
def w618 := combineObserved 0 w2 w470
def w619 := combineObserved 0 w0 w79
def w620 := combineObserved 3 w42 w82
def w621 := combineObserved 3 w620 w0
def w622 := combineObserved 0 w183 w82
def w623 := combineObserved 2 w183 w41
def w624 := combineObserved 1 w468 w0
def w625 := combineObserved 3 w222 w0
def w626 := combineObserved 3 w468 w2
def w627 := combineObserved 1 w221 w42
def w628 := combineObserved 3 w564 w79
def w629 := combineObserved 0 w182 w5
def w630 := combineObserved 0 w221 w79
def w631 := combineObserved 1 w182 w0
def w632 := combineObserved 3 w42 w4
def w633 := combineObserved 3 w632 w0
def w634 := combineObserved 3 w41 w5
def w635 := combineObserved 3 w634 w2
def w636 := combineObserved 3 w42 w3
def w637 := combineObserved 0 w1 w82
def w638 := combineObserved 3 w637 w0
def w639 := combineObserved 0 w286 w82
def w640 := combineObserved 1 w620 w0
def w641 := combineObserved 3 w639 w640
def w642 := combineObserved 1 w116 w0
def w643 := combineObserved 2 w116 w1
def w644 := combineObserved 3 w116 w1
def w645 := combineObserved 3 w116 w0
def w646 := combineObserved 0 w1 w117
def w647 := combineObserved 1 w646 w0
def w648 := combineObserved 1 w1 w117
def w649 := combineObserved 0 w0 w117
def w650 := combineObserved 1 w649 w1
def w651 := combineObserved 3 w646 w0
def w652 := combineObserved 3 w646 w648
def w653 := combineObserved 1 w0 w117
def w654 := combineObserved 0 w1 w653
def w655 := combineObserved 0 w0 w648
def w656 := combineObserved 3 w1 w653
def w657 := combineObserved 2 w0 w117
def w658 := combineObserved 3 w0 w117
def w659 := combineObserved 3 w1 w117
def w660 := combineObserved 0 w1 w79
def w661 := combineObserved 1 w660 w0
def w662 := combineObserved 3 w1 w79
def w663 := combineObserved 1 w662 w0
def w664 := combineObserved 3 w1 w82
def w665 := combineObserved 3 w664 w0
def w666 := combineObserved 0 w570 w0
def w667 := combineObserved 2 w453 w1
def w668 := combineObserved 2 w160 w2
def w669 := combineObserved 3 w668 w1
def w670 := combineObserved 1 w669 w0
def w671 := combineObserved 3 w577 w0
def w672 := combineObserved 2 w233 w2
def w673 := combineObserved 3 w672 w0
def x0 : Sig := 0xff00ff00ff00ff00
def x1 : Sig := 0xffff0000ffff0000
def x2 : Sig := 0xf0f0f0f0f0f0f0f0
def x3 : Sig := 0xffffffff00000000
def x4 : Sig := 0xaaaaaaaaaaaaaaaa
def x5 : Sig := 0xcccccccccccccccc
def x6 : Sig := 0x8888888888888888
def x7 : Sig := 0xaaaa0000aaaa0000
def x8 : Sig := 0xaaaaaaaa00000000
def x9 : Sig := 0xcccc0000cccc0000
def x10 : Sig := 0xcccccccc00000000
def x11 : Sig := 0xffff000000000000
def x12 : Sig := 0xeeeeeeeeeeeeeeee
def x13 : Sig := 0xffffaaaaffffaaaa
def x14 : Sig := 0xffffffffaaaaaaaa
def x15 : Sig := 0xffffccccffffcccc
def x16 : Sig := 0xffffffffcccccccc
def x17 : Sig := 0xffffffffffff0000
def x18 : Sig := 0x2222222222222222
def x19 : Sig := 0xaaaa0000aaaa
def x20 : Sig := 0xcccc0000cccc
def x21 : Sig := 0x4444444444444444
def x22 : Sig := 0x5555000055550000
def x23 : Sig := 0x5555555500000000
def x24 : Sig := 0x3333333300000000
def x25 : Sig := 0xaa00aa00aa00aa00
def x26 : Sig := 0xcc00cc00cc00cc00
def x27 : Sig := 0xff00ff0000000000
def x28 : Sig := 0x3300330033003300
def x29 : Sig := 0xa0a0a0a0a0a0a0a0
def x30 : Sig := 0xc0c0c0c0c0c0c0c0
def x31 : Sig := 0xf0f00000f0f00000
def x32 : Sig := 0xfafafafafafafafa
def x33 : Sig := 0x3030303030303030
def p0 := prefixPool s0 [] (by decide +kernel)
def p1 := prefixPool s0 [(0,x0,x1)] (by decide +kernel)
def p2 := prefixPool s1 [] (by decide +kernel)
def p3 := prefixPool s1 [(0,x2,x3)] (by decide +kernel)
def p4 := prefixPool s2 [] (by decide +kernel)
def p5 := prefixPool s2 [(0,x2,x3)] (by decide +kernel)
def p6 := prefixPool s3 [] (by decide +kernel)
def p7 := prefixPool s4 [] (by decide +kernel)
def p8 := prefixPool s4 [(0,x0,x1)] (by decide +kernel)
def p9 := prefixPool s4 [(2,x0,x1)] (by decide +kernel)
def p10 := prefixPool s5 [] (by decide +kernel)
def p11 := prefixPool s6 [] (by decide +kernel)
def p12 := prefixPool s6 [(0,x2,x3)] (by decide +kernel)
def p13 := prefixPool s7 [] (by decide +kernel)
def p14 := prefixPool s8 [] (by decide +kernel)
def p15 := prefixPool s8 [(0,x4,x5)] (by decide +kernel)
def p16 := prefixPool s8 [(0,x4,x5),(1,x6,x1)] (by decide +kernel)
def p17 := prefixPool s8 [(0,x4,x5),(1,x6,x3)] (by decide +kernel)
def p18 := prefixPool s8 [(0,x4,x5),(1,x4,x5)] (by decide +kernel)
def p19 := prefixPool s8 [(0,x4,x5),(2,x6,x3)] (by decide +kernel)
def p20 := prefixPool s8 [(0,x4,x5),(3,x6,x1)] (by decide +kernel)
def p21 := prefixPool s8 [(0,x4,x5),(3,x6,x3)] (by decide +kernel)
def p22 := prefixPool s8 [(0,x4,x1)] (by decide +kernel)
def p23 := prefixPool s8 [(0,x4,x1),(1,x7,x5)] (by decide +kernel)
def p24 := prefixPool s8 [(0,x4,x1),(1,x7,x3)] (by decide +kernel)
def p25 := prefixPool s8 [(0,x4,x1),(2,x7,x3)] (by decide +kernel)
def p26 := prefixPool s8 [(0,x4,x3)] (by decide +kernel)
def p27 := prefixPool s8 [(0,x4,x3),(1,x8,x5)] (by decide +kernel)
def p28 := prefixPool s8 [(0,x4,x3),(1,x8,x5),(1,x4,x3)] (by decide +kernel)
def p29 := prefixPool s8 [(0,x4,x3),(1,x8,x1)] (by decide +kernel)
def p30 := prefixPool s8 [(0,x4,x3),(1,x4,x3)] (by decide +kernel)
def p31 := prefixPool s8 [(0,x5,x1)] (by decide +kernel)
def p32 := prefixPool s8 [(0,x5,x1),(0,x9,x3)] (by decide +kernel)
def p33 := prefixPool s8 [(0,x5,x1),(1,x9,x4)] (by decide +kernel)
def p34 := prefixPool s8 [(0,x5,x1),(1,x5,x1)] (by decide +kernel)
def p35 := prefixPool s8 [(0,x5,x1),(3,x9,x4)] (by decide +kernel)
def p36 := prefixPool s8 [(0,x5,x1),(3,x9,x3)] (by decide +kernel)
def p37 := prefixPool s8 [(0,x5,x3)] (by decide +kernel)
def p38 := prefixPool s8 [(0,x5,x3),(1,x10,x4)] (by decide +kernel)
def p39 := prefixPool s8 [(0,x5,x3),(1,x10,x4),(1,x5,x3)] (by decide +kernel)
def p40 := prefixPool s8 [(0,x5,x3),(1,x10,x1)] (by decide +kernel)
def p41 := prefixPool s8 [(0,x5,x3),(1,x5,x3)] (by decide +kernel)
def p42 := prefixPool s8 [(0,x5,x3),(3,x10,x4)] (by decide +kernel)
def p43 := prefixPool s8 [(0,x1,x3)] (by decide +kernel)
def p44 := prefixPool s8 [(0,x1,x3),(1,x11,x5)] (by decide +kernel)
def p45 := prefixPool s8 [(0,x1,x3),(3,x11,x4)] (by decide +kernel)
def p46 := prefixPool s8 [(1,x4,x5)] (by decide +kernel)
def p47 := prefixPool s8 [(1,x4,x5),(0,x4,x5),(1,x6,x1)] (by decide +kernel)
def p48 := prefixPool s8 [(1,x4,x5),(0,x4,x5),(1,x6,x3)] (by decide +kernel)
def p49 := prefixPool s8 [(1,x4,x5),(0,x12,x1)] (by decide +kernel)
def p50 := prefixPool s8 [(1,x4,x5),(1,x5,x1)] (by decide +kernel)
def p51 := prefixPool s8 [(1,x4,x5),(1,x12,x1)] (by decide +kernel)
def p52 := prefixPool s8 [(1,x4,x5),(1,x12,x3)] (by decide +kernel)
def p53 := prefixPool s8 [(1,x4,x5),(2,x12,x1)] (by decide +kernel)
def p54 := prefixPool s8 [(1,x4,x5),(3,x12,x1)] (by decide +kernel)
def p55 := prefixPool s8 [(1,x4,x5),(3,x12,x3)] (by decide +kernel)
def p56 := prefixPool s8 [(1,x4,x1)] (by decide +kernel)
def p57 := prefixPool s8 [(1,x4,x1),(1,x5,x1)] (by decide +kernel)
def p58 := prefixPool s8 [(1,x4,x1),(1,x13,x3)] (by decide +kernel)
def p59 := prefixPool s8 [(1,x4,x3)] (by decide +kernel)
def p60 := prefixPool s8 [(1,x4,x3),(0,x14,x5)] (by decide +kernel)
def p61 := prefixPool s8 [(1,x4,x3),(1,x5,x3)] (by decide +kernel)
def p62 := prefixPool s8 [(1,x4,x3),(1,x1,x3)] (by decide +kernel)
def p63 := prefixPool s8 [(1,x4,x3),(2,x14,x5)] (by decide +kernel)
def p64 := prefixPool s8 [(1,x4,x3),(2,x14,x1)] (by decide +kernel)
def p65 := prefixPool s8 [(1,x5,x1)] (by decide +kernel)
def p66 := prefixPool s8 [(1,x5,x1),(0,x15,x4)] (by decide +kernel)
def p67 := prefixPool s8 [(1,x5,x3)] (by decide +kernel)
def p68 := prefixPool s8 [(1,x5,x3),(2,x16,x4)] (by decide +kernel)
def p69 := prefixPool s8 [(1,x1,x3)] (by decide +kernel)
def p70 := prefixPool s8 [(1,x1,x3),(0,x17,x5)] (by decide +kernel)
def p71 := prefixPool s8 [(1,x1,x3),(2,x17,x4)] (by decide +kernel)
def p72 := prefixPool s8 [(2,x4,x5)] (by decide +kernel)
def p73 := prefixPool s8 [(2,x4,x5),(0,x18,x3)] (by decide +kernel)
def p74 := prefixPool s8 [(2,x4,x5),(1,x18,x1)] (by decide +kernel)
def p75 := prefixPool s8 [(2,x4,x5),(2,x18,x1)] (by decide +kernel)
def p76 := prefixPool s8 [(2,x4,x5),(3,x18,x1)] (by decide +kernel)
def p77 := prefixPool s8 [(2,x4,x5),(3,x18,x3)] (by decide +kernel)
def p78 := prefixPool s8 [(2,x4,x5),(3,x4,x5)] (by decide +kernel)
def p79 := prefixPool s8 [(2,x4,x1)] (by decide +kernel)
def p80 := prefixPool s8 [(2,x4,x1),(1,x19,x3)] (by decide +kernel)
def p81 := prefixPool s8 [(2,x4,x1),(2,x19,x3)] (by decide +kernel)
def p82 := prefixPool s8 [(2,x4,x1),(3,x4,x1)] (by decide +kernel)
def p83 := prefixPool s8 [(2,x4,x3)] (by decide +kernel)
def p84 := prefixPool s8 [(2,x5,x1)] (by decide +kernel)
def p85 := prefixPool s8 [(2,x5,x1),(1,x20,x4)] (by decide +kernel)
def p86 := prefixPool s8 [(2,x5,x3)] (by decide +kernel)
def p87 := prefixPool s8 [(2,x1,x3)] (by decide +kernel)
def p88 := prefixPool s8 [(3,x4,x5)] (by decide +kernel)
def p89 := prefixPool s8 [(3,x4,x5),(1,x5,x3)] (by decide +kernel)
def p90 := prefixPool s8 [(3,x4,x5),(2,x21,x1)] (by decide +kernel)
def p91 := prefixPool s8 [(3,x4,x5),(2,x21,x3)] (by decide +kernel)
def p92 := prefixPool s8 [(3,x4,x1)] (by decide +kernel)
def p93 := prefixPool s8 [(3,x4,x1),(0,x22,x3)] (by decide +kernel)
def p94 := prefixPool s8 [(3,x4,x1),(1,x1,x3)] (by decide +kernel)
def p95 := prefixPool s8 [(3,x4,x3)] (by decide +kernel)
def p96 := prefixPool s8 [(3,x4,x3),(1,x23,x5)] (by decide +kernel)
def p97 := prefixPool s8 [(3,x4,x3),(1,x1,x3)] (by decide +kernel)
def p98 := prefixPool s8 [(3,x5,x1)] (by decide +kernel)
def p99 := prefixPool s8 [(3,x5,x3)] (by decide +kernel)
def p100 := prefixPool s8 [(3,x5,x3),(1,x24,x4)] (by decide +kernel)
def p101 := prefixPool s8 [(3,x5,x3),(3,x24,x1)] (by decide +kernel)
def p102 := prefixPool s8 [(3,x1,x3)] (by decide +kernel)
def p103 := prefixPool s9 [] (by decide +kernel)
def p104 := prefixPool s9 [(0,x4,x5)] (by decide +kernel)
def p105 := prefixPool s9 [(0,x4,x5),(1,x6,x0)] (by decide +kernel)
def p106 := prefixPool s9 [(0,x4,x5),(1,x6,x3)] (by decide +kernel)
def p107 := prefixPool s9 [(0,x4,x5),(1,x4,x5)] (by decide +kernel)
def p108 := prefixPool s9 [(0,x4,x5),(3,x6,x0)] (by decide +kernel)
def p109 := prefixPool s9 [(0,x4,x5),(3,x6,x3)] (by decide +kernel)
def p110 := prefixPool s9 [(0,x4,x0)] (by decide +kernel)
def p111 := prefixPool s9 [(0,x4,x0),(1,x25,x5)] (by decide +kernel)
def p112 := prefixPool s9 [(0,x4,x0),(1,x25,x3)] (by decide +kernel)
def p113 := prefixPool s9 [(0,x4,x3)] (by decide +kernel)
def p114 := prefixPool s9 [(0,x4,x3),(1,x8,x5)] (by decide +kernel)
def p115 := prefixPool s9 [(0,x4,x3),(1,x8,x5),(1,x4,x3)] (by decide +kernel)
def p116 := prefixPool s9 [(0,x4,x3),(1,x8,x0)] (by decide +kernel)
def p117 := prefixPool s9 [(0,x4,x3),(1,x4,x3)] (by decide +kernel)
def p118 := prefixPool s9 [(0,x5,x0)] (by decide +kernel)
def p119 := prefixPool s9 [(0,x5,x0),(1,x26,x4)] (by decide +kernel)
def p120 := prefixPool s9 [(0,x5,x0),(1,x26,x3)] (by decide +kernel)
def p121 := prefixPool s9 [(0,x5,x0),(3,x26,x4)] (by decide +kernel)
def p122 := prefixPool s9 [(0,x5,x3)] (by decide +kernel)
def p123 := prefixPool s9 [(0,x5,x3),(1,x10,x4)] (by decide +kernel)
def p124 := prefixPool s9 [(0,x5,x3),(1,x10,x4),(1,x5,x3)] (by decide +kernel)
def p125 := prefixPool s9 [(0,x5,x3),(3,x10,x4)] (by decide +kernel)
def p126 := prefixPool s9 [(0,x5,x3),(3,x10,x0)] (by decide +kernel)
def p127 := prefixPool s9 [(0,x0,x3)] (by decide +kernel)
def p128 := prefixPool s9 [(0,x0,x3),(1,x27,x5)] (by decide +kernel)
def p129 := prefixPool s9 [(0,x0,x3),(3,x27,x4)] (by decide +kernel)
def p130 := prefixPool s9 [(1,x4,x5)] (by decide +kernel)
def p131 := prefixPool s9 [(1,x4,x5),(0,x4,x5),(1,x6,x0)] (by decide +kernel)
def p132 := prefixPool s9 [(1,x4,x5),(0,x4,x5),(1,x6,x3)] (by decide +kernel)
def p133 := prefixPool s9 [(1,x4,x5),(2,x12,x0)] (by decide +kernel)
def p134 := prefixPool s9 [(1,x4,x5),(3,x12,x3)] (by decide +kernel)
def p135 := prefixPool s9 [(1,x4,x0)] (by decide +kernel)
def p136 := prefixPool s9 [(1,x4,x3)] (by decide +kernel)
def p137 := prefixPool s9 [(1,x4,x3),(1,x5,x3)] (by decide +kernel)
def p138 := prefixPool s9 [(1,x4,x3),(2,x14,x5)] (by decide +kernel)
def p139 := prefixPool s9 [(1,x4,x3),(2,x14,x0)] (by decide +kernel)
def p140 := prefixPool s9 [(1,x5,x0)] (by decide +kernel)
def p141 := prefixPool s9 [(1,x5,x3)] (by decide +kernel)
def p142 := prefixPool s9 [(1,x0,x3)] (by decide +kernel)
def p143 := prefixPool s9 [(2,x4,x5)] (by decide +kernel)
def p144 := prefixPool s9 [(2,x4,x5),(1,x18,x0)] (by decide +kernel)
def p145 := prefixPool s9 [(2,x4,x5),(1,x18,x3)] (by decide +kernel)
def p146 := prefixPool s9 [(2,x4,x5),(2,x18,x3)] (by decide +kernel)
def p147 := prefixPool s9 [(2,x4,x5),(3,x4,x5)] (by decide +kernel)
def p148 := prefixPool s9 [(2,x4,x0)] (by decide +kernel)
def p149 := prefixPool s9 [(2,x4,x0),(3,x4,x0)] (by decide +kernel)
def p150 := prefixPool s9 [(2,x4,x3)] (by decide +kernel)
def p151 := prefixPool s9 [(2,x4,x3),(3,x4,x3)] (by decide +kernel)
def p152 := prefixPool s9 [(2,x5,x0)] (by decide +kernel)
def p153 := prefixPool s9 [(3,x4,x5)] (by decide +kernel)
def p154 := prefixPool s9 [(3,x4,x0)] (by decide +kernel)
def p155 := prefixPool s9 [(3,x4,x0),(1,x0,x3)] (by decide +kernel)
def p156 := prefixPool s9 [(3,x4,x3)] (by decide +kernel)
def p157 := prefixPool s9 [(3,x5,x0)] (by decide +kernel)
def p158 := prefixPool s9 [(3,x5,x0),(1,x28,x4)] (by decide +kernel)
def p159 := prefixPool s9 [(3,x5,x0),(1,x28,x3)] (by decide +kernel)
def p160 := prefixPool s9 [(3,x5,x3)] (by decide +kernel)
def p161 := prefixPool s9 [(3,x5,x3),(1,x24,x4)] (by decide +kernel)
def p162 := prefixPool s9 [(3,x0,x3)] (by decide +kernel)
def p163 := prefixPool s10 [] (by decide +kernel)
def p164 := prefixPool s11 [] (by decide +kernel)
def p165 := prefixPool s12 [] (by decide +kernel)
def p166 := prefixPool s13 [] (by decide +kernel)
def p167 := prefixPool s14 [] (by decide +kernel)
def p168 := prefixPool s14 [(0,x4,x5)] (by decide +kernel)
def p169 := prefixPool s14 [(0,x4,x5),(1,x6,x2)] (by decide +kernel)
def p170 := prefixPool s14 [(0,x4,x5),(1,x6,x1)] (by decide +kernel)
def p171 := prefixPool s14 [(0,x4,x5),(1,x4,x5)] (by decide +kernel)
def p172 := prefixPool s14 [(0,x4,x5),(3,x6,x2)] (by decide +kernel)
def p173 := prefixPool s14 [(0,x4,x5),(3,x6,x1)] (by decide +kernel)
def p174 := prefixPool s14 [(0,x4,x2)] (by decide +kernel)
def p175 := prefixPool s14 [(0,x4,x2),(1,x29,x5)] (by decide +kernel)
def p176 := prefixPool s14 [(0,x4,x2),(1,x29,x1)] (by decide +kernel)
def p177 := prefixPool s14 [(0,x4,x2),(1,x4,x2)] (by decide +kernel)
def p178 := prefixPool s14 [(0,x4,x1)] (by decide +kernel)
def p179 := prefixPool s14 [(0,x4,x1),(1,x7,x5)] (by decide +kernel)
def p180 := prefixPool s14 [(0,x4,x1),(1,x7,x2)] (by decide +kernel)
def p181 := prefixPool s14 [(0,x5,x2)] (by decide +kernel)
def p182 := prefixPool s14 [(0,x5,x2),(1,x30,x4)] (by decide +kernel)
def p183 := prefixPool s14 [(0,x5,x2),(1,x30,x4),(1,x5,x2)] (by decide +kernel)
def p184 := prefixPool s14 [(0,x5,x2),(3,x30,x4)] (by decide +kernel)
def p185 := prefixPool s14 [(0,x5,x1)] (by decide +kernel)
def p186 := prefixPool s14 [(0,x5,x1),(1,x9,x2)] (by decide +kernel)
def p187 := prefixPool s14 [(0,x5,x1),(1,x5,x1)] (by decide +kernel)
def p188 := prefixPool s14 [(0,x5,x1),(3,x9,x4)] (by decide +kernel)
def p189 := prefixPool s14 [(0,x5,x1),(3,x9,x2)] (by decide +kernel)
def p190 := prefixPool s14 [(0,x2,x1),(3,x31,x4)] (by decide +kernel)
def p191 := prefixPool s14 [(1,x4,x5)] (by decide +kernel)
def p192 := prefixPool s14 [(1,x4,x5),(0,x4,x5),(1,x6,x2)] (by decide +kernel)
def p193 := prefixPool s14 [(1,x4,x5),(0,x4,x5),(1,x6,x1)] (by decide +kernel)
def p194 := prefixPool s14 [(1,x4,x5),(1,x12,x1)] (by decide +kernel)
def p195 := prefixPool s14 [(1,x4,x5),(2,x12,x1)] (by decide +kernel)
def p196 := prefixPool s14 [(1,x4,x2)] (by decide +kernel)
def p197 := prefixPool s14 [(1,x4,x2),(1,x5,x2)] (by decide +kernel)
def p198 := prefixPool s14 [(1,x4,x2),(2,x32,x5)] (by decide +kernel)
def p199 := prefixPool s14 [(1,x4,x1)] (by decide +kernel)
def p200 := prefixPool s14 [(1,x5,x2)] (by decide +kernel)
def p201 := prefixPool s14 [(1,x5,x1)] (by decide +kernel)
def p202 := prefixPool s14 [(1,x2,x1)] (by decide +kernel)
def p203 := prefixPool s14 [(2,x4,x5)] (by decide +kernel)
def p204 := prefixPool s14 [(2,x4,x5),(1,x4,x2)] (by decide +kernel)
def p205 := prefixPool s14 [(2,x4,x5),(3,x4,x5)] (by decide +kernel)
def p206 := prefixPool s14 [(2,x4,x2)] (by decide +kernel)
def p207 := prefixPool s14 [(2,x4,x2),(3,x4,x2)] (by decide +kernel)
def p208 := prefixPool s14 [(2,x4,x1)] (by decide +kernel)
def p209 := prefixPool s14 [(2,x4,x1),(3,x4,x1)] (by decide +kernel)
def p210 := prefixPool s14 [(2,x5,x2)] (by decide +kernel)
def p211 := prefixPool s14 [(2,x5,x2),(3,x5,x2)] (by decide +kernel)
def p212 := prefixPool s14 [(2,x5,x1)] (by decide +kernel)
def p213 := prefixPool s14 [(2,x2,x1)] (by decide +kernel)
def p214 := prefixPool s14 [(3,x4,x5)] (by decide +kernel)
def p215 := prefixPool s14 [(3,x4,x2)] (by decide +kernel)
def p216 := prefixPool s14 [(3,x4,x2),(1,x2,x1)] (by decide +kernel)
def p217 := prefixPool s14 [(3,x4,x1)] (by decide +kernel)
def p218 := prefixPool s14 [(3,x5,x2)] (by decide +kernel)
def p219 := prefixPool s14 [(3,x5,x2),(1,x33,x4)] (by decide +kernel)
def p220 := prefixPool s14 [(3,x5,x1)] (by decide +kernel)
def p221 := prefixPool s15 [] (by decide +kernel)
def p222 := prefixPool s15 [(0,x4,x5)] (by decide +kernel)
def p223 := prefixPool s15 [(0,x4,x5),(1,x6,x2)] (by decide +kernel)
def p224 := prefixPool s15 [(0,x4,x5),(1,x4,x5)] (by decide +kernel)
def p225 := prefixPool s15 [(0,x4,x5),(3,x6,x2)] (by decide +kernel)
def p226 := prefixPool s15 [(0,x4,x5),(3,x6,x0)] (by decide +kernel)
def p227 := prefixPool s15 [(0,x4,x2)] (by decide +kernel)
def p228 := prefixPool s15 [(0,x4,x2),(1,x29,x5)] (by decide +kernel)
def p229 := prefixPool s15 [(0,x4,x2),(1,x4,x2)] (by decide +kernel)
def p230 := prefixPool s15 [(0,x4,x2),(3,x29,x0)] (by decide +kernel)
def p231 := prefixPool s15 [(0,x4,x0),(1,x25,x2)] (by decide +kernel)
def p232 := prefixPool s15 [(0,x5,x2)] (by decide +kernel)
def p233 := prefixPool s15 [(0,x5,x2),(1,x30,x4)] (by decide +kernel)
def p234 := prefixPool s15 [(0,x5,x2),(3,x30,x4)] (by decide +kernel)
def p235 := prefixPool s15 [(0,x5,x2),(3,x30,x0)] (by decide +kernel)
def p236 := prefixPool s15 [(0,x5,x0),(3,x26,x4)] (by decide +kernel)
def p237 := prefixPool s15 [(0,x5,x0),(3,x26,x2)] (by decide +kernel)
def p238 := prefixPool s15 [(0,x2,x0)] (by decide +kernel)
def p239 := prefixPool s15 [(1,x4,x5)] (by decide +kernel)
def p240 := prefixPool s15 [(1,x4,x5),(0,x4,x5),(1,x6,x2)] (by decide +kernel)
def p241 := prefixPool s15 [(1,x4,x5),(0,x12,x2)] (by decide +kernel)
def p242 := prefixPool s15 [(1,x4,x2)] (by decide +kernel)
def p243 := prefixPool s15 [(1,x4,x2),(1,x5,x2)] (by decide +kernel)
def p244 := prefixPool s15 [(1,x4,x2),(2,x32,x5)] (by decide +kernel)
def p245 := prefixPool s15 [(1,x5,x2)] (by decide +kernel)
def p246 := prefixPool s15 [(2,x4,x5)] (by decide +kernel)
def p247 := prefixPool s15 [(2,x4,x5),(3,x4,x5)] (by decide +kernel)
def p248 := prefixPool s15 [(2,x4,x0)] (by decide +kernel)
def p249 := prefixPool s15 [(2,x4,x0),(3,x4,x0)] (by decide +kernel)
def p250 := prefixPool s15 [(2,x5,x2)] (by decide +kernel)
def p251 := prefixPool s15 [(2,x5,x2),(3,x5,x2)] (by decide +kernel)
def p252 := prefixPool s15 [(3,x4,x5)] (by decide +kernel)
def p253 := prefixPool s15 [(3,x4,x2)] (by decide +kernel)
def p254 := prefixPool s15 [(3,x5,x2)] (by decide +kernel)
def p255 := prefixPool s15 [(3,x5,x2),(1,x33,x4)] (by decide +kernel)
def p256 := prefixPool s28 [] (by decide +kernel)
def p257 := prefixPool s31 [] (by decide +kernel)
def p258 := prefixPool s35 [] (by decide +kernel)
def p259 := prefixPool s39 [] (by decide +kernel)
def p260 := prefixPool s42 [] (by decide +kernel)
def p261 := prefixPool s45 [] (by decide +kernel)
def p262 := prefixPool s48 [] (by decide +kernel)
def p263 := prefixPool s51 [] (by decide +kernel)
def p264 := prefixPool s55 [] (by decide +kernel)
def p265 := prefixPool s59 [] (by decide +kernel)
def p266 := prefixPool s62 [] (by decide +kernel)
def p267 := prefixPool s65 [] (by decide +kernel)
def p268 := prefixPool s68 [] (by decide +kernel)
def p269 := prefixPool s72 [] (by decide +kernel)
def p270 := prefixPool s76 [] (by decide +kernel)
def p271 := prefixPool s80 [] (by decide +kernel)
def q0 := usePool p0
def q1 := usePool p1
def q2 := usePool p2
def q3 := usePool p3
def q4 := usePool p4
def q5 := usePool p5
def q6 := usePool p6
def q7 := usePool p7
def q8 := usePool p8
def q9 := usePool p9
def q10 := usePool p10
def q11 := usePool p11
def q12 := usePool p12
def q13 := usePool p13
def q14 := usePool p14
def q15 := usePool p15
def q16 := usePool p16
def q17 := usePool p17
def q18 := usePool p18
def q19 := usePool p19
def q20 := usePool p20
def q21 := usePool p21
def q22 := usePool p22
def q23 := usePool p23
def q24 := usePool p24
def q25 := usePool p25
def q26 := usePool p26
def q27 := usePool p27
def q28 := usePool p28
def q29 := usePool p29
def q30 := usePool p30
def q31 := usePool p31
def q32 := usePool p32
def q33 := usePool p33
def q34 := usePool p34
def q35 := usePool p35
def q36 := usePool p36
def q37 := usePool p37
def q38 := usePool p38
def q39 := usePool p39
def q40 := usePool p40
def q41 := usePool p41
def q42 := usePool p42
def q43 := usePool p43
def q44 := usePool p44
def q45 := usePool p45
def q46 := usePool p46
def q47 := usePool p47
def q48 := usePool p48
def q49 := usePool p49
def q50 := usePool p50
def q51 := usePool p51
def q52 := usePool p52
def q53 := usePool p53
def q54 := usePool p54
def q55 := usePool p55
def q56 := usePool p56
def q57 := usePool p57
def q58 := usePool p58
def q59 := usePool p59
def q60 := usePool p60
def q61 := usePool p61
def q62 := usePool p62
def q63 := usePool p63
def q64 := usePool p64
def q65 := usePool p65
def q66 := usePool p66
def q67 := usePool p67
def q68 := usePool p68
def q69 := usePool p69
def q70 := usePool p70
def q71 := usePool p71
def q72 := usePool p72
def q73 := usePool p73
def q74 := usePool p74
def q75 := usePool p75
def q76 := usePool p76
def q77 := usePool p77
def q78 := usePool p78
def q79 := usePool p79
def q80 := usePool p80
def q81 := usePool p81
def q82 := usePool p82
def q83 := usePool p83
def q84 := usePool p84
def q85 := usePool p85
def q86 := usePool p86
def q87 := usePool p87
def q88 := usePool p88
def q89 := usePool p89
def q90 := usePool p90
def q91 := usePool p91
def q92 := usePool p92
def q93 := usePool p93
def q94 := usePool p94
def q95 := usePool p95
def q96 := usePool p96
def q97 := usePool p97
def q98 := usePool p98
def q99 := usePool p99
def q100 := usePool p100
def q101 := usePool p101
def q102 := usePool p102
def q103 := usePool p103
def q104 := usePool p104
def q105 := usePool p105
def q106 := usePool p106
def q107 := usePool p107
def q108 := usePool p108
def q109 := usePool p109
def q110 := usePool p110
def q111 := usePool p111
def q112 := usePool p112
def q113 := usePool p113
def q114 := usePool p114
def q115 := usePool p115
def q116 := usePool p116
def q117 := usePool p117
def q118 := usePool p118
def q119 := usePool p119
def q120 := usePool p120
def q121 := usePool p121
def q122 := usePool p122
def q123 := usePool p123
def q124 := usePool p124
def q125 := usePool p125
def q126 := usePool p126
def q127 := usePool p127
def q128 := usePool p128
def q129 := usePool p129
def q130 := usePool p130
def q131 := usePool p131
def q132 := usePool p132
def q133 := usePool p133
def q134 := usePool p134
def q135 := usePool p135
def q136 := usePool p136
def q137 := usePool p137
def q138 := usePool p138
def q139 := usePool p139
def q140 := usePool p140
def q141 := usePool p141
def q142 := usePool p142
def q143 := usePool p143
def q144 := usePool p144
def q145 := usePool p145
def q146 := usePool p146
def q147 := usePool p147
def q148 := usePool p148
def q149 := usePool p149
def q150 := usePool p150
def q151 := usePool p151
def q152 := usePool p152
def q153 := usePool p153
def q154 := usePool p154
def q155 := usePool p155
def q156 := usePool p156
def q157 := usePool p157
def q158 := usePool p158
def q159 := usePool p159
def q160 := usePool p160
def q161 := usePool p161
def q162 := usePool p162
def q163 := usePool p163
def q164 := joinPools p163 p0
def q165 := joinPools p163 p7
def q166 := usePool p164
def q167 := joinPools p164 p6
def q168 := usePool p165
def q169 := usePool p166
def q170 := joinPools p166 p11
def q171 := usePool p167
def q172 := usePool p168
def q173 := usePool p169
def q174 := usePool p170
def q175 := usePool p171
def q176 := usePool p172
def q177 := usePool p173
def q178 := usePool p174
def q179 := usePool p175
def q180 := usePool p176
def q181 := usePool p177
def q182 := usePool p178
def q183 := usePool p179
def q184 := usePool p180
def q185 := usePool p181
def q186 := usePool p182
def q187 := usePool p183
def q188 := usePool p184
def q189 := usePool p185
def q190 := usePool p186
def q191 := usePool p187
def q192 := usePool p188
def q193 := usePool p189
def q194 := usePool p190
def q195 := usePool p191
def q196 := usePool p192
def q197 := usePool p193
def q198 := usePool p194
def q199 := usePool p195
def q200 := usePool p196
def q201 := usePool p197
def q202 := usePool p198
def q203 := usePool p199
def q204 := usePool p200
def q205 := usePool p201
def q206 := usePool p202
def q207 := usePool p203
def q208 := usePool p204
def q209 := usePool p205
def q210 := usePool p206
def q211 := usePool p207
def q212 := usePool p208
def q213 := usePool p209
def q214 := usePool p210
def q215 := usePool p211
def q216 := usePool p212
def q217 := usePool p213
def q218 := usePool p214
def q219 := usePool p215
def q220 := usePool p216
def q221 := usePool p217
def q222 := usePool p218
def q223 := usePool p219
def q224 := usePool p220
def q225 := usePool p221
def q226 := usePool p222
def q227 := usePool p223
def q228 := usePool p224
def q229 := usePool p225
def q230 := usePool p226
def q231 := usePool p227
def q232 := usePool p228
def q233 := usePool p229
def q234 := usePool p230
def q235 := usePool p231
def q236 := usePool p232
def q237 := usePool p233
def q238 := usePool p234
def q239 := usePool p235
def q240 := usePool p236
def q241 := usePool p237
def q242 := usePool p238
def q243 := usePool p239
def q244 := usePool p240
def q245 := usePool p241
def q246 := usePool p242
def q247 := usePool p243
def q248 := usePool p244
def q249 := usePool p245
def q250 := usePool p246
def q251 := usePool p247
def q252 := usePool p248
def q253 := usePool p249
def q254 := usePool p250
def q255 := usePool p251
def q256 := usePool p252
def q257 := usePool p253
def q258 := usePool p254
def q259 := usePool p255
def q260 := usePool p256
def q261 := usePool p257
def q262 := usePool p258
def q263 := joinPools p258 p256
def q264 := joinPools p258 p257
def q265 := usePool p259
def q266 := joinPools p259 p257
def q267 := usePool p260
def q268 := usePool p261
def q269 := usePool p262
def q270 := usePool p263
def q271 := usePool p264
def q272 := usePool p265
def q273 := usePool p266
def q274 := usePool p267
def q275 := usePool p268
def q276 := usePool p269
def q277 := usePool p270
def q278 := usePool p271
def cc (k : Nat) (w : List (Observed (asRow Pos) (asRow Neg))) (ps : List (ChosenPool R T))
    (ns : List (Closed T (k-1))) (h : stateCheck k w (fun _ => (ps,ns)) = true) : Closed T k :=
  closeState (raw := R) correctPairs k w (fun _ => (ps,ns)) h
def n0 := cc 6 [w9,w2,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n1 := cc 7 [w7,w8,w2,w3,w4,w5] [q0,q7,q78,q147,q209] [n0] (by decide +kernel)
def n2 := cc 8 [w7,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q143,q207] [n1] (by decide +kernel)
def n3 := cc 7 [w6,w10,w2,w3,w4,w5] [q0,q18,q262] [n0] (by decide +kernel)
def n4 := cc 8 [w6,w0,w1,w2,w3,w4,w5] [q0,q7,q104,q172] [n3] (by decide +kernel)
def n5 := cc 7 [w9,w2,w3,w4,w5] [q4,q6,q260,q262,q265] [] (by decide +kernel)
def n6 := cc 7 [w9,w6,w2,w3,w4,w5] [q0,q2,q4,q6,q262] [] (by decide +kernel)
def n7 := cc 7 [w9,w10,w2,w3,w4,w5] [q0,q262,q265] [] (by decide +kernel)
def n8 := cc 7 [w9,w6,w10,w2,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n9 := cc 8 [w6,w10,w2,w3,w4,w5] [q0,q4,q175,q262,q265] [n8,n6,n7,n5] (by decide +kernel)
def n10 := cc 7 [w7,w9,w2,w3,w4,w5] [q0,q2,q4,q6,q7] [] (by decide +kernel)
def n11 := cc 8 [w7,w6,w10,w2,w3,w4,w5] [q2,q4,q271] [n10] (by decide +kernel)
def n12 := cc 7 [w9,w0,w2,w3,w4,w5] [q2,q4,q262] [] (by decide +kernel)
def n13 := cc 8 [w6,w0,w10,w2,w3,w4,w5] [q2,q262] [n12] (by decide +kernel)
def n14 := cc 7 [w7,w8,w9,w2,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def v0 : Closed T 7 := rotateClosed n10 auto8 auto8ok
def n15 := cc 8 [w7,w8,w2,w3,w4,w5] [q0,q4,q209,q262,q265] [n14,n10,v0,n5] (by decide +kernel)
def n16 := cc 8 [w7,w8,w6,w2,w3,w4,w5] [q0,q2,q4,q6,q7] [n6] (by decide +kernel)
def n17 := cc 8 [w7,w8,w0,w2,w3,w4,w5] [q2,q262] [n12] (by decide +kernel)
def v1 : Closed T 8 := rotateClosed n17 auto8 auto8ok
def v2 : Closed T 8 := rotateClosed n13 auto8 auto8ok
def n18 := cc 9 [w7,w6,w1,w2,w3,w4,w5] [q7,q14,q260,q268,q271,q272] [n16,v1,n15,n11,n2,n4,v2,n9] (by decide +kernel)
def n19 := cc 8 [w7,w6,w1,w2,w3,w4,w5] [q0,q2,q4,q7,q14] [n1,n3] (by decide +kernel)
def n20 := cc 8 [w7,w0,w10,w2,w3,w4,w5] [q2,q14,q262] [n1,n3] (by decide +kernel)
def n21 := cc 8 [w0,w1,w10,w2,w3,w4,w5] [q0,q7,q46,q130,q195] [n3] (by decide +kernel)
def n22 := cc 8 [w11,w0,w1,w2,w3,w4,w5] [q6,q46,q72,q143] [] (by decide +kernel)
def n23 := cc 8 [w0,w12,w1,w2,w3,w4,w5] [q7,q88,q153,q163] [] (by decide +kernel)
def n24 := cc 7 [w9,w0,w1,w2,w3,w4,w5] [q2,q4,q262] [] (by decide +kernel)
def n25 := cc 8 [w7,w8,w0,w1,w2,w3,w4,w5] [q2,q4,q262] [n24] (by decide +kernel)
def v3 : Closed T 8 := rotateClosed n22 auto2 auto2ok
def v4 : Closed T 8 := rotateClosed n22 auto3 auto3ok
def v5 : Closed T 8 := rotateClosed n22 auto6 auto6ok
def v6 : Closed T 8 := rotateClosed n23 auto8 auto8ok
def v7 : Closed T 8 := rotateClosed n23 auto10 auto10ok
def v8 : Closed T 8 := rotateClosed n23 auto11 auto11ok
def v9 : Closed T 8 := rotateClosed n23 auto14 auto14ok
def n26 := cc 9 [w7,w0,w1,w2,w3,w4,w5] [q0,q72,q250,q271,q272] [n22,v3,v4,v5,n25,n17,v1,n15,n19,n20,n4,v6,v7,v8,v9,n21] (by decide +kernel)
def n27 := cc 8 [w6,w0,w1,w10,w2,w3,w4,w5] [q2,q4,q262] [n24] (by decide +kernel)
def n28 := cc 9 [w7,w6,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q271] [n16,n25,n17,n11,n27,n13] (by decide +kernel)
def n29 := cc 7 [w14,w15,w2,w3,w4,w5] [q0,q209,q251] [] (by decide +kernel)
def n30 := cc 7 [w14,w1,w16,w3,w4,w5] [q6,q42,q125] [] (by decide +kernel)
def n31 := cc 8 [w14,w13,w1,w2,w3,w4,w5] [q0,q2,q6,q7,q14] [n29,n30] (by decide +kernel)
def n32 := cc 8 [w14,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q207,q250] [] (by decide +kernel)
def n33 := cc 7 [w14,w17,w1,w2,w3,w4] [] [] (by decide +kernel)
def n34 := cc 7 [w19,w0,w1,w3,w20,w5] [q0,q2,q229] [] (by decide +kernel)
def n35 := cc 7 [w19,w0,w1,w3,w4,w21] [q0,q176,q229] [] (by decide +kernel)
def v10 : Closed T 7 := rotateClosed n33 auto6 auto6ok
def v11 : Closed T 7 := rotateClosed n33 auto14 auto14ok
def v12 : Closed T 7 := rotateClosed n34 auto1 auto1ok
def n36 := cc 8 [w19,w18,w0,w1,w3,w4,w5] [q2,q6,q7,q104] [v10,v11,n35,n34,v12] (by decide +kernel)
def n37 := cc 8 [w19,w0,w1,w2,w3,w4,w5] [q0,q7,q15,q163] [] (by decide +kernel)
def n38 := cc 7 [w23,w0,w1,w3,w4,w5] [q0,q2,q229] [] (by decide +kernel)
def n39 := cc 7 [w26,w0,w1,w3,w4,w5] [q0,q2,q229] [] (by decide +kernel)
def v13 : Closed T 7 := rotateClosed n38 auto1 auto1ok
def v14 : Closed T 7 := rotateClosed n38 auto4 auto4ok
def v15 : Closed T 7 := rotateClosed n39 auto5 auto5ok
def v16 : Closed T 7 := rotateClosed n39 auto7 auto7ok
def n40 := cc 8 [w27,w0,w1,w2,w3,w4,w5] [q4,q6,q15,q88,q103,q171] [v13,v14,v15,v16] (by decide +kernel)
def n41 := cc 7 [w0,w1,w2,w28,w20,w5] [q6,q16,q105] [] (by decide +kernel)
def n42 := cc 7 [w23,w0,w1,w3,w4,w29] [q0,q2,q229] [] (by decide +kernel)
def n43 := cc 7 [w30,w0,w1,w3,w31,w5] [q0,q2,q229] [] (by decide +kernel)
def v17 : Closed T 7 := rotateClosed n43 auto6 auto6ok
def v18 : Closed T 7 := rotateClosed n38 auto5 auto5ok
def v19 : Closed T 7 := rotateClosed n42 auto4 auto4ok
def n44 := cc 8 [w18,w0,w1,w2,w3,w20,w5] [q2,q6,q104,q153,q225] [n34,v17,v18,v19,n41] (by decide +kernel)
def n45 := cc 8 [w23,w0,w1,w3,w4,w5] [q0,q10,q169,q229,q262] [] (by decide +kernel)
def n46 := cc 7 [w23,w0,w1,w32,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n47 := cc 7 [w30,w35,w0,w1,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n48 := cc 7 [w23,w36,w0,w1,w3,w4] [q0,q2,q4,q6] [] (by decide +kernel)
def v20 : Closed T 7 := rotateClosed n47 auto2 auto2ok
def n49 := cc 8 [w23,w24,w0,w1,w3,w4,w5] [q2,q4,q6,q7,q14] [v20,n48,n42,n46] (by decide +kernel)
def n50 := cc 8 [w23,w0,w1,w2,w3,w4,w5] [q0,q7,q104,q163] [] (by decide +kernel)
def n51 := cc 7 [w38,w1,w2,w3,w4,w5] [q0,q35,q121,q192] [] (by decide +kernel)
def n52 := cc 7 [w30,w0,w1,w3,w4,w5] [q0,q176,q229] [] (by decide +kernel)
def n53 := cc 7 [w39,w0,w1,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def v21 : Closed T 7 := rotateClosed n51 auto2 auto2ok
def v22 : Closed T 7 := rotateClosed n51 auto10 auto10ok
def v23 : Closed T 7 := rotateClosed n52 auto6 auto6ok
def v24 : Closed T 7 := rotateClosed n53 auto2 auto2ok
def v25 : Closed T 7 := rotateClosed n53 auto3 auto3ok
def n54 := cc 8 [w40,w0,w1,w2,w3,w4,w5] [q2,q4,q6,q7,q14,q103] [v21,v22,n52,v23,v24,v25] (by decide +kernel)
def v26 : Closed T 7 := rotateClosed n30 auto6 auto6ok
def v27 : Closed T 7 := rotateClosed n30 auto14 auto14ok
def v28 : Closed T 7 := rotateClosed n46 auto4 auto4ok
def v29 : Closed T 7 := rotateClosed n46 auto5 auto5ok
def n55 := cc 8 [w18,w0,w1,w2,w3,w4,w21] [q2,q4,q6,q7,q171,q225] [v26,v27,n35,v23,v28,v29] (by decide +kernel)
def n56 := cc 7 [w30,w0,w1,w41,w3,w4,w5] [q2,q8,q10,q163,q229] [] (by decide +kernel)
def n57 := cc 8 [w30,w0,w1,w3,w4,w5] [q0,q10,q11,q229,q262] [n56] (by decide +kernel)
def v30 : Closed T 7 := rotateClosed n47 auto1 auto1ok
def v31 : Closed T 7 := rotateClosed n43 auto1 auto1ok
def n58 := cc 8 [w30,w13,w0,w1,w3,w4,w5] [q0,q2,q4,q6,q7,q14] [n47,v30,n43,v31] (by decide +kernel)
def n59 := cc 8 [w30,w0,w1,w2,w3,w4,w5] [q7,q163,q260] [] (by decide +kernel)
def n60 := cc 8 [w18,w0,w1,w42,w3,w4,w5] [q12,q13,q103,q163,q171,q267] [] (by decide +kernel)
def n61 := cc 7 [w44,w0,w1,w2,w3,w4] [q6,q21,q109] [] (by decide +kernel)
def n62 := cc 8 [w43,w13,w0,w1,w2,w3,w4] [q0,q14,q172,q218,q226] [n61] (by decide +kernel)
def n63 := cc 7 [w0,w1,w2,w45,w3,w4,w5] [q7,q173,q261] [] (by decide +kernel)
def n64 := cc 7 [w0,w1,w42,w2,w45,w3,w4,w5] [q17,q19,q173] [] (by decide +kernel)
def v32 : Closed T 7 := rotateClosed n56 auto6 auto6ok
def v33 : Closed T 7 := rotateClosed n64 auto2 auto2ok
def v34 : Closed T 7 := rotateClosed n63 auto2 auto2ok
def n65 := cc 8 [w18,w0,w1,w2,w41,w3,w4,w5] [q10,q104,q168,q169,q171,q267] [v32,v33,v34] (by decide +kernel)
def v35 : Closed T 8 := rotateClosed n62 auto6 auto6ok
def v36 : Closed T 8 := rotateClosed n31 auto6 auto6ok
def v37 : Closed T 8 := rotateClosed n31 auto14 auto14ok
def v38 : Closed T 8 := rotateClosed n32 auto6 auto6ok
def v39 : Closed T 8 := rotateClosed n32 auto14 auto14ok
def v40 : Closed T 8 := rotateClosed n58 auto6 auto6ok
def v41 : Closed T 8 := rotateClosed n59 auto6 auto6ok
def v42 : Closed T 8 := rotateClosed n57 auto6 auto6ok
def v43 : Closed T 8 := rotateClosed n49 auto4 auto4ok
def v44 : Closed T 8 := rotateClosed n49 auto5 auto5ok
def v45 : Closed T 8 := rotateClosed n50 auto4 auto4ok
def v46 : Closed T 8 := rotateClosed n50 auto5 auto5ok
def v47 : Closed T 8 := rotateClosed n45 auto4 auto4ok
def v48 : Closed T 8 := rotateClosed n45 auto5 auto5ok
def v49 : Closed T 8 := rotateClosed n40 auto1 auto1ok
def v50 : Closed T 8 := rotateClosed n44 auto1 auto1ok
def n66 := cc 9 [w18,w0,w1,w2,w3,w4,w5] [q6,q10,q11,q103,q104,q171,q262] [v35,v36,v37,v38,v39,n36,n37,v40,v41,v42,v43,v44,v45,v46,v47,v48,n40,v49,n54,n60,n65,n55,n44,v50] (by decide +kernel)
def n67 := cc 8 [w14,w6,w1,w2,w3,w4,w5] [q0,q2,q6,q7,q14] [n3] (by decide +kernel)
def n68 := cc 6 [w9,w2,w3,w4,w46] [q0,q2,q4,q6] [] (by decide +kernel)
def n69 := cc 7 [w6,w10,w2,w3,w4,w46] [q0,q265] [n68] (by decide +kernel)
def v51 : Closed T 7 := rotateClosed n34 auto2 auto2ok
def n70 := cc 8 [w6,w0,w1,w2,w3,w4,w46] [q0,q7,q172,q226] [v51,n69] (by decide +kernel)
def n71 := cc 6 [w9,w23,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n72 := cc 7 [w23,w6,w10,w3,w4,w5] [q2,q262] [n71] (by decide +kernel)
def n73 := cc 8 [w23,w6,w0,w1,w3,w4,w5] [q0,q2,q4,q6,q7] [n72] (by decide +kernel)
def n74 := cc 6 [w10,w2,w32,w47,w5] [q131,q197] [] (by decide +kernel)
def n75 := cc 6 [w0,w1,w2,w48,w5] [q1,q8,q174] [] (by decide +kernel)
def n76 := cc 7 [w0,w1,w2,w32,w47,w5] [q0,q7,q16,q105] [n75,n74] (by decide +kernel)
def n77 := cc 6 [w9,w2,w3,w4,w21] [q0,q2,q4,q6] [] (by decide +kernel)
def v52 : Closed T 6 := rotateClosed n74 auto4 auto4ok
def n78 := cc 7 [w6,w10,w2,w3,w4,w21] [q0,q175,q262] [n77,v52] (by decide +kernel)
def v53 : Closed T 7 := rotateClosed n76 auto4 auto4ok
def n79 := cc 8 [w6,w0,w1,w2,w3,w4,w21] [q0,q7,q172,q226] [n35,n78,v53] (by decide +kernel)
def n80 := cc 6 [w9,w30,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n81 := cc 7 [w30,w6,w10,w3,w4,w5] [q2,q262] [n80] (by decide +kernel)
def n82 := cc 8 [w30,w6,w0,w1,w3,w4,w5] [q0,q2,q4,q6,q7] [n81] (by decide +kernel)
def n83 := cc 7 [w50,w0,w1,w2,w3,w4] [q0,q6,q172,q226] [] (by decide +kernel)
def n84 := cc 6 [w51,w2,w3,w4,w49] [q0,q2,q4,q6] [] (by decide +kernel)
def n85 := cc 6 [w50,w10,w2,w3,w4] [] [] (by decide +kernel)
def v54 : Closed T 6 := rotateClosed n84 auto6 auto6ok
def v55 : Closed T 6 := rotateClosed n85 auto6 auto6ok
def n86 := cc 7 [w18,w10,w52,w3,w4,w5] [q18,q262] [v54,v55,v52] (by decide +kernel)
def v56 : Closed T 6 := rotateClosed n75 auto2 auto2ok
def n87 := cc 7 [w18,w0,w1,w53,w3,w4] [q7,q15,q104,q262] [v56] (by decide +kernel)
def v57 : Closed T 7 := rotateClosed n83 auto6 auto6ok
def n88 := cc 8 [w18,w0,w1,w52,w3,w4,w5] [q0,q6,q7,q15,q103] [v57,n87,n86,v53] (by decide +kernel)
def n89 := cc 7 [w51,w6,w2,w3,w4,w5] [q2,q262] [n0,n84] (by decide +kernel)
def n90 := cc 6 [w9,w54,w2,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def v58 : Closed T 6 := rotateClosed n80 auto6 auto6ok
def v59 : Closed T 6 := rotateClosed n71 auto4 auto4ok
def v60 : Closed T 6 := rotateClosed n71 auto5 auto5ok
def v61 : Closed T 6 := rotateClosed n68 auto2 auto2ok
def v62 : Closed T 6 := rotateClosed n68 auto3 auto3ok
def n91 := cc 7 [w9,w18,w2,w3,w4,w5] [q0,q2,q4,q6] [v58,v59,v60,n90,n77,v61,v62] (by decide +kernel)
def v63 : Closed T 7 := rotateClosed n89 auto6 auto6ok
def v64 : Closed T 7 := rotateClosed n81 auto6 auto6ok
def v65 : Closed T 7 := rotateClosed n72 auto4 auto4ok
def v66 : Closed T 7 := rotateClosed n72 auto5 auto5ok
def v67 : Closed T 7 := rotateClosed n69 auto2 auto2ok
def v68 : Closed T 7 := rotateClosed n69 auto3 auto3ok
def n92 := cc 8 [w18,w6,w10,w2,w3,w4,w5] [q2,q4,q262] [n91,v63,v64,v65,v66,n86,n78,v67,v68] (by decide +kernel)
def v69 : Closed T 8 := rotateClosed n67 auto6 auto6ok
def v70 : Closed T 8 := rotateClosed n67 auto14 auto14ok
def v71 : Closed T 8 := rotateClosed n82 auto6 auto6ok
def v72 : Closed T 8 := rotateClosed n73 auto4 auto4ok
def v73 : Closed T 8 := rotateClosed n73 auto5 auto5ok
def v74 : Closed T 8 := rotateClosed n70 auto2 auto2ok
def v75 : Closed T 8 := rotateClosed n70 auto3 auto3ok
def n93 := cc 9 [w18,w6,w0,w1,w2,w3,w4,w5] [q2,q4,q6,q7,q14] [v69,v70,n36,v71,v72,v73,n92,n88,n79,v74,v75] (by decide +kernel)
def n94 := cc 7 [w10,w2,w52,w3,w4,w5,w49] [q48,q196,q262] [] (by decide +kernel)
def n95 := cc 7 [w0,w1,w55,w52,w3,w4,w5] [q7,q17,q106,q171,q262] [] (by decide +kernel)
def n96 := cc 7 [w0,w1,w2,w56,w3,w4,w5] [q7,q17,q106,q262] [] (by decide +kernel)
def v76 : Closed T 7 := rotateClosed n95 auto6 auto6ok
def n97 := cc 8 [w0,w1,w2,w52,w3,w4,w5,w49] [q0,q7,q106,q173] [n95,v76,n96,n94] (by decide +kernel)
def n98 := cc 6 [w9,w57,w52,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n99 := cc 6 [w9,w58,w2,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n100 := cc 6 [w9,w55,w3,w4,w5] [q262,q267,q268] [] (by decide +kernel)
def n101 := cc 6 [w59,w9,w2,w3,w4] [q6,q260,q261] [] (by decide +kernel)
def v77 : Closed T 6 := rotateClosed n100 auto6 auto6ok
def n102 := cc 7 [w9,w2,w52,w3,w4,w5] [q6,q260,q261,q262] [n101,n98,n99,v77] (by decide +kernel)
def n103 := cc 6 [w9,w60,w52,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n104 := cc 6 [w9,w61,w2,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n105 := cc 6 [w59,w9,w10,w2,w3,w4] [q6,q260,q261] [] (by decide +kernel)
def n106 := cc 7 [w9,w10,w2,w52,w3,w4,w5] [q260,q261,q262] [n105,n103,n104] (by decide +kernel)
def n107 := cc 7 [w6,w60,w10,w52,w3,w4,w5] [q0,q18,q107,q262] [n103] (by decide +kernel)
def n108 := cc 7 [w6,w61,w10,w2,w3,w4,w5] [q0,q18,q107,q262] [n104] (by decide +kernel)
def n109 := cc 7 [w6,w10,w55,w3,w4,w5] [q6,q175,q262] [n100] (by decide +kernel)
def n110 := cc 7 [w59,w6,w10,w2,w3,w4] [q0,q18,q107,q175] [n105,n101] (by decide +kernel)
def v78 : Closed T 7 := rotateClosed n109 auto6 auto6ok
def n111 := cc 8 [w6,w10,w2,w52,w3,w4,w5] [q0,q6,q18,q107,q262] [n110,n106,n102,n86,n107,n108,v78,n94] (by decide +kernel)
def n112 := cc 7 [w0,w1,w55,w56,w3,w4,w5] [q13,q173,q227,q262] [] (by decide +kernel)
def v79 : Closed T 7 := rotateClosed n87 auto6 auto6ok
def n113 := cc 8 [w6,w0,w1,w55,w3,w4,w5] [q0,q6,q13,q163,q172,q226] [v79,n109,n112] (by decide +kernel)
def n114 := cc 8 [w6,w0,w1,w55,w2,w3,w4,w5] [q6,q7,q172,q226,q262] [n95,n96] (by decide +kernel)
def n115 := cc 8 [w59,w6,w0,w1,w2,w3,w4] [q0,q7,q104,q172] [n110] (by decide +kernel)
def v80 : Closed T 8 := rotateClosed n114 auto6 auto6ok
def v81 : Closed T 8 := rotateClosed n113 auto6 auto6ok
def n116 := cc 9 [w6,w0,w1,w2,w52,w3,w4,w5] [q0,q6,q7,q15,q104,q166] [n115,n37,n88,v80,v81,n111,n97] (by decide +kernel)
def n117 := cc 8 [w18,w0,w1,w2,w3,w4,w5] [q6,q15,q88,q104,q171] [v23,v14,v18] (by decide +kernel)
def n118 := cc 8 [w6,w63,w1,w2,w3,w4,w5] [q0,q6,q7,q15] [n3] (by decide +kernel)
def n119 := cc 8 [w64,w17,w0,w1,w2,w3,w4] [q0,q6,q7,q172,q226] [n83] (by decide +kernel)
def n120 := cc 6 [w19,w54,w3,w4,w5] [q0,q6,q18,q107] [] (by decide +kernel)
def n121 := cc 7 [w6,w54,w2,w3,w4,w5] [q6,q18,q107] [n90,n0,n120] (by decide +kernel)
def n122 := cc 7 [w6,w54,w10,w2,w3,w4,w5] [q0,q18,q107,q262] [n90] (by decide +kernel)
def n123 := cc 7 [w64,w9,w2,w3,w4,w5] [q0,q2,q4,q6,q262] [] (by decide +kernel)
def v82 : Closed T 6 := rotateClosed n90 auto6 auto6ok
def n124 := cc 7 [w64,w9,w10,w2,w3,w4,w5] [q2,q4,q262] [v82] (by decide +kernel)
def v83 : Closed T 7 := rotateClosed n122 auto6 auto6ok
def v84 : Closed T 7 := rotateClosed n121 auto6 auto6ok
def n125 := cc 8 [w64,w6,w10,w2,w3,w4,w5] [q0,q175,q228] [n124,n123,v83,v84] (by decide +kernel)
def v85 : Closed T 8 := rotateClosed n117 auto6 auto6ok
def v86 : Closed T 8 := rotateClosed n118 auto6 auto6ok
def v87 : Closed T 8 := rotateClosed n118 auto14 auto14ok
def n126 := cc 9 [w64,w6,w0,w1,w2,w3,w4,w5] [q0,q7,q172,q226] [n119,n125,v85,v86,v87] (by decide +kernel)
def n127 := cc 8 [w65,w0,w1,w2,w3,w4,w5] [q0,q13,q172,q226] [] (by decide +kernel)
def n128 := cc 6 [w69,w0,w1,w2,w3] [q4,q11,q109,q177] [] (by decide +kernel)
def v88 : Closed T 6 := rotateClosed n128 auto5 auto5ok
def n129 := cc 7 [w70,w0,w1,w71,w4,w5] [q0,q108,q163] [v88] (by decide +kernel)
def n130 := cc 8 [w70,w0,w1,w2,w3,w4,w5] [q163,q168,q260] [n129] (by decide +kernel)
def n131 := cc 7 [w73,w0,w1,w3,w4,w5] [q6,q13,q163,q229] [] (by decide +kernel)
def v89 : Closed T 6 := rotateClosed n128 auto1 auto1ok
def n132 := cc 7 [w74,w76,w0,w1,w2,w4] [q2,q10,q230] [v89] (by decide +kernel)
def v90 : Closed T 7 := rotateClosed n132 auto7 auto7ok
def v91 : Closed T 7 := rotateClosed n131 auto4 auto4ok
def n133 := cc 8 [w77,w0,w1,w2,w3,w4,w5] [q4,q11,q14,q163,q168] [v90,v91,v18] (by decide +kernel)
def n134 := cc 6 [w80,w0,w1,w2,w5] [q2,q10,q20,q177] [] (by decide +kernel)
def v92 : Closed T 6 := rotateClosed n134 auto2 auto2ok
def n135 := cc 7 [w81,w0,w1,w3,w4,w82] [q0,q7,q21,q109,q163] [v92] (by decide +kernel)
def n136 := cc 8 [w81,w0,w1,w2,w3,w4,w5] [q13,q67,q169,q229,q262,q269,q270,q276] [n135] (by decide +kernel)
def n137 := cc 7 [w43,w83,w0,w1,w3,w4] [q0,q176,q229] [v92] (by decide +kernel)
def v93 : Closed T 7 := rotateClosed n137 auto6 auto6ok
def n138 := cc 8 [w84,w0,w1,w2,w3,w4,w5] [q13,q166,q267] [v93,v23] (by decide +kernel)
def n139 := cc 8 [w19,w85,w0,w1,w3,w4,w5] [q0,q2,q4,q6,q7,q14] [v11] (by decide +kernel)
def n140 := cc 8 [w86,w17,w0,w1,w2,w3,w4] [q0,q6,q7,q172,q226] [] (by decide +kernel)
def n141 := cc 8 [w19,w0,w1,w3,w71,w4,w5] [q0,q7,q104,q176] [n129] (by decide +kernel)
def n142 := cc 7 [w19,w0,w1,w3,w88,w5] [q2,q9,q104,q176] [] (by decide +kernel)
def v94 : Closed T 7 := rotateClosed n142 auto4 auto4ok
def v95 : Closed T 7 := rotateClosed n38 auto2 auto2ok
def n143 := cc 8 [w74,w75,w0,w1,w2,w4,w5] [q2,q6,q13,q15,q168,q230] [n132,v94,v95] (by decide +kernel)
def v96 : Closed T 7 := rotateClosed n61 auto6 auto6ok
def n144 := cc 8 [w19,w0,w1,w3,w4,w5,w82] [q0,q7,q104,q176] [n135,v96] (by decide +kernel)
def n145 := cc 8 [w43,w19,w0,w1,w3,w4,w5] [q0,q6,q7,q176,q229] [n137,n52] (by decide +kernel)
def n146 := cc 8 [w19,w0,w1,w2,w41,w3,w4,w5] [q14,q104,q168,q260,q269,q276] [] (by decide +kernel)
def v97 : Closed T 8 := rotateClosed n140 auto6 auto6ok
def v98 : Closed T 8 := rotateClosed n140 auto14 auto14ok
def v99 : Closed T 8 := rotateClosed n143 auto2 auto2ok
def v100 : Closed T 8 := rotateClosed n143 auto3 auto3ok
def v101 : Closed T 8 := rotateClosed n22 auto8 auto8ok
def v102 : Closed T 8 := rotateClosed n130 auto1 auto1ok
def v103 : Closed T 8 := rotateClosed n139 auto8 auto8ok
def v104 : Closed T 8 := rotateClosed n141 auto1 auto1ok
def v105 : Closed T 8 := rotateClosed n138 auto6 auto6ok
def v106 : Closed T 8 := rotateClosed n133 auto4 auto4ok
def v107 : Closed T 8 := rotateClosed n133 auto5 auto5ok
def v108 : Closed T 8 := rotateClosed n127 auto6 auto6ok
def v109 : Closed T 8 := rotateClosed n127 auto14 auto14ok
def n147 := cc 9 [w19,w0,w1,w2,w3,w4,w5] [q14,q104,q163,q171,q260,q262,q269,q270] [v97,v98,n145,v99,v100,n22,v101,n130,v102,n136,n36,n139,v103,n146,n141,v104,n144,n117,v105,v106,v107,v108,v109] (by decide +kernel)
def n148 := cc 8 [w81,w6,w0,w1,w2,w3,w4,w5] [q6,q7,q260,q261,q262] [n96] (by decide +kernel)
def n149 := cc 7 [w9,w19,w2,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n150 := cc 7 [w64,w17,w10,w2,w3,w4] [] [] (by decide +kernel)
def v110 : Closed T 7 := rotateClosed n150 auto6 auto6ok
def n151 := cc 8 [w19,w6,w10,w2,w3,w4,w5] [q260,q262] [v110,n149] (by decide +kernel)
def v111 : Closed T 8 := rotateClosed n119 auto6 auto6ok
def n152 := cc 9 [w19,w6,w0,w1,w2,w3,w4,w5] [q6,q7,q14,q163,q260,q261,q262] [v111,n148,n36,n151] (by decide +kernel)
def n153 := cc 6 [w89,w90,w3,w4,w5] [q260,q262] [] (by decide +kernel)
def n154 := cc 5 [w9,w91,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n155 := cc 6 [w89,w9,w90,w3,w4,w5] [q260,q261,q262] [n154] (by decide +kernel)
def n156 := cc 6 [w89,w92,w9,w2,w3,w4,w5] [q260,q262,q265] [] (by decide +kernel)
def n157 := cc 6 [w89,w9,w93,w2,w3,w4,w5] [q260] [] (by decide +kernel)
def n158 := cc 5 [w9,w2,w94,w3,w4,w5] [] [] (by decide +kernel)
def v112 : Closed T 5 := rotateClosed n158 auto2 auto2ok
def n159 := cc 6 [w89,w9,w2,w41,w3,w4,w5] [q4,q260,q262,q265] [v112] (by decide +kernel)
def v113 : Closed T 6 := rotateClosed n156 auto1 auto1ok
def v114 : Closed T 6 := rotateClosed n157 auto1 auto1ok
def n160 := cc 7 [w89,w9,w2,w3,w4,w5] [q260,q261,q262,q265] [n156,v113,n157,v114,n159,n155,n153] (by decide +kernel)
def n161 := cc 5 [w9,w42,w90,w3,w4,w95] [q0] [] (by decide +kernel)
def n162 := cc 6 [w9,w2,w90,w3,w4,w5,w95] [q0,q6,q262] [n161] (by decide +kernel)
def n163 := cc 6 [w96,w9,w2,w90,w3,w4,w5] [q0,q262] [] (by decide +kernel)
def n164 := cc 5 [w97,w9,w2,w3,w98,w5] [q265] [] (by decide +kernel)
def v115 : Closed T 5 := rotateClosed n164 auto2 auto2ok
def n165 := cc 6 [w9,w42,w2,w3,w4,w95] [q262,q267,q268] [v115,n161] (by decide +kernel)
def v116 : Closed T 6 := rotateClosed n165 auto6 auto6ok
def n166 := cc 7 [w9,w2,w90,w3,w4,w5] [q6,q260,q261,q262] [n163,n155,n153,v116,n162] (by decide +kernel)
def n167 := cc 6 [w9,w2,w3,w4,w100] [q6,q260,q261] [] (by decide +kernel)
def n168 := cc 6 [w9,w101,w3,w4,w5] [q262,q267,q268] [] (by decide +kernel)
def n169 := cc 6 [w96,w99,w9,w2,w3,w4,w5] [q0,q6,q262] [] (by decide +kernel)
def n170 := cc 6 [w96,w102,w2,w3,w4] [q262,q267] [] (by decide +kernel)
def v117 : Closed T 5 := rotateClosed n154 auto6 auto6ok
def n171 := cc 6 [w96,w9,w102,w2,w3,w4] [q262,q267,q268] [v117] (by decide +kernel)
def v118 : Closed T 6 := rotateClosed n167 auto6 auto6ok
def n172 := cc 7 [w96,w9,w2,w3,w4,w5] [q0,q262,q267,q268] [n169,n171,n163,n170,n168,v118] (by decide +kernel)
def n173 := cc 6 [w9,w57,w93,w2,w3,w4,w5] [q260,q262,q265] [] (by decide +kernel)
def n174 := cc 5 [w9,w2,w103,w3,w4,w5] [] [] (by decide +kernel)
def v119 : Closed T 5 := rotateClosed n174 auto2 auto2ok
def n175 := cc 6 [w9,w57,w2,w41,w3,w4,w5] [q4,q260,q262,q265] [v119] (by decide +kernel)
def v120 : Closed T 6 := rotateClosed n171 auto6 auto6ok
def v121 : Closed T 6 := rotateClosed n157 auto2 auto2ok
def v122 : Closed T 6 := rotateClosed n157 auto3 auto3ok
def v123 : Closed T 6 := rotateClosed n173 auto1 auto1ok
def n176 := cc 7 [w9,w57,w2,w3,w4,w5] [q260,q261,q262,q265] [v120,v121,v122,n173,v123,n175] (by decide +kernel)
def n177 := cc 6 [w9,w104,w71,w4,w5] [q260,q262,q266] [] (by decide +kernel)
def n178 := cc 7 [w9,w104,w2,w3,w4,w5] [q260,q262,q265] [n177] (by decide +kernel)
def n179 := cc 6 [w105,w9,w2,w3,w4,w5] [q2,q6,q261,q262] [] (by decide +kernel)
def n180 := cc 6 [w9,w106,w2,w3,w4,w5] [q261,q267] [] (by decide +kernel)
def n181 := cc 7 [w9,w2,w3,w71,w4,w5] [q261,q267] [n179,n180,n177] (by decide +kernel)
def n182 := cc 6 [w9,w107,w2,w3,w4,w5] [q0,q6,q262,q265] [] (by decide +kernel)
def n183 := cc 6 [w109,w9,w2,w3,w4,w5] [q6,q260,q261,q262] [] (by decide +kernel)
def n184 := cc 6 [w9,w2,w3,w4,w111] [q6,q260,q261] [] (by decide +kernel)
def n185 := cc 6 [w9,w113,w3,w4,w5] [q262,q265] [] (by decide +kernel)
def n186 := cc 6 [w74,w114,w9,w2,w4] [q263,q265] [] (by decide +kernel)
def v124 : Closed T 6 := rotateClosed n183 auto7 auto7ok
def v125 : Closed T 6 := rotateClosed n185 auto1 auto1ok
def v126 : Closed T 6 := rotateClosed n184 auto6 auto6ok
def n187 := cc 7 [w74,w9,w2,w3,w4,w5] [q6,q260,q262,q265] [n186,v124,n182,v125,v126] (by decide +kernel)
def n188 := cc 6 [w9,w2,w115,w3,w4,w5] [q2,q4,q262,q265] [] (by decide +kernel)
def v127 : Closed T 5 := rotateClosed n164 auto1 auto1ok
def n189 := cc 6 [w97,w9,w2,w3,w4,w5] [q0,q6,q262,q265] [n164,v127] (by decide +kernel)
def n190 := cc 5 [w116,w9,w2,w5] [q260,q265,q267] [] (by decide +kernel)
def v128 : Closed T 5 := rotateClosed n190 auto2 auto2ok
def n191 := cc 6 [w9,w42,w3,w4,w82] [q260,q261,q262] [v128] (by decide +kernel)
def n192 := cc 5 [w9,w2,w3,w117,w4,w5] [] [] (by decide +kernel)
def n193 := cc 6 [w9,w42,w2,w41,w3,w4,w5] [q6,q260,q261,q262,q265] [n192] (by decide +kernel)
def v129 : Closed T 6 := rotateClosed n189 auto2 auto2ok
def v130 : Closed T 6 := rotateClosed n159 auto2 auto2ok
def v131 : Closed T 6 := rotateClosed n159 auto3 auto3ok
def v132 : Closed T 6 := rotateClosed n175 auto2 auto2ok
def v133 : Closed T 6 := rotateClosed n175 auto3 auto3ok
def n194 := cc 7 [w9,w42,w2,w3,w4,w5] [q260,q261,q262,q265,q267,q268] [v129,v130,v131,v132,v133,n193,n165,v116,n191,n188] (by decide +kernel)
def v134 : Closed T 6 := rotateClosed n191 auto2 auto2ok
def n195 := cc 7 [w9,w2,w3,w4,w79,w5] [q260,q265,q267] [v134] (by decide +kernel)
def n196 := cc 6 [w9,w118,w2,w3,w4,w5] [q2,q4,q262,q265] [] (by decide +kernel)
def n197 := cc 6 [w120,w9,w2,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n198 := cc 6 [w43,w119,w9,w3,w4] [q6,q260,q261] [v128] (by decide +kernel)
def v135 : Closed T 6 := rotateClosed n197 auto6 auto6ok
def n199 := cc 7 [w43,w9,w2,w3,w4,w5] [q262,q267,q268] [n198,v135,n196] (by decide +kernel)
def v136 : Closed T 7 := rotateClosed n172 auto2 auto2ok
def v137 : Closed T 7 := rotateClosed n172 auto3 auto3ok
def v138 : Closed T 7 := rotateClosed n172 auto6 auto6ok
def v139 : Closed T 7 := rotateClosed n199 auto2 auto2ok
def v140 : Closed T 7 := rotateClosed n199 auto3 auto3ok
def v141 : Closed T 7 := rotateClosed n199 auto6 auto6ok
def v142 : Closed T 7 := rotateClosed n187 auto1 auto1ok
def v143 : Closed T 7 := rotateClosed n187 auto2 auto2ok
def v144 : Closed T 7 := rotateClosed n187 auto3 auto3ok
def v145 : Closed T 7 := rotateClosed n187 auto4 auto4ok
def v146 : Closed T 7 := rotateClosed n187 auto5 auto5ok
def v147 : Closed T 7 := rotateClosed n187 auto6 auto6ok
def v148 : Closed T 7 := rotateClosed n187 auto7 auto7ok
def v149 : Closed T 7 := rotateClosed n160 auto2 auto2ok
def v150 : Closed T 7 := rotateClosed n160 auto3 auto3ok
def v151 : Closed T 7 := rotateClosed n160 auto6 auto6ok
def v152 : Closed T 7 := rotateClosed n176 auto2 auto2ok
def v153 : Closed T 7 := rotateClosed n176 auto3 auto3ok
def v154 : Closed T 7 := rotateClosed n176 auto6 auto6ok
def v155 : Closed T 7 := rotateClosed n178 auto1 auto1ok
def v156 : Closed T 7 := rotateClosed n178 auto4 auto4ok
def v157 : Closed T 7 := rotateClosed n178 auto5 auto5ok
def v158 : Closed T 7 := rotateClosed n194 auto2 auto2ok
def v159 : Closed T 7 := rotateClosed n166 auto2 auto2ok
def v160 : Closed T 7 := rotateClosed n166 auto3 auto3ok
def v161 : Closed T 7 := rotateClosed n166 auto6 auto6ok
def v162 : Closed T 7 := rotateClosed n181 auto1 auto1ok
def v163 : Closed T 7 := rotateClosed n181 auto4 auto4ok
def v164 : Closed T 7 := rotateClosed n181 auto5 auto5ok
def v165 : Closed T 7 := rotateClosed n195 auto2 auto2ok
def n200 := cc 8 [w9,w2,w3,w4,w5] [] [n172,v136,v137,v138,n199,v139,v140,v141,n187,v142,v143,v144,v145,v146,v147,v148,n160,v149,v150,v151,n176,v152,v153,v154,n178,v155,v156,v157,n194,v158,n166,v159,v160,v161,n181,v162,v163,v164,n195,v165] (by decide +kernel)
def n201 := cc 7 [w89,w9,w6,w2,w3,w4,w5] [q260,q261,q262] [n104] (by decide +kernel)
def n202 := cc 7 [w9,w6,w57,w2,w3,w4,w5] [q260,q261,q262] [n98,n99] (by decide +kernel)
def n203 := cc 6 [w9,w6,w2,w115,w3,w4,w5] [q262] [] (by decide +kernel)
def n204 := cc 6 [w97,w9,w6,w2,w3,w4,w5] [q265] [] (by decide +kernel)
def n205 := cc 6 [w9,w2,w56,w3,w4,w5] [q6,q260,q261,q262] [] (by decide +kernel)
def v166 : Closed T 6 := rotateClosed n204 auto2 auto2ok
def n206 := cc 7 [w9,w6,w42,w2,w3,w4,w5] [q6,q260,q261,q262] [v166,n203,n205] (by decide +kernel)
def v167 : Closed T 7 := rotateClosed n123 auto2 auto2ok
def v168 : Closed T 7 := rotateClosed n123 auto3 auto3ok
def v169 : Closed T 7 := rotateClosed n123 auto6 auto6ok
def v170 : Closed T 7 := rotateClosed n201 auto2 auto2ok
def v171 : Closed T 7 := rotateClosed n201 auto3 auto3ok
def v172 : Closed T 7 := rotateClosed n201 auto6 auto6ok
def v173 : Closed T 7 := rotateClosed n149 auto2 auto2ok
def v174 : Closed T 7 := rotateClosed n149 auto3 auto3ok
def v175 : Closed T 7 := rotateClosed n149 auto6 auto6ok
def v176 : Closed T 7 := rotateClosed n91 auto2 auto2ok
def v177 : Closed T 7 := rotateClosed n91 auto3 auto3ok
def v178 : Closed T 7 := rotateClosed n91 auto6 auto6ok
def v179 : Closed T 7 := rotateClosed n202 auto2 auto2ok
def v180 : Closed T 7 := rotateClosed n202 auto3 auto3ok
def v181 : Closed T 7 := rotateClosed n202 auto6 auto6ok
def v182 : Closed T 7 := rotateClosed n206 auto2 auto2ok
def v183 : Closed T 7 := rotateClosed n102 auto2 auto2ok
def v184 : Closed T 7 := rotateClosed n102 auto3 auto3ok
def v185 : Closed T 7 := rotateClosed n102 auto6 auto6ok
def n207 := cc 8 [w9,w6,w2,w3,w4,w5] [q260,q261,q267,q268] [n123,v167,v168,v169,n201,v170,v171,v172,n149,v173,v174,v175,n91,v176,v177,v178,n202,v179,v180,v181,n8,n206,v182,n7,n102,v183,v184,v185,n3] (by decide +kernel)
def n208 := cc 6 [w9,w60,w90,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n209 := cc 7 [w9,w10,w2,w90,w3,w4,w5] [q260,q261,q262] [n208,n90] (by decide +kernel)
def n210 := cc 6 [w9,w10,w2,w3,w4,w100] [q6,q260,q261] [] (by decide +kernel)
def v186 : Closed T 6 := rotateClosed n104 auto6 auto6ok
def v187 : Closed T 6 := rotateClosed n210 auto6 auto6ok
def n211 := cc 7 [w96,w9,w10,w2,w3,w4,w5] [q262,q267,q268] [v186,v187] (by decide +kernel)
def n212 := cc 7 [w9,w60,w2,w3,w4,w5] [q260,q261,q262,q265] [n208,n90] (by decide +kernel)
def n213 := cc 6 [w9,w122,w3,w4,w5] [q260,q262,q265] [] (by decide +kernel)
def n214 := cc 6 [w123,w9,w2,w3,w4] [q6,q260,q265] [] (by decide +kernel)
def n215 := cc 6 [w9,w125,w3,w4,w5] [q262,q265] [] (by decide +kernel)
def n216 := cc 6 [w127,w9,w2,w3,w4] [q6,q260,q261] [] (by decide +kernel)
def v188 : Closed T 6 := rotateClosed n214 auto2 auto2ok
def v189 : Closed T 6 := rotateClosed n214 auto3 auto3ok
def v190 : Closed T 6 := rotateClosed n213 auto2 auto2ok
def v191 : Closed T 6 := rotateClosed n213 auto3 auto3ok
def v192 : Closed T 6 := rotateClosed n215 auto6 auto6ok
def n217 := cc 7 [w9,w2,w126,w3,w4,w5] [q260,q261,q262] [n216,v188,v189,n99,v190,v191,v192] (by decide +kernel)
def n218 := cc 7 [w128,w9,w2,w3,w4,w5] [q262,q267,q268] [] (by decide +kernel)
def n219 := cc 7 [w129,w9,w2,w3,w4,w5] [q0,q262,q265] [] (by decide +kernel)
def n220 := cc 6 [w105,w9,w10,w2,w3,w4,w5] [q0] [] (by decide +kernel)
def n221 := cc 6 [w9,w106,w10,w2,w3,w4,w5] [q0] [] (by decide +kernel)
def n222 := cc 6 [w9,w130,w2,w3,w4,w5] [q261,q262] [] (by decide +kernel)
def n223 := cc 7 [w9,w10,w2,w3,w71,w4,w5] [q2,q261,q262] [n220,n221,n222] (by decide +kernel)
def v193 : Closed T 7 := rotateClosed n211 auto2 auto2ok
def v194 : Closed T 7 := rotateClosed n211 auto3 auto3ok
def v195 : Closed T 7 := rotateClosed n211 auto6 auto6ok
def v196 : Closed T 7 := rotateClosed n218 auto2 auto2ok
def v197 : Closed T 7 := rotateClosed n218 auto3 auto3ok
def v198 : Closed T 7 := rotateClosed n218 auto6 auto6ok
def v199 : Closed T 7 := rotateClosed n219 auto2 auto2ok
def v200 : Closed T 7 := rotateClosed n219 auto3 auto3ok
def v201 : Closed T 7 := rotateClosed n219 auto6 auto6ok
def v202 : Closed T 7 := rotateClosed n212 auto2 auto2ok
def v203 : Closed T 7 := rotateClosed n212 auto3 auto3ok
def v204 : Closed T 7 := rotateClosed n212 auto6 auto6ok
def v205 : Closed T 7 := rotateClosed n209 auto2 auto2ok
def v206 : Closed T 7 := rotateClosed n209 auto3 auto3ok
def v207 : Closed T 7 := rotateClosed n209 auto6 auto6ok
def v208 : Closed T 7 := rotateClosed n223 auto1 auto1ok
def v209 : Closed T 7 := rotateClosed n223 auto4 auto4ok
def v210 : Closed T 7 := rotateClosed n223 auto5 auto5ok
def v211 : Closed T 7 := rotateClosed n217 auto2 auto2ok
def v212 : Closed T 7 := rotateClosed n217 auto3 auto3ok
def v213 : Closed T 7 := rotateClosed n217 auto6 auto6ok
def n224 := cc 8 [w9,w10,w2,w3,w4,w5] [q262,q265] [n211,v193,v194,v195,n218,v196,v197,v198,n219,v199,v200,v201,n8,n6,n212,v202,v203,v204,n209,v205,v206,v207,n223,v208,v209,v210,n217,v211,v212,v213,n3] (by decide +kernel)
def n225 := cc 7 [w9,w6,w60,w2,w3,w4,w5] [q260,q261,q262] [n103,n104] (by decide +kernel)
def n226 := cc 7 [w129,w9,w6,w2,w3,w4,w5] [q260,q261,q262] [n99] (by decide +kernel)
def v214 : Closed T 7 := rotateClosed n124 auto2 auto2ok
def v215 : Closed T 7 := rotateClosed n124 auto3 auto3ok
def v216 : Closed T 7 := rotateClosed n124 auto6 auto6ok
def v217 : Closed T 7 := rotateClosed n226 auto2 auto2ok
def v218 : Closed T 7 := rotateClosed n226 auto3 auto3ok
def v219 : Closed T 7 := rotateClosed n226 auto6 auto6ok
def v220 : Closed T 7 := rotateClosed n225 auto2 auto2ok
def v221 : Closed T 7 := rotateClosed n225 auto3 auto3ok
def v222 : Closed T 7 := rotateClosed n225 auto6 auto6ok
def v223 : Closed T 7 := rotateClosed n106 auto2 auto2ok
def v224 : Closed T 7 := rotateClosed n106 auto3 auto3ok
def v225 : Closed T 7 := rotateClosed n106 auto6 auto6ok
def n227 := cc 8 [w9,w6,w10,w2,w3,w4,w5] [q4,q6,q260,q262,q265] [n124,v214,v215,v216,n226,v217,v218,v219,n225,v220,v221,v222,n106,v223,v224,v225] (by decide +kernel)
def n228 := cc 6 [w131,w60,w3,w4,w5] [q0,q18,q262] [] (by decide +kernel)
def n229 := cc 6 [w6,w60,w132,w4,w5] [q0,q18,q262] [] (by decide +kernel)
def v226 : Closed T 6 := rotateClosed n229 auto1 auto1ok
def n230 := cc 7 [w6,w60,w126,w3,w4,w5] [q0,q18,q107,q262] [n228,n229,v226] (by decide +kernel)
def n231 := cc 7 [w6,w60,w133,w2,w3,w4,w5] [q260,q262,q265] [] (by decide +kernel)
def v227 : Closed T 7 := rotateClosed n231 auto1 auto1ok
def n232 := cc 8 [w6,w60,w10,w2,w3,w4,w5] [q107,q260,q262,q265] [n225,n212,n231,v227,n107,n230,n108] (by decide +kernel)
def n233 := cc 7 [w131,w10,w2,w3,w4,w5] [q0,q18,q262] [n0,n228] (by decide +kernel)
def v228 : Closed T 6 := rotateClosed n229 auto2 auto2ok
def n234 := cc 7 [w6,w10,w122,w3,w4,w5] [q2,q262] [n213,v228] (by decide +kernel)
def n235 := cc 7 [w123,w6,w10,w2,w3,w4] [q2,q262] [n214] (by decide +kernel)
def n236 := cc 7 [w6,w10,w125,w3,w4,w5] [q6,q175,q262] [n215] (by decide +kernel)
def n237 := cc 7 [w127,w6,w10,w2,w3,w4] [q0,q18,q262] [n216] (by decide +kernel)
def v229 : Closed T 7 := rotateClosed n235 auto2 auto2ok
def v230 : Closed T 7 := rotateClosed n235 auto3 auto3ok
def v231 : Closed T 7 := rotateClosed n234 auto2 auto2ok
def v232 : Closed T 7 := rotateClosed n234 auto3 auto3ok
def v233 : Closed T 7 := rotateClosed n236 auto6 auto6ok
def n238 := cc 8 [w6,w10,w2,w126,w3,w4,w5] [q0,q18,q107,q262] [n237,v229,v230,n217,n233,n230,v231,v232,v233] (by decide +kernel)
def n239 := cc 6 [w135,w6,w2,w3,w4] [q6,q175,q262] [] (by decide +kernel)
def n240 := cc 6 [w128,w136,w2,w3,w4] [q262,q265] [] (by decide +kernel)
def n241 := cc 7 [w128,w134,w6,w2,w3,w4] [q6,q175,q262] [n240,n239] (by decide +kernel)
def n242 := cc 8 [w128,w6,w10,w2,w3,w4,w5] [q6,q175,q262] [n241,n218] (by decide +kernel)
def n243 := cc 7 [w58,w10,w2,w3,w4,w5] [q262,q265] [n99,n0] (by decide +kernel)
def n244 := cc 7 [w6,w58,w10,w2,w3,w4,w5] [q260,q261,q262] [n99] (by decide +kernel)
def n245 := cc 8 [w129,w6,w10,w2,w3,w4,w5] [q262,q265] [n226,n219,n244,n243] (by decide +kernel)
def n246 := cc 6 [w6,w130,w104,w4,w5] [q0,q18,q107,q175] [] (by decide +kernel)
def n247 := cc 6 [w138,w6,w10,w2,w3] [q4,q175,q262,q264] [] (by decide +kernel)
def v234 : Closed T 6 := rotateClosed n247 auto5 auto5ok
def n248 := cc 7 [w6,w10,w104,w71,w4,w5] [q0,q262] [v234,n177,n246] (by decide +kernel)
def n249 := cc 8 [w6,w10,w104,w2,w3,w4,w5] [q260,q262] [n178,n248] (by decide +kernel)
def n250 := cc 7 [w6,w130,w2,w3,w4,w5] [q0,q18,q107,q175] [n246] (by decide +kernel)
def n251 := cc 7 [w6,w130,w10,w2,w3,w4,w5] [q0,q18,q107,q262] [n222] (by decide +kernel)
def n252 := cc 6 [w140,w2,w3,w4,w5] [q2,q261,q262] [] (by decide +kernel)
def n253 := cc 7 [w139,w6,w2,w3,w4,w5] [q0,q18,q262] [n252] (by decide +kernel)
def n254 := cc 8 [w6,w10,w2,w3,w71,w4,w5] [q0,q18,q107,q175,q262] [n253,n223,n181,n251,n250,n248] (by decide +kernel)
def n255 := cc 7 [w6,w10,w2,w3,w4,w111] [q0,q265] [n184] (by decide +kernel)
def n256 := cc 7 [w6,w10,w113,w3,w4,w5] [q6,q175,q262] [n185] (by decide +kernel)
def v235 : Closed T 6 := rotateClosed n247 auto1 auto1ok
def n257 := cc 7 [w74,w114,w6,w10,w2,w4] [q2,q228,q262] [n186,v235] (by decide +kernel)
def v236 : Closed T 7 := rotateClosed n256 auto1 auto1ok
def v237 : Closed T 7 := rotateClosed n255 auto6 auto6ok
def n258 := cc 8 [w74,w6,w10,w2,w3,w4,w5] [q0,q6,q262,q265] [n257,n187,v236,v237] (by decide +kernel)
def n259 := cc 6 [w10,w2,w142,w79,w5] [q47,q197,q265] [] (by decide +kernel)
def n260 := cc 6 [w10,w143,w2,w3,w142,w4,w5] [q47,q131] [] (by decide +kernel)
def n261 := cc 6 [w144,w10,w2,w3,w142,w4,w5] [q47,q131] [] (by decide +kernel)
def n262 := cc 4 [w146,w2,w3,w4,w5] [] [] (by decide +kernel)
def n263 := cc 5 [w10,w2,w3,w145,w4,w5] [] [n262] (by decide +kernel)
def n264 := cc 5 [w147,w10,w2,w3,w4,w5] [] [] (by decide +kernel)
def v238 : Closed T 5 := rotateClosed n264 auto2 auto2ok
def n265 := cc 6 [w10,w42,w2,w3,w142,w4,w5] [q47,q131,q265] [v238,n263] (by decide +kernel)
def v239 : Closed T 6 := rotateClosed n261 auto2 auto2ok
def v240 : Closed T 6 := rotateClosed n261 auto3 auto3ok
def v241 : Closed T 6 := rotateClosed n260 auto2 auto2ok
def v242 : Closed T 6 := rotateClosed n260 auto3 auto3ok
def v243 : Closed T 6 := rotateClosed n265 auto2 auto2ok
def v244 : Closed T 6 := rotateClosed n259 auto2 auto2ok
def n266 := cc 7 [w10,w2,w56,w3,w4,w5] [q0,q6,q48,q132,q196,q244,q262] [v239,v240,v241,v242,v243,v244] (by decide +kernel)
def n267 := cc 7 [w6,w10,w2,w56,w3,w4,w5] [q6,q260,q261,q262] [n205] (by decide +kernel)
def n268 := cc 6 [w149,w2,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def v245 : Closed T 6 := rotateClosed n268 auto2 auto2ok
def n269 := cc 7 [w150,w10,w2,w3,w4,w5] [q0,q265] [v245] (by decide +kernel)
def n270 := cc 6 [w116,w6,w10,w2,w5] [q2,q18,q265] [n190] (by decide +kernel)
def v246 : Closed T 6 := rotateClosed n270 auto2 auto2ok
def n271 := cc 7 [w6,w10,w42,w3,w4,w82] [q0,q18,q262] [v246,n191,v244] (by decide +kernel)
def n272 := cc 5 [w6,w151,w2,w3,w4,w5] [] [n262] (by decide +kernel)
def n273 := cc 6 [w6,w10,w2,w3,w117,w4,w5] [q0,q262] [n192,n272,n263] (by decide +kernel)
def n274 := cc 7 [w6,w10,w42,w2,w41,w3,w4,w5] [q0,q2,q18,q107,q175,q262,q265] [n193,n273,n265,v243] (by decide +kernel)
def v247 : Closed T 7 := rotateClosed n269 auto2 auto2ok
def n275 := cc 8 [w6,w10,w42,w2,w3,w4,w5] [q6,q175,q228,q260,q261,q262,q265] [v247,n206,n194,n274,n271,n267,n266] (by decide +kernel)
def v248 : Closed T 7 := rotateClosed n271 auto2 auto2ok
def n276 := cc 8 [w6,w10,w2,w3,w4,w79,w5] [q2,q18,q265] [n195,v248] (by decide +kernel)
def n277 := cc 7 [w43,w119,w6,w10,w3,w4] [q0,q18,q262] [n198,v246] (by decide +kernel)
def n278 := cc 8 [w43,w6,w10,w2,w3,w4,w5] [q6,q175,q228,q262] [n277,n199] (by decide +kernel)
def v249 : Closed T 8 := rotateClosed n125 auto2 auto2ok
def v250 : Closed T 8 := rotateClosed n125 auto3 auto3ok
def v251 : Closed T 8 := rotateClosed n125 auto6 auto6ok
def v252 : Closed T 8 := rotateClosed n242 auto2 auto2ok
def v253 : Closed T 8 := rotateClosed n242 auto3 auto3ok
def v254 : Closed T 8 := rotateClosed n242 auto6 auto6ok
def v255 : Closed T 8 := rotateClosed n278 auto2 auto2ok
def v256 : Closed T 8 := rotateClosed n278 auto3 auto3ok
def v257 : Closed T 8 := rotateClosed n278 auto6 auto6ok
def v258 : Closed T 8 := rotateClosed n258 auto1 auto1ok
def v259 : Closed T 8 := rotateClosed n258 auto2 auto2ok
def v260 : Closed T 8 := rotateClosed n258 auto3 auto3ok
def v261 : Closed T 8 := rotateClosed n258 auto4 auto4ok
def v262 : Closed T 8 := rotateClosed n258 auto5 auto5ok
def v263 : Closed T 8 := rotateClosed n258 auto6 auto6ok
def v264 : Closed T 8 := rotateClosed n258 auto7 auto7ok
def v265 : Closed T 8 := rotateClosed n245 auto2 auto2ok
def v266 : Closed T 8 := rotateClosed n245 auto3 auto3ok
def v267 : Closed T 8 := rotateClosed n245 auto6 auto6ok
def v268 : Closed T 8 := rotateClosed n151 auto2 auto2ok
def v269 : Closed T 8 := rotateClosed n151 auto3 auto3ok
def v270 : Closed T 8 := rotateClosed n151 auto6 auto6ok
def v271 : Closed T 8 := rotateClosed n92 auto2 auto2ok
def v272 : Closed T 8 := rotateClosed n92 auto3 auto3ok
def v273 : Closed T 8 := rotateClosed n92 auto6 auto6ok
def v274 : Closed T 8 := rotateClosed n232 auto2 auto2ok
def v275 : Closed T 8 := rotateClosed n232 auto3 auto3ok
def v276 : Closed T 8 := rotateClosed n232 auto6 auto6ok
def v277 : Closed T 8 := rotateClosed n249 auto1 auto1ok
def v278 : Closed T 8 := rotateClosed n249 auto4 auto4ok
def v279 : Closed T 8 := rotateClosed n249 auto5 auto5ok
def v280 : Closed T 8 := rotateClosed n275 auto2 auto2ok
def v281 : Closed T 8 := rotateClosed n111 auto2 auto2ok
def v282 : Closed T 8 := rotateClosed n111 auto3 auto3ok
def v283 : Closed T 8 := rotateClosed n111 auto6 auto6ok
def v284 : Closed T 8 := rotateClosed n238 auto2 auto2ok
def v285 : Closed T 8 := rotateClosed n238 auto3 auto3ok
def v286 : Closed T 8 := rotateClosed n238 auto6 auto6ok
def v287 : Closed T 8 := rotateClosed n254 auto1 auto1ok
def v288 : Closed T 8 := rotateClosed n254 auto4 auto4ok
def v289 : Closed T 8 := rotateClosed n254 auto5 auto5ok
def v290 : Closed T 8 := rotateClosed n276 auto2 auto2ok
def n279 := cc 9 [w6,w10,w2,w3,w4,w5] [] [n125,v249,v250,v251,n242,v252,v253,v254,n278,v255,v256,v257,n258,v258,v259,v260,v261,v262,v263,v264,n245,v265,v266,v267,n227,n207,n224,n200,n151,v268,v269,v270,n92,v271,v272,v273,n232,v274,v275,v276,n249,v277,v278,v279,n275,v280,n111,v281,v282,v283,n238,v284,v285,v286,n254,v287,v288,v289,n276,v290] (by decide +kernel)
def n280 := cc 7 [w9,w85,w2,w3,w4,w5] [q0,q2,q4,q6,q7] [n90] (by decide +kernel)
def n281 := cc 6 [w9,w153,w3,w4,w5] [q262,q265] [] (by decide +kernel)
def n282 := cc 6 [w155,w9,w2,w3,w4] [q6,q260,q261] [] (by decide +kernel)
def v291 : Closed T 6 := rotateClosed n281 auto6 auto6ok
def n283 := cc 7 [w9,w2,w154,w3,w4,w5] [q260,q261,q262,q271] [n282,n99,v291] (by decide +kernel)
def n284 := cc 7 [w86,w9,w2,w3,w4,w5] [q2,q4,q262] [] (by decide +kernel)
def n285 := cc 7 [w156,w9,w2,w3,w4,w5] [q262,q269,q270] [] (by decide +kernel)
def v292 : Closed T 7 := rotateClosed n284 auto2 auto2ok
def v293 : Closed T 7 := rotateClosed n284 auto3 auto3ok
def v294 : Closed T 7 := rotateClosed n284 auto6 auto6ok
def v295 : Closed T 7 := rotateClosed n285 auto8 auto8ok
def v296 : Closed T 7 := rotateClosed n285 auto10 auto10ok
def v297 : Closed T 7 := rotateClosed n285 auto11 auto11ok
def v298 : Closed T 7 := rotateClosed n285 auto14 auto14ok
def v299 : Closed T 7 := rotateClosed n280 auto2 auto2ok
def v300 : Closed T 7 := rotateClosed n280 auto3 auto3ok
def v301 : Closed T 7 := rotateClosed n280 auto6 auto6ok
def v302 : Closed T 7 := rotateClosed n283 auto2 auto2ok
def v303 : Closed T 7 := rotateClosed n283 auto3 auto3ok
def v304 : Closed T 7 := rotateClosed n283 auto6 auto6ok
def n286 := cc 8 [w9,w0,w2,w3,w4,w5] [q4,q6,q260,q262,q265] [n284,v292,v293,v294,n10,v0,v295,v296,v297,v298,n6,n280,v299,v300,v301,n7,n283,v302,v303,v304] (by decide +kernel)
def n287 := cc 8 [w9,w6,w0,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q262] [n10,n8,n3] (by decide +kernel)
def n288 := cc 8 [w9,w0,w10,w2,w3,w4,w5] [q0,q262,q265,q271] [v0,n8,n3] (by decide +kernel)
def n289 := cc 8 [w9,w6,w0,w10,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q271] [] (by decide +kernel)
def n290 := cc 8 [w6,w85,w10,w2,w3,w4,w5] [q2,q4,q262] [n280] (by decide +kernel)
def n291 := cc 7 [w6,w10,w153,w3,w4,w5] [q6,q175,q262] [n281] (by decide +kernel)
def n292 := cc 7 [w155,w6,w10,w2,w3,w4] [q0,q18,q262] [n282] (by decide +kernel)
def v305 : Closed T 7 := rotateClosed n291 auto6 auto6ok
def n293 := cc 8 [w6,w10,w2,w154,w3,w4,w5] [q0,q18,q107,q262] [n292,n283,v305] (by decide +kernel)
def n294 := cc 8 [w86,w6,w10,w2,w3,w4,w5] [q0,q175,q262] [n284] (by decide +kernel)
def n295 := cc 8 [w156,w6,w10,w2,w3,w4,w5] [q262,q269] [n285] (by decide +kernel)
def v306 : Closed T 8 := rotateClosed n294 auto2 auto2ok
def v307 : Closed T 8 := rotateClosed n294 auto3 auto3ok
def v308 : Closed T 8 := rotateClosed n294 auto6 auto6ok
def v309 : Closed T 8 := rotateClosed n19 auto8 auto8ok
def v310 : Closed T 8 := rotateClosed n11 auto8 auto8ok
def v311 : Closed T 8 := rotateClosed n295 auto8 auto8ok
def v312 : Closed T 8 := rotateClosed n295 auto10 auto10ok
def v313 : Closed T 8 := rotateClosed n295 auto11 auto11ok
def v314 : Closed T 8 := rotateClosed n295 auto14 auto14ok
def v315 : Closed T 8 := rotateClosed n290 auto2 auto2ok
def v316 : Closed T 8 := rotateClosed n290 auto3 auto3ok
def v317 : Closed T 8 := rotateClosed n290 auto6 auto6ok
def v318 : Closed T 8 := rotateClosed n293 auto2 auto2ok
def v319 : Closed T 8 := rotateClosed n293 auto3 auto3ok
def v320 : Closed T 8 := rotateClosed n293 auto6 auto6ok
def n296 := cc 9 [w6,w0,w10,w2,w3,w4,w5] [q4,q6,q260,q262,q265] [n294,v306,v307,v308,v309,n11,v310,n20,v311,v312,v313,v314,n289,n287,n288,n286,n290,v315,v316,v317,n293,v318,v319,v320] (by decide +kernel)
def n297 := cc 8 [w9,w0,w1,w2,w3,w4,w5] [q4,q6,q7,q10,q11,q13,q260,q262,q265,q271,q272] [n10,v0,n6,n7] (by decide +kernel)
def n298 := cc 8 [w9,w6,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q262,q271] [n8] (by decide +kernel)
def n299 := cc 8 [w9,w0,w1,w10,w2,w3,w4,w5] [q0,q7,q262,q265,q271] [n8] (by decide +kernel)
def n300 := cc 8 [w9,w6,w0,w1,w10,w2,w3,w4,w5] [q0,q7,q262,q271] [] (by decide +kernel)
def n301 := cc 8 [w6,w0,w1,w60,w2,w3,w4,w5] [q7,q46,q260,q261,q262] [] (by decide +kernel)
def n302 := cc 7 [w58,w0,w1,w2,w3,w4,w5] [q260,q261,q262] [] (by decide +kernel)
def n303 := cc 8 [w129,w6,w0,w1,w2,w3,w4,w5] [q260,q261,q262] [n302] (by decide +kernel)
def v321 : Closed T 8 := rotateClosed n303 auto2 auto2ok
def v322 : Closed T 8 := rotateClosed n303 auto3 auto3ok
def v323 : Closed T 8 := rotateClosed n303 auto6 auto6ok
def v324 : Closed T 8 := rotateClosed n301 auto2 auto2ok
def v325 : Closed T 8 := rotateClosed n301 auto3 auto3ok
def v326 : Closed T 8 := rotateClosed n301 auto6 auto6ok
def n304 := cc 9 [w6,w0,w1,w10,w2,w3,w4,w5] [q4,q6,q7,q10,q11,q13,q46,q130,q195,q260,q262,q265,q271,q272] [n303,v321,v322,v323,n11,v310,n300,n298,n299,n297,n301,v324,v325,v326] (by decide +kernel)
def n305 := cc 8 [w6,w0,w157,w2,w3,w4,w5] [q0,q2,q4,q6,q262,q271] [n3] (by decide +kernel)
def n306 := cc 8 [w6,w0,w1,w159,w2,w3,w4,w5] [q10,q11,q262,q271] [] (by decide +kernel)
def n307 := cc 7 [w162,w6,w0,w2,w3,w4] [q6,q7,q172,q218,q226] [] (by decide +kernel)
def v327 : Closed T 7 := rotateClosed n307 auto14 auto14ok
def n308 := cc 8 [w6,w85,w1,w154,w3,w4,w5] [q0,q6,q15,q88,q104] [v327] (by decide +kernel)
def v328 : Closed T 8 := rotateClosed n306 auto8 auto8ok
def n309 := cc 9 [w6,w85,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q14,q262,q271] [n22,v70,n139,n117,n308,n290,v328,n305] (by decide +kernel)
def n310 := cc 8 [w163,w0,w1,w2,w3,w4,w5] [q0,q6,q7,q15,q104,q166] [] (by decide +kernel)
def n311 := cc 7 [w0,w1,w153,w164,w3,w4,w5] [q6,q13,q59,q136] [] (by decide +kernel)
def n312 := cc 8 [w6,w0,w1,w153,w3,w4,w5] [q6,q13,q163,q172,q226] [n291,n311] (by decide +kernel)
def n313 := cc 8 [w6,w0,w1,w153,w2,w3,w4,w5] [q0,q13,q59,q172,q226,q262] [] (by decide +kernel)
def n314 := cc 8 [w155,w6,w0,w1,w2,w3,w4] [q0,q7,q104,q172] [n292] (by decide +kernel)
def v329 : Closed T 8 := rotateClosed n313 auto6 auto6ok
def v330 : Closed T 8 := rotateClosed n312 auto6 auto6ok
def n315 := cc 9 [w6,w0,w1,w2,w154,w3,w4,w5] [q0,q6,q7,q15,q104,q166,q200] [n314,n310,n308,v329,v330,n293] (by decide +kernel)
def n316 := cc 8 [w6,w0,w165,w2,w3,w4,w5] [q0,q13,q172] [n3] (by decide +kernel)
def v331 : Closed T 7 := rotateClosed n307 auto8 auto8ok
def n317 := cc 8 [w86,w166,w6,w1,w2,w3,w4] [q0,q6,q172,q218,q226] [v331] (by decide +kernel)
def n318 := cc 9 [w86,w6,w0,w1,w2,w3,w4,w5] [q0,q13,q172,q226] [n317,n140,n294,v85,v87,n316,n127] (by decide +kernel)
def n319 := cc 8 [w0,w167,w1,w2,w3,w4,w5] [q7,q13,q88,q153,q262] [] (by decide +kernel)
def n320 := cc 7 [w0,w169,w1,w2,w3,w4,w5] [q262,q269,q270] [] (by decide +kernel)
def n321 := cc 8 [w168,w6,w0,w1,w2,w3,w4,w5] [q262,q269,q270] [n320] (by decide +kernel)
def n322 := cc 9 [w156,w6,w0,w1,w2,w3,w4,w5] [q0,q13,q222,q262,q269,q270,q271] [n303,n321,n295,n319] (by decide +kernel)
def n323 := cc 7 [w0,w1,w2,w171,w3,w4,w5] [q260,q262] [] (by decide +kernel)
def n324 := cc 8 [w6,w0,w1,w170,w2,w3,w4,w5] [q104,q262,q269] [n323] (by decide +kernel)
def n325 := cc 7 [w138,w6,w0,w1,w2,w3] [q4,q11,q104,q172,q226] [n247] (by decide +kernel)
def v332 : Closed T 7 := rotateClosed n325 auto5 auto5ok
def n326 := cc 8 [w6,w0,w1,w104,w71,w4,w5] [q0,q7,q15,q104,q172] [v332,n129,n248] (by decide +kernel)
def v333 : Closed T 8 := rotateClosed n324 auto2 auto2ok
def n327 := cc 9 [w6,w0,w1,w104,w2,w3,w4,w5] [q14,q104,q172,q260,q262,q265,q269] [n130,n40,n324,v333,n326,n249] (by decide +kernel)
def n328 := cc 7 [w173,w0,w1,w3,w4,w5] [q0,q104,q176] [] (by decide +kernel)
def v334 : Closed T 7 := rotateClosed n328 auto5 auto5ok
def v335 : Closed T 7 := rotateClosed n328 auto7 auto7ok
def n329 := cc 8 [w174,w0,w1,w2,w3,w4,w5] [q0,q88,q104,q172] [v334,v335] (by decide +kernel)
def n330 := cc 8 [w175,w0,w1,w2,w3,w4,w5] [q0,q88,q104,q172] [] (by decide +kernel)
def n331 := cc 7 [w6,w177,w2,w3,w4,w5] [q0,q18,q262] [] (by decide +kernel)
def v336 : Closed T 7 := rotateClosed n331 auto8 auto8ok
def n332 := cc 8 [w6,w178,w1,w2,w3,w4,w5] [q0,q7,q104,q172] [v336] (by decide +kernel)
def n333 := cc 8 [w179,w6,w0,w2,w3,w4,w5] [q0,q7,q172] [n253] (by decide +kernel)
def v337 : Closed T 8 := rotateClosed n333 auto8 auto8ok
def v338 : Closed T 8 := rotateClosed n141 auto2 auto2ok
def v339 : Closed T 8 := rotateClosed n332 auto8 auto8ok
def n334 := cc 9 [w6,w0,w1,w2,w3,w71,w4,w5] [q0,q7,q104,q172] [n333,v337,n141,v338,n330,n329,n332,v339,n326,n254] (by decide +kernel)
def n335 := cc 8 [w180,w0,w1,w2,w3,w4,w5] [q6,q13,q14,q163,q172,q226] [] (by decide +kernel)
def n336 := cc 8 [w181,w0,w1,w2,w3,w4,w5] [q0,q6,q15,q88,q104] [v18] (by decide +kernel)
def v340 : Closed T 7 := rotateClosed n142 auto2 auto2ok
def n337 := cc 8 [w6,w0,w1,w2,w3,w4,w111] [q0,q7,q104,q172] [v340,n255] (by decide +kernel)
def n338 := cc 8 [w6,w0,w1,w113,w3,w4,w5] [q6,q13,q163,q172,q226,q275] [n256] (by decide +kernel)
def n339 := cc 8 [w6,w0,w1,w113,w2,w3,w4,w5] [q13,q104,q172,q262,q275] [] (by decide +kernel)
def v341 : Closed T 7 := rotateClosed n325 auto1 auto1ok
def n340 := cc 8 [w74,w114,w6,w0,w1,w2,w4] [q2,q10,q15,q226] [n257,v341] (by decide +kernel)
def v342 : Closed T 8 := rotateClosed n336 auto7 auto7ok
def v343 : Closed T 8 := rotateClosed n339 auto1 auto1ok
def v344 : Closed T 8 := rotateClosed n338 auto1 auto1ok
def v345 : Closed T 8 := rotateClosed n337 auto6 auto6ok
def n341 := cc 9 [w74,w6,w0,w1,w2,w3,w4,w5] [q6,q13,q15,q163,q172,q226] [n340,n143,n258,v342,v343,v344,v345,n335] (by decide +kernel)
def n342 := cc 6 [w0,w1,w2,w48,w142,w5] [q8,q174,q265] [] (by decide +kernel)
def n343 := cc 7 [w0,w1,w2,w142,w79,w5] [q2,q10,q16,q174] [n342,n75,n259] (by decide +kernel)
def n344 := cc 7 [w0,w1,w143,w2,w3,w142,w4,w5] [q16,q105,q163] [n260] (by decide +kernel)
def n345 := cc 7 [w144,w0,w1,w2,w3,w142,w4,w5] [q16,q105,q163] [n261] (by decide +kernel)
def n346 := cc 6 [w0,w1,w2,w3,w145,w4,w5] [q0,q7,q103,q171] [n263] (by decide +kernel)
def n347 := cc 6 [w147,w0,w1,w2,w3,w4,w5] [] [n264] (by decide +kernel)
def v346 : Closed T 6 := rotateClosed n347 auto2 auto2ok
def n348 := cc 7 [w0,w1,w42,w2,w3,w142,w4,w5] [q16,q105,q163,q166,q265] [v346,n346,n265] (by decide +kernel)
def v347 : Closed T 7 := rotateClosed n345 auto2 auto2ok
def v348 : Closed T 7 := rotateClosed n345 auto3 auto3ok
def v349 : Closed T 7 := rotateClosed n344 auto2 auto2ok
def v350 : Closed T 7 := rotateClosed n344 auto3 auto3ok
def v351 : Closed T 7 := rotateClosed n348 auto2 auto2ok
def v352 : Closed T 7 := rotateClosed n112 auto6 auto6ok
def v353 : Closed T 7 := rotateClosed n343 auto2 auto2ok
def n349 := cc 8 [w0,w1,w2,w56,w3,w4,w5] [q6,q13,q14,q168,q169,q171,q173,q227,q260,q262,q270,q271] [v347,v348,v349,v350,v351,n112,v352,v353,n266] (by decide +kernel)
def n350 := cc 8 [w6,w0,w1,w2,w56,w3,w4,w5] [q6,q7,q260,q261,q262,q271] [n267] (by decide +kernel)
def n351 := cc 7 [w182,w0,w1,w2,w3,w142,w4,w5] [q16,q163,q265] [] (by decide +kernel)
def n352 := cc 6 [w116,w0,w1,w2,w142,w5] [q10,q16,q174,q265] [] (by decide +kernel)
def v354 : Closed T 6 := rotateClosed n352 auto2 auto2ok
def n353 := cc 7 [w0,w1,w42,w56,w3,w4,w82] [q7,q17,q106,q262] [v354] (by decide +kernel)
def v355 : Closed T 7 := rotateClosed n351 auto2 auto2ok
def v356 : Closed T 7 := rotateClosed n351 auto3 auto3ok
def n354 := cc 8 [w0,w1,w42,w2,w56,w3,w4,w5] [q7,q13,q17,q106,q173,q227,q262,q271,q275] [v355,v356,n353] (by decide +kernel)
def n355 := cc 8 [w6,w0,w1,w42,w2,w56,w3,w4,w5] [q0,q6,q262,q271] [] (by decide +kernel)
def n356 := cc 8 [w150,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q7] [n269] (by decide +kernel)
def v357 : Closed T 7 := rotateClosed n96 auto2 auto2ok
def n357 := cc 8 [w150,w0,w1,w2,w41,w3,w4,w5] [q4,q10,q260,q265,q267] [v357] (by decide +kernel)
def n358 := cc 8 [w6,w0,w1,w2,w183,w3,w4,w5] [q6,q7,q260,q261,q262,q271] [] (by decide +kernel)
def n359 := cc 8 [w182,w6,w0,w1,w2,w3,w4,w5] [q104,q260,q262,q269,q275] [] (by decide +kernel)
def n360 := cc 8 [w182,w6,w0,w1,w2,w41,w3,w4,w5] [q260,q265,q275,q276] [n351] (by decide +kernel)
def n361 := cc 7 [w184,w0,w1,w2,w41,w5] [q1,q8,q14,q172,q265] [n75] (by decide +kernel)
def n362 := cc 7 [w116,w6,w0,w1,w2,w5] [q2,q10,q15,q168,q172,q265] [n270] (by decide +kernel)
def n363 := cc 7 [w116,w6,w0,w1,w2,w41,w5] [q10,q15,q172,q265] [n352] (by decide +kernel)
def v358 : Closed T 7 := rotateClosed n363 auto2 auto2ok
def v359 : Closed T 7 := rotateClosed n362 auto2 auto2ok
def v360 : Closed T 7 := rotateClosed n361 auto2 auto2ok
def n364 := cc 8 [w6,w0,w1,w42,w3,w4,w82] [q0,q7,q15,q104,q163] [v358,v359,n135,v360,n271,n353,v353] (by decide +kernel)
def n365 := cc 6 [w185,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n366 := cc 7 [w6,w0,w1,w2,w3,w117,w4,w5] [q0,q7,q262,q271] [n365,n273,n346] (by decide +kernel)
def n367 := cc 8 [w6,w0,w1,w42,w2,w41,w3,w4,w5] [q260,q261,q262,q265,q267,q275,q276] [n366,n274,n348,v351] (by decide +kernel)
def v361 : Closed T 8 := rotateClosed n357 auto2 auto2ok
def v362 : Closed T 8 := rotateClosed n356 auto2 auto2ok
def v363 : Closed T 8 := rotateClosed n360 auto2 auto2ok
def v364 : Closed T 8 := rotateClosed n360 auto3 auto3ok
def v365 : Closed T 8 := rotateClosed n359 auto2 auto2ok
def v366 : Closed T 8 := rotateClosed n359 auto3 auto3ok
def v367 : Closed T 8 := rotateClosed n321 auto8 auto8ok
def v368 : Closed T 8 := rotateClosed n146 auto2 auto2ok
def v369 : Closed T 8 := rotateClosed n146 auto3 auto3ok
def v370 : Closed T 8 := rotateClosed n60 auto6 auto6ok
def v371 : Closed T 8 := rotateClosed n65 auto2 auto2ok
def v372 : Closed T 8 := rotateClosed n65 auto3 auto3ok
def v373 : Closed T 8 := rotateClosed n324 auto3 auto3ok
def v374 : Closed T 8 := rotateClosed n358 auto8 auto8ok
def n368 := cc 9 [w6,w0,w1,w42,w2,w3,w4,w5] [q6,q13,q14,q171,q172,q226,q260,q262,q270,q271] [v361,v362,v363,v364,v365,v366,n321,v367,n148,n136,v368,v369,n54,n60,v370,v371,v372,v333,v373,n355,n367,n364,n350,n358,v374,n275,n354,n349] (by decide +kernel)
def n369 := cc 7 [w186,w0,w1,w3,w4,w5] [q0,q104,q176] [] (by decide +kernel)
def v375 : Closed T 7 := rotateClosed n369 auto6 auto6ok
def n370 := cc 8 [w184,w0,w1,w2,w3,w4,w5] [q0,q88,q104,q172] [n369,v375,n361] (by decide +kernel)
def n371 := cc 8 [w187,w0,w1,w2,w3,w4,w5] [q2,q88,q104,q172] [] (by decide +kernel)
def v376 : Closed T 8 := rotateClosed n144 auto2 auto2ok
def v377 : Closed T 8 := rotateClosed n144 auto3 auto3ok
def v378 : Closed T 8 := rotateClosed n364 auto2 auto2ok
def n372 := cc 9 [w6,w0,w1,w2,w3,w4,w79,w5] [q2,q10,q104,q172] [v376,v377,n371,n370,v378,n276] (by decide +kernel)
def n373 := cc 8 [w188,w0,w1,w2,w3,w4,w5] [q6,q7,q163,q172,q226] [] (by decide +kernel)
def n374 := cc 8 [w189,w0,w1,w2,w3,w4,w5] [q0,q6,q15,q88,q104] [v23] (by decide +kernel)
def n375 := cc 8 [w6,w0,w1,w42,w2,w3,w4,w5] [q7,q15,q104,q262] [n96] (by decide +kernel)
def n376 := cc 8 [w43,w119,w6,w0,w1,w3,w4] [q0,q7,q104,q172] [n277,v359] (by decide +kernel)
def v379 : Closed T 8 := rotateClosed n374 auto6 auto6ok
def n377 := cc 9 [w43,w6,w0,w1,w2,w3,w4,w5] [q6,q13,q14,q104,q163,q172,q226] [n376,n145,n62,n278,v379,n375,n373] (by decide +kernel)
def v380 : Closed T 9 := rotateClosed n126 auto2 auto2ok
def v381 : Closed T 9 := rotateClosed n126 auto3 auto3ok
def v382 : Closed T 9 := rotateClosed n126 auto6 auto6ok
def v383 : Closed T 9 := rotateClosed n318 auto2 auto2ok
def v384 : Closed T 9 := rotateClosed n318 auto3 auto3ok
def v385 : Closed T 9 := rotateClosed n318 auto6 auto6ok
def v386 : Closed T 9 := rotateClosed n318 auto8 auto8ok
def v387 : Closed T 9 := rotateClosed n318 auto10 auto10ok
def v388 : Closed T 9 := rotateClosed n318 auto11 auto11ok
def v389 : Closed T 9 := rotateClosed n318 auto14 auto14ok
def v390 : Closed T 9 := rotateClosed n377 auto2 auto2ok
def v391 : Closed T 9 := rotateClosed n377 auto3 auto3ok
def v392 : Closed T 9 := rotateClosed n377 auto6 auto6ok
def v393 : Closed T 9 := rotateClosed n341 auto1 auto1ok
def v394 : Closed T 9 := rotateClosed n341 auto2 auto2ok
def v395 : Closed T 9 := rotateClosed n341 auto3 auto3ok
def v396 : Closed T 9 := rotateClosed n341 auto4 auto4ok
def v397 : Closed T 9 := rotateClosed n341 auto5 auto5ok
def v398 : Closed T 9 := rotateClosed n341 auto6 auto6ok
def v399 : Closed T 9 := rotateClosed n341 auto7 auto7ok
def v400 : Closed T 9 := rotateClosed n28 auto8 auto8ok
def v401 : Closed T 9 := rotateClosed n18 auto8 auto8ok
def v402 : Closed T 9 := rotateClosed n26 auto8 auto8ok
def v403 : Closed T 9 := rotateClosed n322 auto2 auto2ok
def v404 : Closed T 9 := rotateClosed n322 auto3 auto3ok
def v405 : Closed T 9 := rotateClosed n322 auto6 auto6ok
def v406 : Closed T 9 := rotateClosed n322 auto8 auto8ok
def v407 : Closed T 9 := rotateClosed n322 auto10 auto10ok
def v408 : Closed T 9 := rotateClosed n322 auto11 auto11ok
def v409 : Closed T 9 := rotateClosed n322 auto14 auto14ok
def v410 : Closed T 9 := rotateClosed n152 auto2 auto2ok
def v411 : Closed T 9 := rotateClosed n152 auto3 auto3ok
def v412 : Closed T 9 := rotateClosed n152 auto6 auto6ok
def v413 : Closed T 9 := rotateClosed n147 auto2 auto2ok
def v414 : Closed T 9 := rotateClosed n147 auto3 auto3ok
def v415 : Closed T 9 := rotateClosed n147 auto6 auto6ok
def v416 : Closed T 9 := rotateClosed n93 auto2 auto2ok
def v417 : Closed T 9 := rotateClosed n93 auto3 auto3ok
def v418 : Closed T 9 := rotateClosed n93 auto6 auto6ok
def v419 : Closed T 9 := rotateClosed n66 auto2 auto2ok
def v420 : Closed T 9 := rotateClosed n66 auto3 auto3ok
def v421 : Closed T 9 := rotateClosed n66 auto6 auto6ok
def v422 : Closed T 9 := rotateClosed n309 auto2 auto2ok
def v423 : Closed T 9 := rotateClosed n309 auto3 auto3ok
def v424 : Closed T 9 := rotateClosed n309 auto6 auto6ok
def v425 : Closed T 9 := rotateClosed n309 auto8 auto8ok
def v426 : Closed T 9 := rotateClosed n309 auto10 auto10ok
def v427 : Closed T 9 := rotateClosed n309 auto11 auto11ok
def v428 : Closed T 9 := rotateClosed n309 auto14 auto14ok
def v429 : Closed T 9 := rotateClosed n327 auto1 auto1ok
def v430 : Closed T 9 := rotateClosed n327 auto4 auto4ok
def v431 : Closed T 9 := rotateClosed n327 auto5 auto5ok
def v432 : Closed T 9 := rotateClosed n368 auto2 auto2ok
def v433 : Closed T 9 := rotateClosed n116 auto2 auto2ok
def v434 : Closed T 9 := rotateClosed n116 auto3 auto3ok
def v435 : Closed T 9 := rotateClosed n116 auto6 auto6ok
def v436 : Closed T 9 := rotateClosed n315 auto2 auto2ok
def v437 : Closed T 9 := rotateClosed n315 auto3 auto3ok
def v438 : Closed T 9 := rotateClosed n315 auto6 auto6ok
def v439 : Closed T 9 := rotateClosed n315 auto8 auto8ok
def v440 : Closed T 9 := rotateClosed n315 auto10 auto10ok
def v441 : Closed T 9 := rotateClosed n315 auto11 auto11ok
def v442 : Closed T 9 := rotateClosed n315 auto14 auto14ok
def v443 : Closed T 9 := rotateClosed n334 auto1 auto1ok
def v444 : Closed T 9 := rotateClosed n334 auto4 auto4ok
def v445 : Closed T 9 := rotateClosed n334 auto5 auto5ok
def v446 : Closed T 9 := rotateClosed n372 auto2 auto2ok
def v447 : Closed T 9 := rotateClosed n296 auto8 auto8ok
def n378 := cc 10 [w6,w0,w1,w2,w3,w4,w5] [q14,q103,q171] [n126,v380,v381,v382,n318,v383,v384,v385,v386,v387,v388,v389,n377,v390,v391,v392,n341,v393,v394,v395,v396,v397,v398,v399,n28,v400,n18,v401,n26,v402,n322,v403,v404,v405,v406,v407,v408,v409,n152,v410,v411,v412,n147,v413,v414,v415,n93,v416,v417,v418,n66,v419,v420,v421,n309,v422,v423,v424,v425,v426,v427,v428,n304,n327,v429,v430,v431,n368,v432,n116,v433,v434,v435,n315,v436,v437,v438,v439,v440,v441,v442,n334,v443,v444,v445,n372,v446,n296,v447,n279] (by decide +kernel)
def n379 := cc 8 [w7,w8,w10,w2,w3,w4,w5] [q262,q265,q271] [n7] (by decide +kernel)
def n380 := cc 9 [w7,w0,w10,w2,w3,w4,w5] [q4,q14,q260,q262,q265,q271] [n17,n379,n15,n11,n2,n13,n9,n21] (by decide +kernel)
def n381 := cc 9 [w7,w0,w1,w10,w2,w3,w4,w5] [q0,q262,q271,q272] [n25,v1,n379,n11,n27,v2] (by decide +kernel)
def n382 := cc 8 [w190,w0,w1,w2,w3,w4,w5] [q6,q207,q250,q262] [] (by decide +kernel)
def n383 := cc 7 [w162,w0,w10,w2,w3,w4] [q6,q195,q243,q262] [] (by decide +kernel)
def v448 : Closed T 7 := rotateClosed n383 auto14 auto14ok
def n384 := cc 8 [w85,w1,w10,w154,w3,w4,w5] [q0,q46,q130,q262] [v448] (by decide +kernel)
def n385 := cc 8 [w85,w0,w1,w133,w2,w3,w4,w5] [q2,q10,q46,q262,q265] [] (by decide +kernel)
def v449 : Closed T 8 := rotateClosed n382 auto14 auto14ok
def v450 : Closed T 8 := rotateClosed n385 auto1 auto1ok
def n386 := cc 9 [w85,w0,w1,w10,w2,w3,w4,w5] [q46,q130,q262,q265,q271] [v449,n290,n385,v450,n384] (by decide +kernel)
def n387 := cc 8 [w192,w1,w10,w2,w3,w4,w5] [q6,q7,q46,q130,q262] [n3] (by decide +kernel)
def n388 := cc 8 [w192,w0,w1,w10,w2,w3,w4,w5] [q0,q6,q7,q46,q130] [] (by decide +kernel)
def n389 := cc 8 [w193,w0,w10,w2,w3,w4,w5] [q7,q46,q130,q262] [n3] (by decide +kernel)
def n390 := cc 7 [w0,w1,w60,w194,w3,w4] [q46,q130,q262] [] (by decide +kernel)
def n391 := cc 8 [w0,w1,w60,w154,w3,w4,w5] [q7,q46,q130,q262,q271] [n390] (by decide +kernel)
def n392 := cc 8 [w0,w1,w159,w2,w3,w4,w5] [q0,q7,q46,q130,q262] [] (by decide +kernel)
def n393 := cc 8 [w129,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q130,q163] [] (by decide +kernel)
def v451 : Closed T 7 := rotateClosed n390 auto6 auto6ok
def n394 := cc 8 [w0,w1,w10,w153,w3,w4,w5] [q6,q13,q195,q243,q262] [n291,v451] (by decide +kernel)
def n395 := cc 8 [w155,w0,w1,w10,w2,w3,w4] [q0,q7,q46,q130,q195] [n292] (by decide +kernel)
def v452 : Closed T 8 := rotateClosed n388 auto8 auto8ok
def v453 : Closed T 8 := rotateClosed n387 auto8 auto8ok
def v454 : Closed T 8 := rotateClosed n394 auto6 auto6ok
def n396 := cc 9 [w0,w1,w10,w2,w154,w3,w4,w5] [q0,q7,q46,q130,q262,q271] [n395,n393,n389,n293,n384,v452,v453,n391,n392,v454] (by decide +kernel)
def n397 := cc 8 [w0,w1,w196,w2,w3,w4,w5] [q46,q130,q271] [] (by decide +kernel)
def v455 : Closed T 8 := rotateClosed n397 auto14 auto14ok
def n398 := cc 9 [w86,w0,w1,w10,w2,w3,w4,w5] [q0,q13,q195,q243,q262] [n294,v455] (by decide +kernel)
def n399 := cc 7 [w0,w198,w60,w3,w4,w5] [q163,q260] [] (by decide +kernel)
def n400 := cc 8 [w0,w198,w10,w2,w3,w4,w5] [q14,q260,q262] [n3,n399] (by decide +kernel)
def n401 := cc 8 [w65,w1,w10,w2,w3,w4,w5] [q262,q272] [n3] (by decide +kernel)
def n402 := cc 8 [w86,w166,w1,w10,w2,w3,w4] [] [] (by decide +kernel)
def v456 : Closed T 7 := rotateClosed n399 auto8 auto8ok
def n403 := cc 8 [w156,w0,w1,w60,w3,w4,w5] [q14,q262,q272] [v456] (by decide +kernel)
def v457 : Closed T 8 := rotateClosed n402 auto14 auto14ok
def v458 : Closed T 8 := rotateClosed n401 auto6 auto6ok
def v459 : Closed T 8 := rotateClosed n400 auto8 auto8ok
def n404 := cc 9 [w156,w0,w1,w10,w2,w3,w4,w5] [q14,q262,q272] [v457,n393,n22,n295,n403,v458,v459] (by decide +kernel)
def n405 := cc 8 [w129,w0,w1,w60,w3,w4,w5] [q14,q262,q265,q271] [n399,v456] (by decide +kernel)
def n406 := cc 8 [w0,w1,w199,w2,w3,w4,w5] [q46,q168,q262] [] (by decide +kernel)
def n407 := cc 8 [w201,w0,w1,w2,w3,w4,w5] [q49,q130,q143,q262,q265] [] (by decide +kernel)
def n408 := cc 7 [w0,w203,w2,w3,w4,w5] [q0,q27,q114,q179] [] (by decide +kernel)
def n409 := cc 7 [w205,w0,w1,w3,w4,w5] [q168,q262] [] (by decide +kernel)
def v460 : Closed T 7 := rotateClosed n409 auto2 auto2ok
def v461 : Closed T 7 := rotateClosed n409 auto3 auto3ok
def v462 : Closed T 7 := rotateClosed n408 auto8 auto8ok
def n410 := cc 8 [w0,w1,w202,w2,w3,w4,w5] [q14,q103,q169,q262,q271,q276] [v460,v461,n408,v462] (by decide +kernel)
def n411 := cc 8 [w207,w0,w1,w2,w3,w4,w5] [q166,q262,q271,q276] [] (by decide +kernel)
def n412 := cc 8 [w0,w1,w60,w104,w3,w4,w5] [q46,q262,q265] [] (by decide +kernel)
def n413 := cc 7 [w0,w1,w60,w208,w3,w4] [q46,q130,q262] [] (by decide +kernel)
def v463 : Closed T 7 := rotateClosed n413 auto7 auto7ok
def n414 := cc 8 [w74,w0,w1,w206,w2,w3,w4] [q6,q13,q243,q276] [v463] (by decide +kernel)
def n415 := cc 7 [w0,w60,w209,w3,w4,w5] [q271,q272] [] (by decide +kernel)
def v464 : Closed T 7 := rotateClosed n415 auto8 auto8ok
def n416 := cc 8 [w0,w1,w60,w42,w3,w4,w5] [q130,q171,q262,q265,q271,q276] [n415,v464] (by decide +kernel)
def n417 := cc 8 [w43,w0,w1,w206,w2,w3,w4] [q6,q13,q166,q195,q243] [] (by decide +kernel)
def n418 := cc 7 [w0,w1,w2,w210,w3,w4,w5] [q52,q63,q68,q275] [] (by decide +kernel)
def v465 : Closed T 7 := rotateClosed n418 auto2 auto2ok
def n419 := cc 8 [w0,w1,w60,w2,w41,w3,w4,w5] [q14,q103,q265,q272,q276] [v465] (by decide +kernel)
def v466 : Closed T 8 := rotateClosed n417 auto6 auto6ok
def v467 : Closed T 8 := rotateClosed n414 auto6 auto6ok
def v468 : Closed T 8 := rotateClosed n414 auto7 auto7ok
def v469 : Closed T 8 := rotateClosed n411 auto6 auto6ok
def v470 : Closed T 8 := rotateClosed n407 auto4 auto4ok
def v471 : Closed T 8 := rotateClosed n407 auto5 auto5ok
def v472 : Closed T 8 := rotateClosed n403 auto8 auto8ok
def v473 : Closed T 8 := rotateClosed n385 auto2 auto2ok
def v474 : Closed T 8 := rotateClosed n385 auto3 auto3ok
def v475 : Closed T 8 := rotateClosed n385 auto10 auto10ok
def v476 : Closed T 8 := rotateClosed n385 auto11 auto11ok
def v477 : Closed T 8 := rotateClosed n406 auto1 auto1ok
def v478 : Closed T 8 := rotateClosed n412 auto1 auto1ok
def v479 : Closed T 8 := rotateClosed n391 auto8 auto8ok
def v480 : Closed T 8 := rotateClosed n392 auto8 auto8ok
def n420 := cc 9 [w0,w1,w60,w2,w3,w4,w5] [q14,q130,q171,q262,q271,q276,q277] [v466,v467,v468,n405,n393,v469,v470,v471,n22,v101,n403,v472,n301,v473,v474,v475,v476,n406,v477,n410,n412,v478,n416,n419,n391,v479,n392,v480] (by decide +kernel)
def n421 := cc 7 [w135,w0,w1,w2,w3,w4] [q13,q195,q243,q262] [n239] (by decide +kernel)
def n422 := cc 7 [w0,w1,w60,w132,w4,w5] [q7,q46,q130,q262] [n229] (by decide +kernel)
def n423 := cc 7 [w0,w1,w60,w211,w3,w4] [q46,q130,q262] [] (by decide +kernel)
def v481 : Closed T 7 := rotateClosed n421 auto6 auto6ok
def v482 : Closed T 7 := rotateClosed n422 auto1 auto1ok
def n424 := cc 8 [w0,w1,w60,w126,w3,w4,w5] [q46,q130,q262,q271] [v481,n230,n422,v482,n423] (by decide +kernel)
def n425 := cc 8 [w0,w1,w60,w133,w2,w3,w4,w5] [q46,q262,q265,q269] [n231] (by decide +kernel)
def v483 : Closed T 8 := rotateClosed n425 auto1 auto1ok
def n426 := cc 9 [w0,w1,w60,w10,w2,w3,w4,w5] [q46,q130,q262,q265,q271] [n405,n232,n425,v483,n424] (by decide +kernel)
def v484 : Closed T 7 := rotateClosed n422 auto2 auto2ok
def n427 := cc 8 [w0,w1,w10,w122,w3,w4,w5] [q10,q72,q262,q265] [n234,v484] (by decide +kernel)
def n428 := cc 8 [w123,w0,w1,w10,w2,w3,w4] [q2,q10,q46,q243] [n235] (by decide +kernel)
def v485 : Closed T 7 := rotateClosed n423 auto6 auto6ok
def n429 := cc 8 [w0,w1,w10,w125,w3,w4,w5] [q6,q13,q195,q243,q262] [n236,v485] (by decide +kernel)
def n430 := cc 8 [w127,w0,w1,w10,w2,w3,w4] [q0,q7,q46,q130,q195] [n237] (by decide +kernel)
def v486 : Closed T 8 := rotateClosed n428 auto2 auto2ok
def v487 : Closed T 8 := rotateClosed n428 auto3 auto3ok
def v488 : Closed T 8 := rotateClosed n389 auto8 auto8ok
def v489 : Closed T 8 := rotateClosed n427 auto2 auto2ok
def v490 : Closed T 8 := rotateClosed n427 auto3 auto3ok
def v491 : Closed T 8 := rotateClosed n429 auto6 auto6ok
def n431 := cc 9 [w0,w1,w10,w2,w126,w3,w4,w5] [q46,q130,q262,q271] [n430,v486,v487,n393,n389,v488,n238,n424,v489,v490,v491] (by decide +kernel)
def n432 := cc 8 [w0,w1,w60,w2,w3,w4,w5] [q0,q7,q46,q130,q163] [] (by decide +kernel)
def n433 := cc 8 [w128,w134,w0,w1,w2,w3,w4] [q6,q13,q195,q243,q262] [n241,n421] (by decide +kernel)
def v492 : Closed T 8 := rotateClosed n432 auto6 auto6ok
def n434 := cc 9 [w128,w0,w1,w10,w2,w3,w4,w5] [q6,q13,q195,q243,q262] [n433,n242,v492] (by decide +kernel)
def n435 := cc 7 [w212,w198,w2,w3,w4,w5] [q0,q7,q78,q147] [] (by decide +kernel)
def n436 := cc 8 [w129,w0,w198,w2,w3,w4,w5] [q14,q163,q260] [n399,n435] (by decide +kernel)
def n437 := cc 8 [w0,w212,w1,w2,w3,w4,w5] [q7,q88,q153,q262] [] (by decide +kernel)
def n438 := cc 8 [w213,w0,w1,w2,w3,w4,w5] [q72,q168,q262] [] (by decide +kernel)
def n439 := cc 8 [w0,w1,w215,w2,w3,w4,w5] [q54,q130,q262,q265] [] (by decide +kernel)
def n440 := cc 8 [w216,w0,w1,w2,w3,w4,w5] [q265,q271] [] (by decide +kernel)
def n441 := cc 8 [w0,w1,w217,w2,w3,w4,w5] [q55,q134,q166,q262,q265] [] (by decide +kernel)
def v493 : Closed T 8 := rotateClosed n438 auto1 auto1ok
def v494 : Closed T 8 := rotateClosed n436 auto8 auto8ok
def v495 : Closed T 8 := rotateClosed n437 auto8 auto8ok
def v496 : Closed T 8 := rotateClosed n441 auto6 auto6ok
def v497 : Closed T 8 := rotateClosed n439 auto4 auto4ok
def v498 : Closed T 8 := rotateClosed n439 auto5 auto5ok
def n442 := cc 9 [w129,w0,w1,w2,w3,w4,w5] [q46,q130,q163,q171,q265,q271] [n438,v493,n440,n303,n405,n436,v494,n437,v495,n432,v496,v497,v498] (by decide +kernel)
def v499 : Closed T 8 := rotateClosed n433 auto6 auto6ok
def n443 := cc 9 [w129,w0,w1,w10,w2,w3,w4,w5] [q14,q265,q271] [v499,n245,n405,n400,v459] (by decide +kernel)
def n444 := cc 7 [w0,w1,w130,w104,w4,w5] [q0,q7,q46,q130,q195] [n246] (by decide +kernel)
def n445 := cc 7 [w138,w0,w1,w10,w2,w3] [q4,q11,q130,q195,q243] [n247] (by decide +kernel)
def v500 : Closed T 7 := rotateClosed n445 auto5 auto5ok
def n446 := cc 8 [w0,w1,w10,w104,w71,w4,w5] [q0,q7,q130,q262] [v500,n248,n444] (by decide +kernel)
def v501 : Closed T 8 := rotateClosed n412 auto2 auto2ok
def n447 := cc 9 [w0,w1,w10,w104,w2,w3,w4,w5] [q46,q72,q262,q265,q269] [n438,n249,n406,n412,v501,n446] (by decide +kernel)
def n448 := cc 8 [w178,w0,w1,w10,w2,w3,w4,w5] [q0,q7,q130,q195] [] (by decide +kernel)
def n449 := cc 8 [w0,w1,w130,w2,w3,w4,w5] [q0,q7,q46,q130,q195] [n250,n444] (by decide +kernel)
def n450 := cc 8 [w0,w1,w130,w10,w2,w3,w4,w5] [q0,q7,q46,q130,q262] [n251] (by decide +kernel)
def n451 := cc 8 [w139,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q130,q195] [n253] (by decide +kernel)
def v502 : Closed T 8 := rotateClosed n448 auto8 auto8ok
def n452 := cc 9 [w0,w1,w10,w2,w3,w71,w4,w5] [q0,q7,q130,q195,q262,q271] [n451,n254,n448,v502,n450,n449,n446] (by decide +kernel)
def n453 := cc 8 [w0,w1,w218,w2,w3,w4,w5] [q6,q195,q243,q262] [] (by decide +kernel)
def n454 := cc 8 [w0,w1,w219,w2,w3,w4,w5] [q0,q46,q130,q245,q262] [] (by decide +kernel)
def n455 := cc 8 [w0,w1,w10,w2,w3,w4,w111] [q0,q7,q130,q195] [n255] (by decide +kernel)
def v503 : Closed T 7 := rotateClosed n413 auto6 auto6ok
def n456 := cc 8 [w0,w1,w10,w113,w3,w4,w5] [q6,q13,q195,q243,q262] [n256,v503] (by decide +kernel)
def v504 : Closed T 7 := rotateClosed n445 auto1 auto1ok
def n457 := cc 8 [w74,w114,w0,w1,w10,w2,w4] [q2,q10,q46,q195,q243] [n257,v504] (by decide +kernel)
def v505 : Closed T 8 := rotateClosed n454 auto7 auto7ok
def v506 : Closed T 8 := rotateClosed n456 auto1 auto1ok
def v507 : Closed T 8 := rotateClosed n455 auto6 auto6ok
def n458 := cc 9 [w74,w0,w1,w10,w2,w3,w4,w5] [q46,q163,q195,q262,q265,q272] [n457,n258,n414,v505,v506,v507,n453] (by decide +kernel)
def n459 := cc 7 [w220,w10,w2,w3,w4,w5] [q2,q262] [] (by decide +kernel)
def v508 : Closed T 7 := rotateClosed n415 auto6 auto6ok
def n460 := cc 8 [w0,w10,w2,w209,w3,w4,w5] [q262,q271,q272] [n459,n415,v508,n408] (by decide +kernel)
def n461 := cc 6 [w221,w222,w10,w2,w3,w4,w5] [q0] [] (by decide +kernel)
def n462 := cc 6 [w221,w223,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def n463 := cc 7 [w221,w1,w10,w42,w2,w3,w4,w5] [q0,q265,q272] [n461,n462] (by decide +kernel)
def n464 := cc 8 [w221,w1,w10,w2,w3,w4,w5] [q0,q6,q265,q272] [n269,n463] (by decide +kernel)
def n465 := cc 7 [w0,w1,w225,w3,w4,w5] [q262,q265] [] (by decide +kernel)
def v509 : Closed T 7 := rotateClosed n465 auto2 auto2ok
def v510 : Closed T 7 := rotateClosed n465 auto3 auto3ok
def n466 := cc 8 [w0,w1,w2,w226,w3,w4,w5] [q14,q103,q171,q262,q265,q271] [v509,v510] (by decide +kernel)
def n467 := cc 6 [w228,w0,w1,w2,w3,w4,w5] [] [] (by decide +kernel)
def v511 : Closed T 6 := rotateClosed n462 auto2 auto2ok
def v512 : Closed T 6 := rotateClosed n462 auto10 auto10ok
def n468 := cc 7 [w227,w0,w1,w42,w2,w3,w4,w5] [q53,q163,q166,q265,q272] [n467,v511,v512] (by decide +kernel)
def n469 := cc 8 [w227,w0,w1,w2,w3,w4,w5] [q53,q163,q166,q199,q265,q272] [n468] (by decide +kernel)
def n470 := cc 7 [w0,w1,w229,w2,w41,w5] [q46,q195,q265] [] (by decide +kernel)
def n471 := cc 7 [w116,w0,w1,w10,w2,w5] [q2,q10,q46,q195,q265] [n270] (by decide +kernel)
def v513 : Closed T 7 := rotateClosed n471 auto2 auto2ok
def v514 : Closed T 7 := rotateClosed n470 auto2 auto2ok
def n472 := cc 8 [w0,w1,w10,w42,w3,w4,w82] [q0,q7,q46,q130,q262] [v513,n271,v514] (by decide +kernel)
def n473 := cc 6 [w0,w1,w151,w2,w3,w4,w5] [q0,q7,q103,q171] [n272] (by decide +kernel)
def n474 := cc 7 [w0,w1,w10,w2,w3,w117,w4,w5] [q0,q7,q262,q271] [n467,n273,n473] (by decide +kernel)
def v515 : Closed T 7 := rotateClosed n463 auto2 auto2ok
def v516 : Closed T 7 := rotateClosed n463 auto8 auto8ok
def v517 : Closed T 7 := rotateClosed n463 auto10 auto10ok
def v518 : Closed T 7 := rotateClosed n468 auto2 auto2ok
def n475 := cc 8 [w0,w1,w10,w42,w2,w41,w3,w4,w5] [q46,q130,q195,q262,q265,q271,q272,q275,q276] [n463,v515,v516,v517,n468,v518,n274,n474] (by decide +kernel)
def v519 : Closed T 8 := rotateClosed n464 auto2 auto2ok
def v520 : Closed T 8 := rotateClosed n464 auto10 auto10ok
def v521 : Closed T 8 := rotateClosed n469 auto2 auto2ok
def v522 : Closed T 8 := rotateClosed n416 auto6 auto6ok
def v523 : Closed T 8 := rotateClosed n419 auto2 auto2ok
def v524 : Closed T 8 := rotateClosed n419 auto3 auto3ok
def v525 : Closed T 8 := rotateClosed n460 auto8 auto8ok
def n476 := cc 9 [w0,w1,w10,w42,w2,w3,w4,w5] [q14,q46,q130,q171,q195,q243,q262,q265,q271] [v519,v520,v521,n440,n275,n410,n416,v522,v523,v524,n475,n472,n466,n460,v525] (by decide +kernel)
def n477 := cc 8 [w0,w1,w229,w2,w3,w4,w5] [q2,q10,q46,q130,q195] [n470] (by decide +kernel)
def n478 := cc 8 [w230,w0,w1,w2,w3,w4,w5] [q2,q10,q46,q130,q195] [] (by decide +kernel)
def v526 : Closed T 8 := rotateClosed n472 auto2 auto2ok
def n479 := cc 9 [w0,w1,w10,w2,w3,w4,w79,w5] [q2,q10,q46,q195,q265] [n478,n276,n477,v526] (by decide +kernel)
def n480 := cc 8 [w0,w1,w231,w2,w3,w4,w5] [q6,q13,q166,q195,q243] [] (by decide +kernel)
def n481 := cc 8 [w0,w1,w232,w2,w3,w4,w5] [q0,q7,q46,q130,q163] [] (by decide +kernel)
def n482 := cc 8 [w43,w119,w0,w1,w10,w3,w4] [q0,q7,q46,q130,q195] [n277,v513] (by decide +kernel)
def v527 : Closed T 8 := rotateClosed n481 auto6 auto6ok
def n483 := cc 9 [w43,w0,w1,w10,w2,w3,w4,w5] [q195,q243,q262,q271] [n482,n278,n417,v527,n480] (by decide +kernel)
def v528 : Closed T 9 := rotateClosed n398 auto2 auto2ok
def v529 : Closed T 9 := rotateClosed n398 auto3 auto3ok
def v530 : Closed T 9 := rotateClosed n398 auto6 auto6ok
def v531 : Closed T 9 := rotateClosed n398 auto8 auto8ok
def v532 : Closed T 9 := rotateClosed n398 auto10 auto10ok
def v533 : Closed T 9 := rotateClosed n398 auto11 auto11ok
def v534 : Closed T 9 := rotateClosed n398 auto14 auto14ok
def v535 : Closed T 9 := rotateClosed n434 auto2 auto2ok
def v536 : Closed T 9 := rotateClosed n434 auto3 auto3ok
def v537 : Closed T 9 := rotateClosed n434 auto6 auto6ok
def v538 : Closed T 9 := rotateClosed n483 auto2 auto2ok
def v539 : Closed T 9 := rotateClosed n483 auto3 auto3ok
def v540 : Closed T 9 := rotateClosed n483 auto6 auto6ok
def v541 : Closed T 9 := rotateClosed n458 auto1 auto1ok
def v542 : Closed T 9 := rotateClosed n458 auto2 auto2ok
def v543 : Closed T 9 := rotateClosed n458 auto3 auto3ok
def v544 : Closed T 9 := rotateClosed n458 auto4 auto4ok
def v545 : Closed T 9 := rotateClosed n458 auto5 auto5ok
def v546 : Closed T 9 := rotateClosed n458 auto6 auto6ok
def v547 : Closed T 9 := rotateClosed n458 auto7 auto7ok
def v548 : Closed T 9 := rotateClosed n443 auto2 auto2ok
def v549 : Closed T 9 := rotateClosed n443 auto3 auto3ok
def v550 : Closed T 9 := rotateClosed n443 auto6 auto6ok
def v551 : Closed T 9 := rotateClosed n442 auto2 auto2ok
def v552 : Closed T 9 := rotateClosed n442 auto3 auto3ok
def v553 : Closed T 9 := rotateClosed n442 auto6 auto6ok
def v554 : Closed T 9 := rotateClosed n381 auto8 auto8ok
def v555 : Closed T 9 := rotateClosed n380 auto8 auto8ok
def v556 : Closed T 9 := rotateClosed n404 auto2 auto2ok
def v557 : Closed T 9 := rotateClosed n404 auto3 auto3ok
def v558 : Closed T 9 := rotateClosed n404 auto6 auto6ok
def v559 : Closed T 9 := rotateClosed n404 auto8 auto8ok
def v560 : Closed T 9 := rotateClosed n404 auto10 auto10ok
def v561 : Closed T 9 := rotateClosed n404 auto11 auto11ok
def v562 : Closed T 9 := rotateClosed n404 auto14 auto14ok
def v563 : Closed T 9 := rotateClosed n386 auto2 auto2ok
def v564 : Closed T 9 := rotateClosed n386 auto3 auto3ok
def v565 : Closed T 9 := rotateClosed n386 auto6 auto6ok
def v566 : Closed T 9 := rotateClosed n386 auto8 auto8ok
def v567 : Closed T 9 := rotateClosed n386 auto10 auto10ok
def v568 : Closed T 9 := rotateClosed n386 auto11 auto11ok
def v569 : Closed T 9 := rotateClosed n386 auto14 auto14ok
def v570 : Closed T 9 := rotateClosed n426 auto2 auto2ok
def v571 : Closed T 9 := rotateClosed n426 auto3 auto3ok
def v572 : Closed T 9 := rotateClosed n426 auto6 auto6ok
def v573 : Closed T 9 := rotateClosed n420 auto2 auto2ok
def v574 : Closed T 9 := rotateClosed n420 auto3 auto3ok
def v575 : Closed T 9 := rotateClosed n420 auto6 auto6ok
def v576 : Closed T 9 := rotateClosed n447 auto1 auto1ok
def v577 : Closed T 9 := rotateClosed n447 auto4 auto4ok
def v578 : Closed T 9 := rotateClosed n447 auto5 auto5ok
def v579 : Closed T 9 := rotateClosed n476 auto2 auto2ok
def v580 : Closed T 9 := rotateClosed n396 auto2 auto2ok
def v581 : Closed T 9 := rotateClosed n396 auto3 auto3ok
def v582 : Closed T 9 := rotateClosed n396 auto6 auto6ok
def v583 : Closed T 9 := rotateClosed n396 auto8 auto8ok
def v584 : Closed T 9 := rotateClosed n396 auto10 auto10ok
def v585 : Closed T 9 := rotateClosed n396 auto11 auto11ok
def v586 : Closed T 9 := rotateClosed n396 auto14 auto14ok
def v587 : Closed T 9 := rotateClosed n431 auto2 auto2ok
def v588 : Closed T 9 := rotateClosed n431 auto3 auto3ok
def v589 : Closed T 9 := rotateClosed n431 auto6 auto6ok
def v590 : Closed T 9 := rotateClosed n452 auto1 auto1ok
def v591 : Closed T 9 := rotateClosed n452 auto4 auto4ok
def v592 : Closed T 9 := rotateClosed n452 auto5 auto5ok
def v593 : Closed T 9 := rotateClosed n479 auto2 auto2ok
def n484 := cc 10 [w0,w1,w10,w2,w3,w4,w5] [q14,q103,q171] [n398,v528,v529,v530,v531,v532,v533,v534,n434,v535,v536,v537,n483,v538,v539,v540,n458,v541,v542,v543,v544,v545,v546,v547,n443,v548,v549,v550,n442,v551,v552,v553,n381,v554,n26,v402,n380,v555,n404,v556,v557,v558,v559,v560,v561,v562,n304,n296,v447,n279,n386,v563,v564,v565,v566,v567,v568,v569,n426,v570,v571,v572,n420,v573,v574,v575,n447,v576,v577,v578,n476,v579,n396,v580,v581,v582,v583,v584,v585,v586,n431,v587,v588,v589,n452,v590,v591,v592,n479,v593] (by decide +kernel)
def v594 : Closed T 8 := rotateClosed n2 auto8 auto8ok
def v595 : Closed T 8 := rotateClosed n37 auto2 auto2ok
def v596 : Closed T 8 := rotateClosed n37 auto3 auto3ok
def v597 : Closed T 8 := rotateClosed n37 auto6 auto6ok
def v598 : Closed T 8 := rotateClosed n117 auto2 auto2ok
def v599 : Closed T 8 := rotateClosed n117 auto3 auto3ok
def v600 : Closed T 8 := rotateClosed n375 auto2 auto2ok
def n485 := cc 9 [w6,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q10,q11,q13,q15,q104,q172,q226] [n19,v309,n2,v594,n37,v595,v596,v597,n117,v598,v599,v85,n27,n375,v600,n13,v2,n9] (by decide +kernel)
def v601 : Closed T 8 := rotateClosed n393 auto2 auto2ok
def v602 : Closed T 8 := rotateClosed n393 auto3 auto3ok
def v603 : Closed T 8 := rotateClosed n393 auto6 auto6ok
def v604 : Closed T 8 := rotateClosed n20 auto8 auto8ok
def v605 : Closed T 8 := rotateClosed n432 auto2 auto2ok
def v606 : Closed T 8 := rotateClosed n432 auto3 auto3ok
def n486 := cc 9 [w0,w1,w10,w2,w3,w4,w5] [q46,q243,q262,q265,q271] [n393,v601,v602,v603,n2,v594,n20,v604,n27,n13,v2,n9,n432,v605,v606,v492] (by decide +kernel)
def n487 := cc 7 [w65,w234,w2,w3,w4,w5] [q0,q175,q228] [] (by decide +kernel)
def n488 := cc 7 [w65,w1,w235,w2,w3,w4] [q0,q2,q4,q6] [] (by decide +kernel)
def v607 : Closed T 7 := rotateClosed n488 auto6 auto6ok
def v608 : Closed T 7 := rotateClosed n487 auto6 auto6ok
def n489 := cc 8 [w11,w236,w1,w2,w3,w4,w5] [q0,q2,q4,q7,q14] [v607,v608] (by decide +kernel)
def n490 := cc 7 [w0,w237,w157,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n491 := cc 8 [w11,w0,w157,w2,w3,w4,w5] [q0,q2,q4,q6,q46] [v608,n490] (by decide +kernel)
def n492 := cc 8 [w11,w0,w1,w237,w3,w4,w5] [q2,q14,q271] [v607,n490] (by decide +kernel)
def n493 := cc 8 [w238,w0,w1,w2,w3,w4,w5] [q4,q6,q46,q72] [] (by decide +kernel)
def n494 := cc 8 [w0,w240,w1,w2,w3,w4,w5] [q7,q153,q262] [] (by decide +kernel)
def n495 := cc 7 [w0,w243,w1,w3,w4,w5] [q7,q10,q11,q13] [] (by decide +kernel)
def v609 : Closed T 7 := rotateClosed n495 auto10 auto10ok
def v610 : Closed T 7 := rotateClosed n495 auto11 auto11ok
def n496 := cc 8 [w244,w0,w1,w2,w3,w4,w5] [q2,q4,q14,q103,q271] [v609,v610,n408] (by decide +kernel)
def n497 := cc 8 [w0,w246,w1,w2,w3,w4,w5] [q7,q262,q265] [] (by decide +kernel)
def v611 : Closed T 8 := rotateClosed n493 auto1 auto1ok
def v612 : Closed T 8 := rotateClosed n497 auto14 auto14ok
def v613 : Closed T 8 := rotateClosed n494 auto12 auto12ok
def v614 : Closed T 8 := rotateClosed n494 auto13 auto13ok
def n498 := cc 9 [w11,w0,w1,w2,w3,w4,w5] [q6,q72,q103,q171,q262,q272] [n493,v611,n496,n489,n492,n491,v108,v6,v612,v613,v614,v480] (by decide +kernel)
def n499 := cc 8 [w7,w65,w1,w2,w3,w4,w5] [q0,q2,q6,q13,q14] [n1,n488] (by decide +kernel)
def n500 := cc 8 [w7,w0,w157,w2,w3,w4,w5] [q2,q14,q271] [n1,n490] (by decide +kernel)
def n501 := cc 7 [w0,w249,w1,w3,w4,w5] [q7,q13,q88,q153] [] (by decide +kernel)
def n502 := cc 6 [w250,w248,w3,w4,w5] [q0,q10,q11,q13] [] (by decide +kernel)
def n503 := cc 6 [w7,w249,w3,w4,w5] [] [] (by decide +kernel)
def v615 : Closed T 6 := rotateClosed n503 auto8 auto8ok
def v616 : Closed T 6 := rotateClosed n502 auto8 auto8ok
def n504 := cc 7 [w11,w8,w251,w3,w4,w5] [q6,q7,q78] [v615,v616] (by decide +kernel)
def v617 : Closed T 7 := rotateClosed n501 auto8 auto8ok
def n505 := cc 8 [w11,w0,w1,w251,w3,w4,w5] [q0,q6,q7,q46,q72,q143] [n504,v617] (by decide +kernel)
def n506 := cc 7 [w7,w252,w2,w3,w4,w5] [q2,q262] [v616,n0] (by decide +kernel)
def n507 := cc 7 [w11,w9,w2,w3,w4,w5] [q0,q2,q4,q6,q7] [] (by decide +kernel)
def n508 := cc 8 [w11,w7,w8,w2,w3,w4,w5] [q2,q4,q262] [n504,n507,n506] (by decide +kernel)
def v618 : Closed T 8 := rotateClosed n499 auto6 auto6ok
def n509 := cc 9 [w11,w7,w0,w1,w2,w3,w4,w5] [q2,q4,q14,q271] [n508,n492,n505,v618,n500] (by decide +kernel)
def n510 := cc 7 [w9,w2,w251,w3,w4,w5] [q260,q261,q271] [] (by decide +kernel)
def n511 := cc 8 [w7,w8,w2,w251,w3,w4,w5] [q7,q78,q271] [n504,n510] (by decide +kernel)
def n512 := cc 9 [w7,w0,w1,w2,w251,w3,w4,w5] [q0,q72,q143,q271] [n505,n511,v6] (by decide +kernel)
def n513 := cc 8 [w7,w192,w1,w2,w3,w4,w5] [q0,q6,q7,q46,q72,q143] [n1] (by decide +kernel)
def n514 := cc 8 [w7,w0,w165,w2,w3,w4,w5] [q0,q13,q207,q250] [n1] (by decide +kernel)
def n515 := cc 6 [w9,w2,w3,w4,w254] [q0,q2,q4,q6] [] (by decide +kernel)
def n516 := cc 7 [w7,w8,w2,w3,w4,w254] [q0,q7,q78,q147,q209] [n515] (by decide +kernel)
def n517 := cc 8 [w7,w0,w1,w2,w3,w4,w254] [q0,q7,q46,q143,q207] [n516] (by decide +kernel)
def n518 := cc 7 [w0,w12,w1,w256,w3,w4] [q7,q13,q88,q153] [] (by decide +kernel)
def n519 := cc 6 [w9,w258,w3,w4,w5] [q6,q7,q10,q11] [] (by decide +kernel)
def n520 := cc 7 [w7,w8,w258,w3,w4,w5] [q6,q7,q209] [n519] (by decide +kernel)
def v619 : Closed T 7 := rotateClosed n520 auto8 auto8ok
def v620 : Closed T 7 := rotateClosed n518 auto14 auto14ok
def n521 := cc 8 [w7,w0,w1,w260,w3,w4,w5] [q0,q13,q195,q207,q250] [v619,v620] (by decide +kernel)
def n522 := cc 6 [w261,w262,w2,w3,w4] [q6,q7,q209,q251] [] (by decide +kernel)
def v621 : Closed T 6 := rotateClosed n503 auto14 auto14ok
def v622 : Closed T 6 := rotateClosed n522 auto8 auto8ok
def n523 := cc 7 [w259,w8,w235,w2,w3,w4] [q0,q6,q13,q209,q251] [v621,v622] (by decide +kernel)
def v623 : Closed T 7 := rotateClosed n501 auto14 auto14ok
def n524 := cc 8 [w259,w0,w1,w235,w2,w3,w4] [q0,q6,q13,q207,q250,q262] [n523,v620,v623] (by decide +kernel)
def n525 := cc 7 [w7,w263,w2,w3,w4,w5] [q0,q13,q209] [v622,n0] (by decide +kernel)
def v624 : Closed T 6 := rotateClosed n519 auto8 auto8ok
def v625 : Closed T 6 := rotateClosed n515 auto6 auto6ok
def n526 := cc 7 [w259,w9,w2,w3,w4,w5] [q0,q2,q4,q6,q262] [v624,v625] (by decide +kernel)
def v626 : Closed T 7 := rotateClosed n516 auto6 auto6ok
def n527 := cc 8 [w259,w7,w8,w2,w3,w4,w5] [q0,q13,q209,q251] [n523,n526,v619,v626,n525] (by decide +kernel)
def v627 : Closed T 8 := rotateClosed n513 auto6 auto6ok
def v628 : Closed T 8 := rotateClosed n517 auto6 auto6ok
def n528 := cc 9 [w259,w7,w0,w1,w2,w3,w4,w5] [q0,q207,q250,q271] [n527,n524,v5,v627,n521,v628,n514] (by decide +kernel)
def n529 := cc 7 [w0,w12,w1,w194,w3,w4] [q7,q88,q262] [] (by decide +kernel)
def n530 := cc 8 [w0,w12,w1,w154,w3,w4,w5] [q7,q88,q262] [n529] (by decide +kernel)
def n531 := cc 8 [w156,w0,w1,w237,w3,w4,w5] [q14,q262,q272] [v607] (by decide +kernel)
def n532 := cc 8 [w85,w0,w264,w1,w2,w3,w4,w5] [q262,q265,q269] [] (by decide +kernel)
def n533 := cc 8 [w0,w265,w1,w2,w3,w4,w5] [q88,q168,q262] [] (by decide +kernel)
def n534 := cc 8 [w267,w0,w1,w2,w3,w4,w5] [q4,q76,q130,q163,q265] [] (by decide +kernel)
def n535 := cc 8 [w0,w268,w1,w2,w3,w4,w5] [q13,q67,q169,q262,q269,q270,q276] [v22] (by decide +kernel)
def n536 := cc 8 [w269,w0,w1,w2,w3,w4,w5] [q166,q267,q268] [] (by decide +kernel)
def n537 := cc 8 [w85,w0,w1,w237,w3,w4,w5] [q2,q14,q271] [n490] (by decide +kernel)
def n538 := cc 8 [w86,w0,w1,w235,w2,w3,w4] [q0,q207,q250,q262] [] (by decide +kernel)
def n539 := cc 7 [w221,w1,w270,w2,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def v629 : Closed T 7 := rotateClosed n539 auto10 auto10ok
def n540 := cc 8 [w0,w12,w1,w42,w3,w4,w5] [q13,q153,q171,q262,q269,q270,q276] [v629] (by decide +kernel)
def n541 := cc 8 [w43,w0,w262,w1,w2,w3,w4] [q13,q166,q218,q256] [] (by decide +kernel)
def n542 := cc 8 [w0,w12,w1,w2,w41,w3,w4,w5] [q14,q265,q269,q276] [] (by decide +kernel)
def v630 : Closed T 8 := rotateClosed n538 auto14 auto14ok
def v631 : Closed T 8 := rotateClosed n541 auto6 auto6ok
def v632 : Closed T 8 := rotateClosed n492 auto8 auto8ok
def v633 : Closed T 8 := rotateClosed n536 auto14 auto14ok
def v634 : Closed T 8 := rotateClosed n534 auto12 auto12ok
def v635 : Closed T 8 := rotateClosed n534 auto13 auto13ok
def v636 : Closed T 8 := rotateClosed n531 auto8 auto8ok
def v637 : Closed T 8 := rotateClosed n532 auto2 auto2ok
def v638 : Closed T 8 := rotateClosed n532 auto3 auto3ok
def v639 : Closed T 8 := rotateClosed n537 auto8 auto8ok
def v640 : Closed T 8 := rotateClosed n533 auto1 auto1ok
def n543 := cc 9 [w0,w12,w1,w2,w3,w4,w5] [q14,q153,q163,q171,q262,q269,q271] [v630,v631,n393,v632,v101,v633,v634,v635,v39,v636,n117,v637,v638,v639,n533,v640,n535,n540,n542,n530,n437] (by decide +kernel)
def n544 := cc 7 [w9,w12,w2,w3,w4,w5] [q7,q10,q11,q262,q265] [] (by decide +kernel)
def n545 := cc 8 [w7,w8,w12,w2,w3,w4,w5] [q7,q265,q271] [n544] (by decide +kernel)
def v641 : Closed T 8 := rotateClosed n524 auto6 auto6ok
def v642 : Closed T 8 := rotateClosed n545 auto8 auto8ok
def n546 := cc 9 [w7,w0,w1,w237,w2,w3,w4,w5] [q143,q260,q261,q271] [v641,n492,v642] (by decide +kernel)
def v643 : Closed T 7 := rotateClosed n526 auto2 auto2ok
def v644 : Closed T 7 := rotateClosed n526 auto3 auto3ok
def v645 : Closed T 7 := rotateClosed n526 auto6 auto6ok
def v646 : Closed T 7 := rotateClosed n507 auto2 auto2ok
def v647 : Closed T 7 := rotateClosed n507 auto3 auto3ok
def v648 : Closed T 7 := rotateClosed n507 auto6 auto6ok
def v649 : Closed T 7 := rotateClosed n544 auto8 auto8ok
def v650 : Closed T 7 := rotateClosed n544 auto10 auto10ok
def v651 : Closed T 7 := rotateClosed n544 auto11 auto11ok
def v652 : Closed T 7 := rotateClosed n544 auto14 auto14ok
def v653 : Closed T 7 := rotateClosed n510 auto2 auto2ok
def v654 : Closed T 7 := rotateClosed n510 auto3 auto3ok
def v655 : Closed T 7 := rotateClosed n510 auto6 auto6ok
def n547 := cc 8 [w7,w9,w2,w3,w4,w5] [q260,q268,q271,q272] [n526,v643,v644,v645,n507,v646,v647,v648,n14,n1,v0,v649,v650,v651,v652,n510,v653,v654,v655] (by decide +kernel)
def n548 := cc 8 [w7,w8,w9,w2,w3,w4,w5] [q4,q6,q7,q10,q11,q13,q260,q262,q265,q271,q272] [] (by decide +kernel)
def n549 := cc 6 [w138,w7,w8,w2,w3] [q209,q251,q264] [] (by decide +kernel)
def v656 : Closed T 6 := rotateClosed n549 auto5 auto5ok
def n550 := cc 7 [w7,w8,w104,w71,w4,w5] [q0,q7,q78,q147,q209] [v656,n177] (by decide +kernel)
def n551 := cc 8 [w7,w8,w104,w2,w3,w4,w5] [q260,q262] [n550,n178] (by decide +kernel)
def n552 := cc 8 [w7,w8,w2,w3,w71,w4,w5] [q0,q7,q147,q209] [n550,n181] (by decide +kernel)
def n553 := cc 7 [w7,w8,w2,w3,w4,w111] [q0,q7,q147,q209] [n184] (by decide +kernel)
def n554 := cc 7 [w7,w8,w113,w3,w4,w5] [q6,q13,q209,q251] [n185] (by decide +kernel)
def v657 : Closed T 6 := rotateClosed n549 auto1 auto1ok
def n555 := cc 7 [w74,w114,w7,w8,w2,w4] [q2,q10,q78,q209,q251] [n186,v657] (by decide +kernel)
def v658 : Closed T 7 := rotateClosed n554 auto1 auto1ok
def v659 : Closed T 7 := rotateClosed n553 auto6 auto6ok
def n556 := cc 8 [w74,w7,w8,w2,w3,w4,w5] [q6,q13,q78,q251,q262] [n555,n187,v658,v659] (by decide +kernel)
def n557 := cc 6 [w116,w7,w8,w2,w5] [q2,q10,q78,q209] [n190] (by decide +kernel)
def v660 : Closed T 6 := rotateClosed n557 auto2 auto2ok
def n558 := cc 7 [w7,w8,w42,w3,w4,w82] [q0,q78,q262] [v660,n191] (by decide +kernel)
def n559 := cc 6 [w7,w8,w2,w3,w117,w4,w5] [] [n192] (by decide +kernel)
def n560 := cc 7 [w7,w8,w42,w2,w41,w3,w4,w5] [q78,q147,q209,q262,q265] [n559,n193] (by decide +kernel)
def n561 := cc 8 [w7,w8,w42,w2,w3,w4,w5] [q78,q147,q209,q251,q262,q265,q271] [n560,n558,n194] (by decide +kernel)
def v661 : Closed T 7 := rotateClosed n558 auto2 auto2ok
def n562 := cc 8 [w7,w8,w2,w3,w4,w79,w5] [q2,q10,q78,q147,q209] [v661,n195] (by decide +kernel)
def n563 := cc 7 [w43,w119,w7,w8,w3,w4] [q0,q7,q78,q147,q209] [n198,v660] (by decide +kernel)
def n564 := cc 8 [w43,w7,w8,w2,w3,w4,w5] [q6,q209,q251,q262] [n563,n199] (by decide +kernel)
def v662 : Closed T 8 := rotateClosed n527 auto2 auto2ok
def v663 : Closed T 8 := rotateClosed n527 auto3 auto3ok
def v664 : Closed T 8 := rotateClosed n527 auto6 auto6ok
def v665 : Closed T 8 := rotateClosed n527 auto8 auto8ok
def v666 : Closed T 8 := rotateClosed n527 auto10 auto10ok
def v667 : Closed T 8 := rotateClosed n527 auto11 auto11ok
def v668 : Closed T 8 := rotateClosed n527 auto14 auto14ok
def v669 : Closed T 8 := rotateClosed n564 auto2 auto2ok
def v670 : Closed T 8 := rotateClosed n564 auto3 auto3ok
def v671 : Closed T 8 := rotateClosed n564 auto6 auto6ok
def v672 : Closed T 8 := rotateClosed n556 auto1 auto1ok
def v673 : Closed T 8 := rotateClosed n556 auto2 auto2ok
def v674 : Closed T 8 := rotateClosed n556 auto3 auto3ok
def v675 : Closed T 8 := rotateClosed n556 auto4 auto4ok
def v676 : Closed T 8 := rotateClosed n556 auto5 auto5ok
def v677 : Closed T 8 := rotateClosed n556 auto6 auto6ok
def v678 : Closed T 8 := rotateClosed n556 auto7 auto7ok
def v679 : Closed T 8 := rotateClosed n508 auto2 auto2ok
def v680 : Closed T 8 := rotateClosed n508 auto3 auto3ok
def v681 : Closed T 8 := rotateClosed n508 auto6 auto6ok
def v682 : Closed T 8 := rotateClosed n508 auto8 auto8ok
def v683 : Closed T 8 := rotateClosed n508 auto10 auto10ok
def v684 : Closed T 8 := rotateClosed n508 auto11 auto11ok
def v685 : Closed T 8 := rotateClosed n508 auto14 auto14ok
def v686 : Closed T 8 := rotateClosed n545 auto2 auto2ok
def v687 : Closed T 8 := rotateClosed n545 auto3 auto3ok
def v688 : Closed T 8 := rotateClosed n545 auto6 auto6ok
def v689 : Closed T 8 := rotateClosed n545 auto10 auto10ok
def v690 : Closed T 8 := rotateClosed n545 auto11 auto11ok
def v691 : Closed T 8 := rotateClosed n545 auto14 auto14ok
def v692 : Closed T 8 := rotateClosed n551 auto1 auto1ok
def v693 : Closed T 8 := rotateClosed n551 auto4 auto4ok
def v694 : Closed T 8 := rotateClosed n551 auto5 auto5ok
def v695 : Closed T 8 := rotateClosed n561 auto2 auto2ok
def v696 : Closed T 8 := rotateClosed n511 auto2 auto2ok
def v697 : Closed T 8 := rotateClosed n511 auto3 auto3ok
def v698 : Closed T 8 := rotateClosed n511 auto6 auto6ok
def v699 : Closed T 8 := rotateClosed n511 auto8 auto8ok
def v700 : Closed T 8 := rotateClosed n511 auto10 auto10ok
def v701 : Closed T 8 := rotateClosed n511 auto11 auto11ok
def v702 : Closed T 8 := rotateClosed n511 auto14 auto14ok
def v703 : Closed T 8 := rotateClosed n552 auto1 auto1ok
def v704 : Closed T 8 := rotateClosed n552 auto4 auto4ok
def v705 : Closed T 8 := rotateClosed n552 auto5 auto5ok
def v706 : Closed T 8 := rotateClosed n562 auto2 auto2ok
def v707 : Closed T 8 := rotateClosed n547 auto8 auto8ok
def n565 := cc 9 [w7,w8,w2,w3,w4,w5] [] [n527,v662,v663,v664,v665,v666,v667,v668,n564,v669,v670,v671,n556,v672,v673,v674,v675,v676,v677,v678,n508,v679,v680,v681,v682,v683,v684,v685,n548,n545,v686,v687,v688,v642,v689,v690,v691,n551,v692,v693,v694,n561,v695,n511,v696,v697,v698,v699,v700,v701,v702,n552,v703,v704,v705,n562,v706,n547,v707,n200] (by decide +kernel)
def n566 := cc 8 [w7,w9,w0,w2,w3,w4,w5] [q0,q2,q4,q6,q262,q271] [n14,n1,n6] (by decide +kernel)
def n567 := cc 8 [w7,w9,w1,w2,w3,w4,w5] [q0,q7,q271,q272] [n14,n1,n7] (by decide +kernel)
def n568 := cc 8 [w7,w8,w9,w0,w2,w3,w4,w5] [q2,q4,q7,q262,q271] [] (by decide +kernel)
def n569 := cc 8 [w7,w8,w85,w2,w3,w4,w5] [q2,q4,q262] [n280] (by decide +kernel)
def n570 := cc 7 [w7,w8,w153,w3,w4,w5] [q6,q13,q209,q251] [n281] (by decide +kernel)
def n571 := cc 7 [w155,w7,w8,w2,w3,w4] [q0,q7,q78,q147,q209] [n282] (by decide +kernel)
def v708 : Closed T 7 := rotateClosed n570 auto6 auto6ok
def n572 := cc 8 [w7,w8,w2,w154,w3,w4,w5] [q0,q78,q147,q262] [n571,v708,n283] (by decide +kernel)
def n573 := cc 8 [w86,w7,w8,w2,w3,w4,w5] [q0,q13,q209,q251] [n284] (by decide +kernel)
def n574 := cc 8 [w7,w156,w8,w2,w3,w4,w5] [q269,q271] [n285] (by decide +kernel)
def v709 : Closed T 8 := rotateClosed n573 auto2 auto2ok
def v710 : Closed T 8 := rotateClosed n573 auto3 auto3ok
def v711 : Closed T 8 := rotateClosed n573 auto6 auto6ok
def v712 : Closed T 8 := rotateClosed n574 auto8 auto8ok
def v713 : Closed T 8 := rotateClosed n574 auto10 auto10ok
def v714 : Closed T 8 := rotateClosed n574 auto11 auto11ok
def v715 : Closed T 8 := rotateClosed n574 auto14 auto14ok
def v716 : Closed T 8 := rotateClosed n569 auto2 auto2ok
def v717 : Closed T 8 := rotateClosed n569 auto3 auto3ok
def v718 : Closed T 8 := rotateClosed n569 auto6 auto6ok
def v719 : Closed T 8 := rotateClosed n572 auto2 auto2ok
def v720 : Closed T 8 := rotateClosed n572 auto3 auto3ok
def v721 : Closed T 8 := rotateClosed n572 auto6 auto6ok
def v722 : Closed T 8 := rotateClosed n567 auto8 auto8ok
def n575 := cc 9 [w7,w8,w0,w2,w3,w4,w5] [q4,q6,q260,q262,q265] [n573,v709,v710,v711,v712,v713,v714,v715,n568,n16,n569,v716,v717,v718,n379,n572,v719,v720,v721,n566,v722,v309,n20,n286] (by decide +kernel)
def n576 := cc 8 [w7,w9,w0,w1,w2,w3,w4,w5] [q2,q4,q7,q262,q271] [n14] (by decide +kernel)
def n577 := cc 8 [w7,w8,w9,w0,w1,w2,w3,w4,w5] [q0,q7,q262,q271] [] (by decide +kernel)
def v723 : Closed T 8 := rotateClosed n576 auto8 auto8ok
def n578 := cc 9 [w7,w8,w0,w1,w2,w3,w4,w5] [q4,q6,q7,q10,q11,q13,q260,q262,q265,q271,q272] [n577,n16,n379,n576,v723,n297] (by decide +kernel)
def n579 := cc 8 [w7,w15,w0,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q262] [n1] (by decide +kernel)
def n580 := cc 7 [w7,w271,w1,w2,w3,w4] [] [] (by decide +kernel)
def v724 : Closed T 7 := rotateClosed n580 auto6 auto6ok
def n581 := cc 8 [w7,w85,w1,w154,w3,w4,w5] [q0,q6,q46,q72,q143] [v724] (by decide +kernel)
def v725 : Closed T 8 := rotateClosed n579 auto6 auto6ok
def n582 := cc 9 [w7,w85,w0,w1,w2,w3,w4,w5] [q2,q4,q14,q271] [n22,n569,v725,n581,n500,n117,n537] (by decide +kernel)
def n583 := cc 8 [w7,w1,w2,w154,w3,w4,w5,w152] [q0,q208,q271] [] (by decide +kernel)
def n584 := cc 8 [w7,w0,w272,w1,w2,w3,w4,w5] [q0,q7,q13,q46,q72,q143] [] (by decide +kernel)
def n585 := cc 8 [w7,w0,w1,w153,w3,w4,w5] [q6,q207,q250,q271] [n570] (by decide +kernel)
def n586 := cc 8 [w155,w7,w0,w1,w2,w3,w4] [q0,q7,q46,q143,q207] [n571] (by decide +kernel)
def v726 : Closed T 8 := rotateClosed n585 auto6 auto6ok
def v727 : Closed T 8 := rotateClosed n319 auto8 auto8ok
def n587 := cc 9 [w7,w0,w1,w2,w154,w3,w4,w5] [q0,q6,q7,q72,q143,q200,q262,q271] [n586,n572,n581,n584,v726,n583,v727] (by decide +kernel)
def n588 := cc 8 [w7,w0,w273,w2,w3,w4,w5] [q0,q6,q7,q46,q72,q143] [n1] (by decide +kernel)
def n589 := cc 8 [w7,w0,w273,w1,w2,w3,w4,w5] [q6,q7,q46,q72,q143] [] (by decide +kernel)
def v728 : Closed T 8 := rotateClosed n589 auto6 auto6ok
def v729 : Closed T 8 := rotateClosed n588 auto6 auto6ok
def n590 := cc 9 [w86,w7,w0,w1,w2,w3,w4,w5] [q0,q13,q195,q207,q250,q271] [n573,n538,v5,v728,v729,n514,n32] (by decide +kernel)
def n591 := cc 8 [w86,w7,w166,w1,w2,w3,w4] [] [] (by decide +kernel)
def v730 : Closed T 8 := rotateClosed n591 auto6 auto6ok
def n592 := cc 9 [w7,w197,w0,w1,w2,w3,w4,w5] [q260,q261,q271] [v730,v712,n310] (by decide +kernel)
def n593 := cc 8 [w7,w0,w1,w159,w2,w3,w4,w5] [q7,q260,q261,q262] [] (by decide +kernel)
def n594 := cc 8 [w7,w0,w158,w191,w3,w4,w5] [q0,q72,q143,q271] [] (by decide +kernel)
def n595 := cc 8 [w7,w0,w158,w274,w2,w3,w4,w5] [q11,q13,q260] [] (by decide +kernel)
def v731 : Closed T 8 := rotateClosed n569 auto8 auto8ok
def v732 : Closed T 8 := rotateClosed n595 auto1 auto1ok
def v733 : Closed T 8 := rotateClosed n532 auto8 auto8ok
def v734 : Closed T 8 := rotateClosed n532 auto9 auto9ok
def n596 := cc 9 [w7,w0,w158,w1,w2,w3,w4,w5] [q10,q11,q143,q260,q262,q271,q272] [v731,n595,v732,n594,n593,v733,v734,n397] (by decide +kernel)
def n597 := cc 8 [w7,w275,w1,w2,w3,w4,w5] [q0,q72,q143,q271] [n1] (by decide +kernel)
def v735 : Closed T 7 := rotateClosed n570 auto8 auto8ok
def v736 : Closed T 7 := rotateClosed n529 auto14 auto14ok
def n598 := cc 8 [w7,w0,w1,w276,w3,w4,w5] [q6,q207,q250,q271] [v735,v736] (by decide +kernel)
def n599 := cc 8 [w155,w8,w0,w1,w2,w3,w4] [q0,q7,q46,q153,q218] [n571] (by decide +kernel)
def v737 : Closed T 8 := rotateClosed n599 auto8 auto8ok
def v738 : Closed T 8 := rotateClosed n572 auto8 auto8ok
def v739 : Closed T 8 := rotateClosed n598 auto6 auto6ok
def v740 : Closed T 8 := rotateClosed n530 auto8 auto8ok
def n600 := cc 9 [w7,w0,w1,w2,w191,w3,w4,w5] [q0,q72,q143,q271] [v737,n22,v738,n597,n513,n594,v739,v740,v495] (by decide +kernel)
def n601 := cc 7 [w7,w162,w0,w2,w3,w4] [q6,q7,q195,q207,q250,q262] [] (by decide +kernel)
def v741 : Closed T 7 := rotateClosed n601 auto8 auto8ok
def n602 := cc 8 [w86,w8,w166,w1,w2,w3,w4] [q13,q151,q218,q262] [v741] (by decide +kernel)
def v742 : Closed T 8 := rotateClosed n382 auto8 auto8ok
def n603 := cc 9 [w86,w8,w0,w1,w2,w3,w4,w5] [q13,q218,q256,q262] [n573,n602,v742] (by decide +kernel)
def n604 := cc 8 [w7,w212,w1,w2,w3,w4,w5] [q7,q265,q271] [n1] (by decide +kernel)
def n605 := cc 8 [w7,w0,w212,w1,w2,w3,w4,w5] [q260,q261,q262] [n302] (by decide +kernel)
def n606 := cc 9 [w7,w156,w0,w1,w2,w3,w4,w5] [q0,q7,q14,q262,q271,q272] [n393,n22,n574,v618,n605,n604,n531] (by decide +kernel)
def n607 := cc 7 [w138,w7,w0,w1,w2,w3] [q4,q11,q130,q143,q207,q250] [n549] (by decide +kernel)
def v743 : Closed T 7 := rotateClosed n607 auto5 auto5ok
def n608 := cc 8 [w7,w0,w1,w104,w71,w4,w5] [q0,q7,q46,q72,q143,q207] [v743,n550] (by decide +kernel)
def v744 : Closed T 8 := rotateClosed n533 auto8 auto8ok
def n609 := cc 9 [w7,w0,w1,w104,w2,w3,w4,w5] [q14,q103,q260,q265,q271] [n493,n551,n608,v744] (by decide +kernel)
def n610 := cc 8 [w277,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q143,q207] [] (by decide +kernel)
def n611 := cc 8 [w0,w278,w1,w2,w3,w4,w5] [q0,q7,q46,q153,q218] [] (by decide +kernel)
def n612 := cc 8 [w7,w0,w176,w2,w3,w4,w5] [q0,q46,q143,q207] [] (by decide +kernel)
def n613 := cc 8 [w7,w0,w176,w1,w2,w3,w4,w5] [q0,q7,q46,q143,q207] [] (by decide +kernel)
def n614 := cc 7 [w7,w279,w2,w3,w4,w5] [q0,q7,q78,q147,q209] [n252] (by decide +kernel)
def n615 := cc 8 [w7,w179,w0,w2,w3,w4,w5] [q0,q7,q143,q207] [n614] (by decide +kernel)
def v745 : Closed T 8 := rotateClosed n611 auto8 auto8ok
def n616 := cc 9 [w7,w0,w1,w2,w3,w71,w4,w5] [q0,q7,q46,q143,q207,q271] [n610,n615,n552,n613,n612,n608,v745] (by decide +kernel)
def n617 := cc 8 [w280,w0,w1,w2,w3,w4,w5] [q6,q13,q77,q250,q271] [] (by decide +kernel)
def n618 := cc 8 [w281,w0,w1,w2,w3,w4,w5] [q0,q6,q46,q72,q143] [] (by decide +kernel)
def n619 := cc 8 [w7,w0,w1,w2,w3,w4,w111] [q0,q7,q46,q143,q207] [n553] (by decide +kernel)
def n620 := cc 8 [w7,w0,w1,w113,w3,w4,w5] [q6,q207,q250,q271] [n554] (by decide +kernel)
def v746 : Closed T 7 := rotateClosed n607 auto1 auto1ok
def n621 := cc 8 [w74,w114,w7,w0,w1,w2,w4] [q2,q10,q46,q72,q250] [n555,v746] (by decide +kernel)
def v747 : Closed T 8 := rotateClosed n618 auto7 auto7ok
def v748 : Closed T 8 := rotateClosed n620 auto1 auto1ok
def v749 : Closed T 8 := rotateClosed n619 auto6 auto6ok
def n622 := cc 9 [w74,w7,w0,w1,w2,w3,w4,w5] [q6,q72,q163,q171,q271,q272] [n621,n556,v747,v748,v749,n617] (by decide +kernel)
def n623 := cc 6 [w0,w1,w2,w3,w283,w4,w5] [q262] [] (by decide +kernel)
def n624 := cc 7 [w0,w1,w42,w2,w3,w282,w4,w5] [q2,q74,q144,q163,q166,q265,q272] [n623] (by decide +kernel)
def v750 : Closed T 7 := rotateClosed n624 auto2 auto2ok
def n625 := cc 8 [w0,w1,w2,w284,w3,w4,w5] [q6,q168,q169,q260,q261,q262,q271] [v750] (by decide +kernel)
def n626 := cc 8 [w285,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q14,q103,q265] [] (by decide +kernel)
def n627 := cc 7 [w0,w169,w2,w209,w3,w4,w5] [q262,q271,q272] [] (by decide +kernel)
def v751 : Closed T 7 := rotateClosed n627 auto8 auto8ok
def n628 := cc 8 [w7,w1,w2,w183,w3,w4,w5] [q0,q6,q265,q271] [v751] (by decide +kernel)
def v752 : Closed T 7 := rotateClosed n320 auto8 auto8ok
def n629 := cc 8 [w7,w0,w1,w2,w183,w3,w4,w5] [q6,q260,q261,q262,q271] [v752] (by decide +kernel)
def n630 := cc 7 [w7,w287,w2,w3,w4,w5] [q0,q2,q4,q7] [n268] (by decide +kernel)
def v753 : Closed T 7 := rotateClosed n539 auto1 auto1ok
def v754 : Closed T 7 := rotateClosed n630 auto2 auto2ok
def n631 := cc 8 [w221,w7,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q265] [n539,v753,v754,n51] (by decide +kernel)
def n632 := cc 7 [w0,w288,w1,w2,w41,w5] [q10,q88,q265] [] (by decide +kernel)
def n633 := cc 7 [w116,w7,w0,w1,w2,w5] [q2,q72,q207,q272] [n557] (by decide +kernel)
def v755 : Closed T 7 := rotateClosed n633 auto2 auto2ok
def v756 : Closed T 7 := rotateClosed n632 auto10 auto10ok
def n634 := cc 8 [w7,w0,w1,w42,w3,w4,w82] [q0,q72,q143,q271] [v755,n558,v756] (by decide +kernel)
def n635 := cc 6 [w0,w289,w1,w2,w3,w4,w5] [q0] [] (by decide +kernel)
def v757 : Closed T 6 := rotateClosed n635 auto8 auto8ok
def n636 := cc 7 [w7,w0,w1,w2,w3,w117,w4,w5] [q0,q7,q142,q206,q262,q271,q275,q276] [n559,v757,n623] (by decide +kernel)
def n637 := cc 8 [w7,w0,w1,w42,w2,w41,w3,w4,w5] [q0,q2,q72,q143,q207,q262,q265,q275,q276] [n560,n636,n624,v750] (by decide +kernel)
def v758 : Closed T 8 := rotateClosed n626 auto2 auto2ok
def v759 : Closed T 8 := rotateClosed n631 auto2 auto2ok
def v760 : Closed T 8 := rotateClosed n535 auto8 auto8ok
def v761 : Closed T 8 := rotateClosed n540 auto8 auto8ok
def v762 : Closed T 8 := rotateClosed n540 auto14 auto14ok
def v763 : Closed T 8 := rotateClosed n542 auto10 auto10ok
def v764 : Closed T 8 := rotateClosed n542 auto11 auto11ok
def n638 := cc 9 [w7,w0,w1,w42,w2,w3,w4,w5] [q6,q14,q143,q171,q207,q250,q260,q262,q271,q272] [v758,v759,n496,n561,n637,n634,n629,n628,n375,v760,v761,v762,v763,v764,n625] (by decide +kernel)
def n639 := cc 8 [w290,w0,w1,w2,w3,w4,w5] [q0,q46,q143,q207] [] (by decide +kernel)
def n640 := cc 8 [w0,w288,w1,w2,w3,w4,w5] [q10,q46,q153,q218] [n632] (by decide +kernel)
def v765 : Closed T 8 := rotateClosed n634 auto2 auto2ok
def v766 : Closed T 8 := rotateClosed n640 auto8 auto8ok
def n641 := cc 9 [w7,w0,w1,w2,w3,w4,w79,w5] [q2,q72,q207,q272] [n639,n562,v765,v766] (by decide +kernel)
def n642 := cc 8 [w291,w0,w1,w2,w3,w4,w5] [q6,q166,q207,q250] [] (by decide +kernel)
def n643 := cc 8 [w292,w0,w1,w2,w3,w4,w5] [q0,q6,q46,q72,q143] [] (by decide +kernel)
def n644 := cc 8 [w43,w119,w7,w0,w1,w3,w4] [q0,q7,q46,q143,q207] [n563,v755] (by decide +kernel)
def v767 : Closed T 8 := rotateClosed n541 auto8 auto8ok
def v768 : Closed T 8 := rotateClosed n643 auto6 auto6ok
def n645 := cc 9 [w43,w7,w0,w1,w2,w3,w4,w5] [q6,q207,q250,q271] [n644,n564,v767,v768,n642] (by decide +kernel)
def v769 : Closed T 9 := rotateClosed n528 auto2 auto2ok
def v770 : Closed T 9 := rotateClosed n528 auto3 auto3ok
def v771 : Closed T 9 := rotateClosed n528 auto6 auto6ok
def v772 : Closed T 9 := rotateClosed n590 auto2 auto2ok
def v773 : Closed T 9 := rotateClosed n590 auto3 auto3ok
def v774 : Closed T 9 := rotateClosed n590 auto6 auto6ok
def v775 : Closed T 9 := rotateClosed n603 auto8 auto8ok
def v776 : Closed T 9 := rotateClosed n603 auto10 auto10ok
def v777 : Closed T 9 := rotateClosed n603 auto11 auto11ok
def v778 : Closed T 9 := rotateClosed n603 auto14 auto14ok
def v779 : Closed T 9 := rotateClosed n645 auto2 auto2ok
def v780 : Closed T 9 := rotateClosed n645 auto3 auto3ok
def v781 : Closed T 9 := rotateClosed n645 auto6 auto6ok
def v782 : Closed T 9 := rotateClosed n622 auto1 auto1ok
def v783 : Closed T 9 := rotateClosed n622 auto2 auto2ok
def v784 : Closed T 9 := rotateClosed n622 auto3 auto3ok
def v785 : Closed T 9 := rotateClosed n622 auto4 auto4ok
def v786 : Closed T 9 := rotateClosed n622 auto5 auto5ok
def v787 : Closed T 9 := rotateClosed n622 auto6 auto6ok
def v788 : Closed T 9 := rotateClosed n622 auto7 auto7ok
def v789 : Closed T 9 := rotateClosed n509 auto2 auto2ok
def v790 : Closed T 9 := rotateClosed n509 auto3 auto3ok
def v791 : Closed T 9 := rotateClosed n509 auto6 auto6ok
def v792 : Closed T 9 := rotateClosed n498 auto2 auto2ok
def v793 : Closed T 9 := rotateClosed n498 auto3 auto3ok
def v794 : Closed T 9 := rotateClosed n498 auto6 auto6ok
def v795 : Closed T 9 := rotateClosed n606 auto2 auto2ok
def v796 : Closed T 9 := rotateClosed n606 auto3 auto3ok
def v797 : Closed T 9 := rotateClosed n606 auto6 auto6ok
def v798 : Closed T 9 := rotateClosed n575 auto8 auto8ok
def v799 : Closed T 9 := rotateClosed n592 auto2 auto2ok
def v800 : Closed T 9 := rotateClosed n592 auto3 auto3ok
def v801 : Closed T 9 := rotateClosed n592 auto6 auto6ok
def v802 : Closed T 9 := rotateClosed n582 auto2 auto2ok
def v803 : Closed T 9 := rotateClosed n582 auto3 auto3ok
def v804 : Closed T 9 := rotateClosed n582 auto6 auto6ok
def v805 : Closed T 9 := rotateClosed n596 auto2 auto2ok
def v806 : Closed T 9 := rotateClosed n596 auto3 auto3ok
def v807 : Closed T 9 := rotateClosed n596 auto6 auto6ok
def v808 : Closed T 9 := rotateClosed n546 auto2 auto2ok
def v809 : Closed T 9 := rotateClosed n546 auto3 auto3ok
def v810 : Closed T 9 := rotateClosed n546 auto6 auto6ok
def v811 : Closed T 9 := rotateClosed n609 auto1 auto1ok
def v812 : Closed T 9 := rotateClosed n609 auto4 auto4ok
def v813 : Closed T 9 := rotateClosed n609 auto5 auto5ok
def v814 : Closed T 9 := rotateClosed n638 auto2 auto2ok
def v815 : Closed T 9 := rotateClosed n512 auto2 auto2ok
def v816 : Closed T 9 := rotateClosed n512 auto3 auto3ok
def v817 : Closed T 9 := rotateClosed n512 auto6 auto6ok
def v818 : Closed T 9 := rotateClosed n587 auto2 auto2ok
def v819 : Closed T 9 := rotateClosed n587 auto3 auto3ok
def v820 : Closed T 9 := rotateClosed n587 auto6 auto6ok
def v821 : Closed T 9 := rotateClosed n600 auto2 auto2ok
def v822 : Closed T 9 := rotateClosed n600 auto3 auto3ok
def v823 : Closed T 9 := rotateClosed n600 auto6 auto6ok
def v824 : Closed T 9 := rotateClosed n616 auto1 auto1ok
def v825 : Closed T 9 := rotateClosed n616 auto4 auto4ok
def v826 : Closed T 9 := rotateClosed n616 auto5 auto5ok
def v827 : Closed T 9 := rotateClosed n641 auto2 auto2ok
def v828 : Closed T 9 := rotateClosed n543 auto8 auto8ok
def v829 : Closed T 9 := rotateClosed n543 auto10 auto10ok
def v830 : Closed T 9 := rotateClosed n543 auto11 auto11ok
def v831 : Closed T 9 := rotateClosed n543 auto14 auto14ok
def n646 := cc 10 [w7,w0,w1,w2,w3,w4,w5] [q14,q103,q171] [n528,v769,v770,v771,n590,v772,v773,v774,v775,v776,v777,v778,n645,v779,v780,v781,n622,v782,v783,v784,v785,v786,v787,v788,n509,v789,v790,v791,n498,v792,v793,v794,n606,v795,v796,v797,n578,n575,v798,n565,n592,v799,v800,v801,n28,n18,n582,v802,v803,v804,n596,v805,v806,v807,n546,v808,v809,v810,n381,n609,v811,v812,v813,n638,v814,n512,v815,v816,v817,n587,v818,v819,v820,n600,v821,v822,v823,n616,v824,v825,v826,n641,v827,n380,n485,v828,v829,v830,v831,n486] (by decide +kernel)
def n647 := cc 8 [w14,w233,w1,w2,w3,w4,w5] [q0,q7,q207,q250] [n29] (by decide +kernel)
def n648 := cc 6 [w162,w35,w0,w2,w4] [q6,q7,q10,q230] [] (by decide +kernel)
def v832 : Closed T 6 := rotateClosed n648 auto10 auto10ok
def n649 := cc 7 [w23,w293,w1,w3,w294,w5] [q0,q2,q229] [v832] (by decide +kernel)
def n650 := cc 8 [w23,w293,w0,w1,w3,w4,w5] [q0,q2,q4,q6,q7,q271] [n649] (by decide +kernel)
def n651 := cc 6 [w159,w191,w3,w4,w21] [q48,q132,q187] [] (by decide +kernel)
def v833 : Closed T 6 := rotateClosed n651 auto8 auto8ok
def n652 := cc 7 [w0,w157,w2,w3,w4,w21] [q0,q179,q232] [v833] (by decide +kernel)
def n653 := cc 6 [w162,w0,w16,w3,w4] [q6,q7,q173,q227] [] (by decide +kernel)
def v834 : Closed T 6 := rotateClosed n653 auto14 auto14ok
def n654 := cc 7 [w85,w1,w154,w3,w4,w21] [q0,q7,q181] [v834,v833] (by decide +kernel)
def n655 := cc 8 [w85,w0,w1,w2,w3,w4,w21] [q0,q178,q231,q271] [v27,n654,n652] (by decide +kernel)
def n656 := cc 7 [w30,w233,w1,w3,w4,w152] [q0,q164,q176,q229] [] (by decide +kernel)
def n657 := cc 8 [w30,w233,w0,w1,w3,w4,w5] [q2,q4,q271] [n656] (by decide +kernel)
def n658 := cc 7 [w296,w1,w2,w3,w4,w5] [q7,q10,q11,q13] [] (by decide +kernel)
def n659 := cc 6 [w296,w2,w3,w4,w161] [] [] (by decide +kernel)
def n660 := cc 6 [w297,w234,w2,w3,w4] [] [] (by decide +kernel)
def v835 : Closed T 6 := rotateClosed n659 auto6 auto6ok
def v836 : Closed T 6 := rotateClosed n660 auto14 auto14ok
def n661 := cc 7 [w18,w159,w191,w3,w4,w5] [q18,q262] [v835,v836,n651] (by decide +kernel)
def v837 : Closed T 7 := rotateClosed n658 auto14 auto14ok
def v838 : Closed T 7 := rotateClosed n661 auto8 auto8ok
def n662 := cc 8 [w18,w0,w157,w2,w3,w4,w5] [q2,q271] [v837,v838,n652] (by decide +kernel)
def n663 := cc 7 [w297,w233,w1,w2,w3,w4] [q0,q6,q172,q226] [] (by decide +kernel)
def v839 : Closed T 6 := rotateClosed n648 auto1 auto1ok
def n664 := cc 7 [w162,w13,w0,w2,w3,w4] [q6,q7,q165,q172,q218,q226] [n648,v839,n653] (by decide +kernel)
def v840 : Closed T 7 := rotateClosed n664 auto14 auto14ok
def v841 : Closed T 7 := rotateClosed n656 auto6 auto6ok
def v842 : Closed T 7 := rotateClosed n649 auto4 auto4ok
def v843 : Closed T 7 := rotateClosed n649 auto5 auto5ok
def v844 : Closed T 7 := rotateClosed n663 auto6 auto6ok
def n665 := cc 8 [w18,w85,w1,w154,w3,w4,w5] [q0,q6,q7,q15,q104] [v840,v841,v842,v843,v844,v838,n654] (by decide +kernel)
def v845 : Closed T 8 := rotateClosed n647 auto6 auto6ok
def v846 : Closed T 8 := rotateClosed n657 auto6 auto6ok
def v847 : Closed T 8 := rotateClosed n650 auto4 auto4ok
def v848 : Closed T 8 := rotateClosed n650 auto5 auto5ok
def n666 := cc 9 [w18,w85,w0,w1,w2,w3,w4,w5] [q2,q4,q14,q103,q271] [n22,v37,v845,n139,v846,v847,v848,n665,n662,n655] (by decide +kernel)
def n667 := cc 8 [w85,w1,w159,w2,w3,w4,w5] [q0,q7,q46,q130,q163] [] (by decide +kernel)
def n668 := cc 8 [w156,w0,w157,w2,w3,w4,w5] [q0,q7,q46,q130,q163] [v608] (by decide +kernel)
def n669 := cc 7 [w0,w298,w191,w3,w4,w5] [q0,q27,q163] [] (by decide +kernel)
def n670 := cc 7 [w0,w157,w276,w3,w4,w5] [q179,q232,q262] [] (by decide +kernel)
def v849 : Closed T 7 := rotateClosed n669 auto6 auto6ok
def n671 := cc 8 [w0,w157,w2,w3,w4,w5,w161] [q6,q179,q271] [v849,n408,n670] (by decide +kernel)
def n672 := cc 8 [w86,w1,w159,w2,w3,w4,w5] [q13,q186,q262] [] (by decide +kernel)
def n673 := cc 8 [w192,w0,w1,w157,w2,w3,w4,w5] [q0,q6,q7,q46,q130] [] (by decide +kernel)
def n674 := cc 7 [w192,w1,w295,w2,w3,w4,w5] [q6,q7,q38,q123] [] (by decide +kernel)
def n675 := cc 7 [w0,w1,w299,w2,w3,w4,w5] [q27,q73,q88,q114,q186] [] (by decide +kernel)
def v850 : Closed T 7 := rotateClosed n674 auto6 auto6ok
def n676 := cc 8 [w0,w1,w159,w2,w3,w4,w5,w161] [q46,q186,q237,q262,q271] [v850,n675] (by decide +kernel)
def n677 := cc 8 [w86,w0,w1,w157,w2,w3,w4,w5] [q179,q232,q262] [] (by decide +kernel)
def n678 := cc 8 [w0,w1,w301,w2,w3,w4,w5] [q46,q119,q262,q265] [] (by decide +kernel)
def n679 := cc 8 [w303,w0,w1,w2,w3,w4,w5] [q14,q130,q168,q262,q271] [] (by decide +kernel)
def v851 : Closed T 7 := rotateClosed n669 auto8 auto8ok
def n680 := cc 8 [w0,w1,w304,w2,w3,w4,w5] [q14,q103,q262,q265,q271] [v851,v462] (by decide +kernel)
def n681 := cc 8 [w305,w0,w1,w2,w3,w4,w5] [q262,q272] [] (by decide +kernel)
def v852 : Closed T 8 := rotateClosed n677 auto8 auto8ok
def v853 : Closed T 8 := rotateClosed n681 auto14 auto14ok
def v854 : Closed T 8 := rotateClosed n679 auto12 auto12ok
def v855 : Closed T 8 := rotateClosed n679 auto13 auto13ok
def v856 : Closed T 8 := rotateClosed n491 auto8 auto8ok
def v857 : Closed T 8 := rotateClosed n500 auto8 auto8ok
def v858 : Closed T 8 := rotateClosed n668 auto8 auto8ok
def v859 : Closed T 8 := rotateClosed n305 auto8 auto8ok
def v860 : Closed T 8 := rotateClosed n673 auto8 auto8ok
def v861 : Closed T 8 := rotateClosed n678 auto2 auto2ok
def v862 : Closed T 8 := rotateClosed n678 auto3 auto3ok
def v863 : Closed T 8 := rotateClosed n680 auto6 auto6ok
def v864 : Closed T 8 := rotateClosed n671 auto8 auto8ok
def n682 := cc 9 [w0,w1,w159,w2,w3,w4,w5] [q14,q46,q130,q171,q262,q265] [v852,n672,n393,v853,v854,v855,v101,v856,n593,n2,v857,v858,n306,v859,n667,v860,v861,v862,v863,n432,n676,n21,v864] (by decide +kernel)
def n683 := cc 7 [w162,w0,w295,w2,w3,w4] [q6,q13,q195,q243,q262] [] (by decide +kernel)
def v865 : Closed T 7 := rotateClosed n683 auto14 auto14ok
def n684 := cc 8 [w85,w1,w157,w154,w3,w4,w5] [q46,q130,q271] [v865,v838] (by decide +kernel)
def n685 := cc 7 [w162,w0,w1,w295,w2,w3,w4] [q6,q7,q13,q195,q243] [] (by decide +kernel)
def v866 : Closed T 7 := rotateClosed n685 auto14 auto14ok
def n686 := cc 8 [w85,w0,w1,w157,w154,w3,w4,w5] [q0,q7,q46,q130,q271] [v866] (by decide +kernel)
def n687 := cc 8 [w85,w0,w1,w306,w2,w3,w4,w5] [q46,q265,q267,q269] [] (by decide +kernel)
def n688 := cc 7 [w0,w1,w159,w2,w3,w307,w4,w5] [q0,q50,q140,q262,q272] [] (by decide +kernel)
def n689 := cc 7 [w221,w158,w1,w159,w2,w3,w4,w5] [q0,q7] [] (by decide +kernel)
def n690 := cc 7 [w308,w0,w158,w1,w2,w3,w4,w5] [q53,q75,q84,q133,q265] [] (by decide +kernel)
def v867 : Closed T 7 := rotateClosed n689 auto8 auto8ok
def v868 : Closed T 7 := rotateClosed n690 auto8 auto8ok
def v869 : Closed T 7 := rotateClosed n688 auto8 auto8ok
def n691 := cc 8 [w85,w0,w1,w157,w2,w41,w3,w4,w5] [q2,q46,q88,q130,q265,q271,q272] [v867,v868,v869] (by decide +kernel)
def v870 : Closed T 8 := rotateClosed n687 auto1 auto1ok
def n692 := cc 9 [w85,w0,w1,w157,w2,w3,w4,w5] [q2,q46,q130,q262,q271,q272] [n491,v39,n662,n687,v870,n691,n686,n684] (by decide +kernel)
def n693 := cc 8 [w65,w233,w1,w2,w3,w4,w5] [q0,q13,q172] [n487] (by decide +kernel)
def n694 := cc 6 [w14,w309,w2,w3,w4] [] [] (by decide +kernel)
def v871 : Closed T 6 := rotateClosed n694 auto14 auto14ok
def v872 : Closed T 6 := rotateClosed n659 auto14 auto14ok
def n695 := cc 7 [w11,w310,w154,w3,w4,w5] [q6,q7,q78] [v871,v872] (by decide +kernel)
def n696 := cc 8 [w11,w310,w0,w2,w3,w4,w5] [q2,q271] [n695,v837] (by decide +kernel)
def n697 := cc 7 [w85,w1,w311,w3,w4,w5] [q0,q6,q7,q72,q143] [v871] (by decide +kernel)
def n698 := cc 7 [w11,w312,w1,w3,w4,w5] [q0,q6,q46,q72,q143] [] (by decide +kernel)
def n699 := cc 8 [w11,w85,w1,w154,w3,w4,w5] [q0,q6,q7,q46,q72,q143] [n695,n698,n697] (by decide +kernel)
def v873 : Closed T 8 := rotateClosed n693 auto6 auto6ok
def n700 := cc 9 [w11,w85,w0,w1,w2,w3,w4,w5] [q2,q4,q271] [n696,n699,n491,n117,v873,n537] (by decide +kernel)
def n701 := cc 7 [w313,w1,w154,w3,w4,w5] [q0,q42,q125,q167] [] (by decide +kernel)
def n702 := cc 8 [w313,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q46,q171] [n701] (by decide +kernel)
def n703 := cc 8 [w0,w314,w1,w2,w3,w4,w5] [q163,q261,q269] [v22] (by decide +kernel)
def n704 := cc 8 [w316,w0,w1,w2,w3,w4,w5] [q2,q6,q46,q143] [] (by decide +kernel)
def n705 := cc 8 [w0,w318,w1,w2,w3,w4,w5] [q7,q88,q163,q261] [] (by decide +kernel)
def n706 := cc 7 [w14,w1,w2,w194,w3,w4] [q0,q7,q42,q125] [] (by decide +kernel)
def n707 := cc 8 [w14,w1,w2,w154,w3,w4,w5] [q0,q7,q42,q166] [n701,n706] (by decide +kernel)
def n708 := cc 7 [w14,w1,w2,w320,w3,w4] [q6,q42,q125] [] (by decide +kernel)
def n709 := cc 7 [w86,w1,w322,w2,w3,w4] [q6,q164,q188,q238] [] (by decide +kernel)
def n710 := cc 7 [w86,w321,w1,w42,w3,w4] [q0,q13,q163,q188] [] (by decide +kernel)
def v874 : Closed T 7 := rotateClosed n708 auto6 auto6ok
def n711 := cc 8 [w86,w321,w1,w2,w3,w4,w5] [q0,q7,q188,q238] [n710,n709,v874,v21] (by decide +kernel)
def n712 := cc 8 [w14,w166,w1,w2,w3,w4,w5] [q6,q166,q207,q250] [] (by decide +kernel)
def n713 := cc 8 [w14,w0,w274,w1,w2,w3,w4,w5] [q2,q7,q11,q46,q207] [] (by decide +kernel)
def n714 := cc 8 [w14,w323,w0,w1,w2,w3,w4,w5] [q2,q10,q157,q169,q271] [] (by decide +kernel)
def v875 : Closed T 7 := rotateClosed n710 auto6 auto6ok
def n715 := cc 8 [w14,w0,w1,w42,w2,w3,w4] [q14,q260,q261,q262] [v875] (by decide +kernel)
def n716 := cc 8 [w43,w14,w0,w1,w2,w3,w4] [q0,q7,q207,q250] [] (by decide +kernel)
def n717 := cc 7 [w0,w1,w42,w2,w324,w3,w4,w5] [q145,q146,q171] [] (by decide +kernel)
def n718 := cc 7 [w14,w1,w2,w41,w3,w325,w4,w5] [q2,q168] [] (by decide +kernel)
def v876 : Closed T 7 := rotateClosed n717 auto2 auto2ok
def n719 := cc 8 [w14,w0,w1,w2,w41,w3,w4,w5] [q10,q11,q46,q168,q250,q260,q262,q271] [n718,v876] (by decide +kernel)
def v877 : Closed T 8 := rotateClosed n711 auto6 auto6ok
def v878 : Closed T 8 := rotateClosed n704 auto2 auto2ok
def v879 : Closed T 8 := rotateClosed n704 auto3 auto3ok
def v880 : Closed T 8 := rotateClosed n579 auto8 auto8ok
def v881 : Closed T 8 := rotateClosed n714 auto1 auto1ok
def v882 : Closed T 8 := rotateClosed n713 auto1 auto1ok
def v883 : Closed T 8 := rotateClosed n705 auto12 auto12ok
def v884 : Closed T 8 := rotateClosed n705 auto13 auto13ok
def v885 : Closed T 8 := rotateClosed n703 auto8 auto8ok
def n720 := cc 9 [w14,w0,w1,w2,w3,w4,w5] [q14,q171,q250,q260,q262] [v877,n716,v5,n702,v878,v879,v880,n2,n714,v881,n712,n31,n67,n647,n713,v882,n715,n719,n707,v85,v883,v884,v885,v9,n21] (by decide +kernel)
def n721 := cc 8 [w316,w0,w326,w1,w2,w3,w4,w5] [q7,q130,q265,q268] [] (by decide +kernel)
def n722 := cc 7 [w14,w328,w0,w1,w2,w3,w4,w5] [q0,q262] [] (by decide +kernel)
def n723 := cc 7 [w14,w327,w0,w1,w2,w41,w4,w5] [q1,q125,q126,q262,q265] [] (by decide +kernel)
def n724 := cc 8 [w14,w327,w0,w1,w2,w3,w4,w5] [q10,q125,q168,q262,q265] [n722,n723] (by decide +kernel)
def n725 := cc 7 [w14,w162,w0,w2,w3,w4] [q6,q207,q250,q262] [] (by decide +kernel)
def n726 := cc 8 [w14,w0,w160,w2,w3,w4,w161] [q6,q207,q262] [n725] (by decide +kernel)
def n727 := cc 7 [w14,w162,w0,w1,w2,w3,w4] [q6,q7,q13,q195,q207,q250] [] (by decide +kernel)
def n728 := cc 8 [w14,w0,w160,w1,w2,w3,w4,w161] [q6,q7,q207,q250,q262] [n727] (by decide +kernel)
def n729 := cc 7 [w14,w0,w1,w2,w3,w329,w4,w5] [q0,q262] [] (by decide +kernel)
def v886 : Closed T 7 := rotateClosed n723 auto1 auto1ok
def n730 := cc 8 [w14,w0,w160,w1,w2,w41,w3,w4,w5] [q10,q195,q262,q267,q268] [n722,n723,v886,n729] (by decide +kernel)
def v887 : Closed T 8 := rotateClosed n696 auto14 auto14ok
def v888 : Closed T 8 := rotateClosed n721 auto2 auto2ok
def v889 : Closed T 8 := rotateClosed n721 auto3 auto3ok
def v890 : Closed T 8 := rotateClosed n724 auto1 auto1ok
def v891 : Closed T 8 := rotateClosed n392 auto6 auto6ok
def n731 := cc 9 [w14,w0,w160,w1,w2,w3,w4,w5] [q10,q207,q250,q262,q271] [v887,v888,v889,n724,v890,n31,n730,n728,n726,v891] (by decide +kernel)
def n732 := cc 7 [w85,w1,w183,w3,w4,w5] [q59,q136,q262] [] (by decide +kernel)
def v892 : Closed T 7 := rotateClosed n732 auto8 auto8ok
def n733 := cc 8 [w168,w0,w158,w1,w3,w4,w5] [q171,q262,q272] [v892] (by decide +kernel)
def n734 := cc 8 [w85,w0,w330,w1,w3,w4,w5] [q6,q260,q261] [] (by decide +kernel)
def v893 : Closed T 8 := rotateClosed n734 auto8 auto8ok
def n735 := cc 9 [w156,w0,w158,w1,w3,w4,w5] [q11,q14,q262,q272] [n733,v893] (by decide +kernel)
def n736 := cc 8 [w156,w0,w158,w1,w3,w4,w5] [q7,q13,q14,q103] [] (by decide +kernel)
def n737 := cc 8 [w168,w0,w1,w2,w3,w4,w5] [q7,q67,q99,q160,q262] [] (by decide +kernel)
def n738 := cc 8 [w331,w0,w1,w2,w3,w4,w5] [q6,q95,q156,q166] [] (by decide +kernel)
def v894 : Closed T 8 := rotateClosed n738 auto14 auto14ok
def n739 := cc 9 [w156,w0,w1,w2,w3,w4,w5] [q7,q14,q103,q222,q262,q271] [n393,n22,n737,n736,v108,v894,n437] (by decide +kernel)
def n740 := cc 9 [w156,w0,w158,w1,w2,w3,w4,w5] [q14,q103,q262] [] (by decide +kernel)
def n741 := cc 8 [w0,w1,w333,w2,w3,w4,w5] [q11,q46,q72,q169,q262] [] (by decide +kernel)
def n742 := cc 8 [w335,w0,w1,w2,w3,w4,w5] [q0,q2,q7,q46,q250] [] (by decide +kernel)
def n743 := cc 7 [w337,w338,w0,w1,w3,w5] [q7,q10,q11,q13] [] (by decide +kernel)
def n744 := cc 8 [w337,w0,w336,w1,w3,w4,w5] [q10,q103,q262] [n743] (by decide +kernel)
def n745 := cc 7 [w0,w341,w2,w3,w4,w5] [q6,q23,q111] [] (by decide +kernel)
def n746 := cc 7 [w344,w1,w2,w3,w4,w5] [q0,q192,q240] [] (by decide +kernel)
def n747 := cc 7 [w346,w0,w1,w3,w4,w5] [q7,q118,q193] [] (by decide +kernel)
def n748 := cc 7 [w347,w0,w1,w3,w4,w5] [q7,q193,q241] [] (by decide +kernel)
def v895 : Closed T 7 := rotateClosed n746 auto14 auto14ok
def v896 : Closed T 7 := rotateClosed n747 auto8 auto8ok
def v897 : Closed T 7 := rotateClosed n748 auto14 auto14ok
def n749 := cc 8 [w340,w0,w1,w2,w3,w4,w5] [q0,q22,q92,q171,q271] [v895,v896,v897,n745] (by decide +kernel)
def n750 := cc 8 [w348,w0,w1,w2,w3,w4,w5] [q7,q122,q262] [] (by decide +kernel)
def v898 : Closed T 8 := rotateClosed n742 auto13 auto13ok
def v899 : Closed T 8 := rotateClosed n744 auto9 auto9ok
def v900 : Closed T 8 := rotateClosed n744 auto12 auto12ok
def v901 : Closed T 8 := rotateClosed n750 auto13 auto13ok
def v902 : Closed T 8 := rotateClosed n750 auto15 auto15ok
def v903 : Closed T 8 := rotateClosed n749 auto2 auto2ok
def v904 : Closed T 8 := rotateClosed n741 auto8 auto8ok
def n751 := cc 9 [w339,w0,w1,w2,w3,w4,w5] [q4,q14,q103,q178,q265,q271] [n493,v898,v899,v900,v901,v902,n40,n749,v903,v904] (by decide +kernel)
def n752 := cc 8 [w337,w0,w158,w1,w3,w4,w5] [q10,q103,q262] [n743] (by decide +kernel)
def v905 : Closed T 8 := rotateClosed n752 auto9 auto9ok
def n753 := cc 9 [w339,w85,w0,w1,w2,w3,w4,w5] [q4,q14,q271] [v900,v905] (by decide +kernel)
def n754 := cc 8 [w0,w349,w1,w2,w3,w4,w5] [q7,q14,q153,q168,q262] [] (by decide +kernel)
def n755 := cc 7 [w156,w351,w0,w3,w4,w5] [] [] (by decide +kernel)
def v906 : Closed T 7 := rotateClosed n755 auto11 auto11ok
def n756 := cc 8 [w352,w0,w1,w2,w3,w4,w5] [q2,q6,q88,q104] [v906,v18] (by decide +kernel)
def n757 := cc 8 [w353,w0,w1,w2,w3,w4,w5] [q37,q168,q262] [] (by decide +kernel)
def n758 := cc 7 [w356,w0,w1,w3,w4,w5] [q13,q163,q193,q241] [] (by decide +kernel)
def n759 := cc 7 [w74,w358,w0,w1,w2,w4] [q2,q26,q234] [] (by decide +kernel)
def v907 : Closed T 7 := rotateClosed n759 auto7 auto7ok
def v908 : Closed T 7 := rotateClosed n758 auto12 auto12ok
def v909 : Closed T 7 := rotateClosed n747 auto11 auto11ok
def n760 := cc 8 [w361,w0,w1,w2,w3,w4,w5] [q4,q14,q168,q271] [v907,v908,v909] (by decide +kernel)
def n761 := cc 8 [w362,w0,w1,w2,w3,w4,w5] [q67,q160,q168,q262,q269] [] (by decide +kernel)
def n762 := cc 8 [w365,w0,w1,w2,w3,w4,w5] [q95,q166,q268] [] (by decide +kernel)
def n763 := cc 8 [w156,w367,w0,w1,w3,w4,w5] [q103,q260,q271] [n38] (by decide +kernel)
def n764 := cc 7 [w337,w0,w1,w3,w368,w5] [q10,q163,q169] [] (by decide +kernel)
def v910 : Closed T 7 := rotateClosed n759 auto8 auto8ok
def v911 : Closed T 7 := rotateClosed n764 auto4 auto4ok
def v912 : Closed T 7 := rotateClosed n747 auto2 auto2ok
def n765 := cc 8 [w74,w369,w0,w1,w2,w4,w5] [q10,q13,q14,q168,q239,q262] [v910,v911,v912] (by decide +kernel)
def n766 := cc 8 [w337,w0,w1,w42,w3,w4,w5] [q14,q258,q262,q269] [] (by decide +kernel)
def v913 : Closed T 8 := rotateClosed n765 auto3 auto3ok
def v914 : Closed T 8 := rotateClosed n679 auto8 auto8ok
def v915 : Closed T 8 := rotateClosed n757 auto2 auto2ok
def v916 : Closed T 8 := rotateClosed n763 auto8 auto8ok
def v917 : Closed T 8 := rotateClosed n756 auto5 auto5ok
def v918 : Closed T 8 := rotateClosed n762 auto15 auto15ok
def v919 : Closed T 8 := rotateClosed n760 auto12 auto12ok
def n767 := cc 9 [w337,w0,w1,w2,w3,w4,w5] [q103,q163,q171,q262,q269,q271,q275] [v913,v914,n704,v915,v916,n761,n744,n752,n766,v917,v918,v919,n754] (by decide +kernel)
def v920 : Closed T 7 := rotateClosed n722 auto2 auto2ok
def n768 := cc 8 [w362,w0,w326,w1,w2,w3,w4,w5] [q4,q141,q262,q265,q269,q271] [v920] (by decide +kernel)
def v921 : Closed T 7 := rotateClosed n723 auto2 auto2ok
def n769 := cc 8 [w337,w0,w326,w1,w42,w3,w4,w5] [q14,q258,q262,q265,q269,q271] [v921] (by decide +kernel)
def v922 : Closed T 8 := rotateClosed n724 auto2 auto2ok
def n770 := cc 9 [w337,w0,w326,w1,w2,w3,w4,w5] [q103,q258,q262,q265,q269,q271] [n721,v922,n768,n744,n769] (by decide +kernel)
def n771 := cc 7 [w221,w372,w2,w3,w4,w5] [q0,q2,q4,q6] [] (by decide +kernel)
def n772 := cc 7 [w221,w373,w1,w2,w4,w5] [q2,q149,q253] [] (by decide +kernel)
def v923 : Closed T 7 := rotateClosed n772 auto1 auto1ok
def n773 := cc 8 [w221,w371,w1,w2,w3,w4,w5] [q0,q14,q272] [n772,v923,n771] (by decide +kernel)
def n774 := cc 8 [w221,w0,w1,w2,w3,w4,w5] [q0,q212,q265] [] (by decide +kernel)
def n775 := cc 8 [w0,w203,w2,w3,w4,w5] [q0,q6,q262,q272] [] (by decide +kernel)
def n776 := cc 7 [w375,w1,w376,w3,w4,w5] [q7,q10,q11,q13] [] (by decide +kernel)
def n777 := cc 7 [w0,w203,w2,w3,w378,w5] [q2,q114,q232] [] (by decide +kernel)
def n778 := cc 7 [w346,w1,w379,w3,w4,w5] [q7,q10,q11,q13] [] (by decide +kernel)
def v924 : Closed T 7 := rotateClosed n771 auto2 auto2ok
def v925 : Closed T 7 := rotateClosed n776 auto8 auto8ok
def v926 : Closed T 7 := rotateClosed n776 auto14 auto14ok
def v927 : Closed T 7 := rotateClosed n778 auto10 auto10ok
def v928 : Closed T 7 := rotateClosed n778 auto11 auto11ok
def v929 : Closed T 7 := rotateClosed n777 auto1 auto1ok
def n779 := cc 8 [w377,w0,w203,w2,w3,w4,w5] [q2,q4,q271] [v924,v22,v925,v926,v927,v928,n777,v929] (by decide +kernel)
def n780 := cc 8 [w0,w1,w376,w2,w3,w4,w5] [q7,q262,q265,q271] [] (by decide +kernel)
def n781 := cc 7 [w38,w1,w42,w2,w3,w4,w5] [q0,q7,q121,q192] [] (by decide +kernel)
def n782 := cc 8 [w38,w1,w2,w3,w4,w5] [q2,q7,q13,q240,q265] [n781] (by decide +kernel)
def n783 := cc 7 [w38,w1,w2,w3,w4,w381] [q6,q7,q192] [] (by decide +kernel)
def n784 := cc 7 [w38,w346,w1,w3,w4,w5] [q7,q10,q11,q13] [] (by decide +kernel)
def v930 : Closed T 7 := rotateClosed n784 auto6 auto6ok
def v931 : Closed T 7 := rotateClosed n783 auto6 auto6ok
def v932 : Closed T 7 := rotateClosed n408 auto10 auto10ok
def n785 := cc 8 [w38,w380,w1,w2,w3,w4,w5] [q7,q13,q265] [n784,v930,n783,v931,v932] (by decide +kernel)
def n786 := cc 8 [w38,w0,w1,w2,w3,w4,w5] [q0,q6,q265] [] (by decide +kernel)
def n787 := cc 7 [w375,w382,w0,w1,w3,w4] [q7,q10,q11,q13] [] (by decide +kernel)
def v933 : Closed T 7 := rotateClosed n772 auto10 auto10ok
def n788 := cc 8 [w375,w0,w374,w1,w3,w4,w5] [q10,q14,q262] [v933,n787,n776] (by decide +kernel)
def n789 := cc 8 [w375,w0,w1,w2,w3,w4,w5] [q7,q122,q163,q222] [] (by decide +kernel)
def n790 := cc 7 [w0,w1,w2,w383,w378,w5] [q0,q29,q116,q180] [] (by decide +kernel)
def n791 := cc 7 [w346,w0,w1,w3,w4,w381] [q7,q193,q241] [] (by decide +kernel)
def v934 : Closed T 7 := rotateClosed n783 auto10 auto10ok
def v935 : Closed T 7 := rotateClosed n791 auto10 auto10ok
def n792 := cc 8 [w377,w0,w1,w2,w3,w378,w5] [q2,q113,q271] [v934,v909,v935,n790,n777] (by decide +kernel)
def n793 := cc 8 [w346,w0,w1,w3,w4,w5] [q10,q168,q169,q262,q271] [] (by decide +kernel)
def n794 := cc 7 [w346,w384,w0,w1,w3,w4] [q7,q10,q11,q13] [] (by decide +kernel)
def n795 := cc 8 [w346,w0,w380,w1,w3,w4,w5] [q13,q31,q265] [n784,n794,n791,n778] (by decide +kernel)
def n796 := cc 8 [w346,w0,w1,w2,w3,w4,w5] [q7,q31,q118,q163] [] (by decide +kernel)
def n797 := cc 6 [w0,w1,w385,w42,w3,w4,w5] [q184,q272] [] (by decide +kernel)
def n798 := cc 7 [w0,w1,w385,w2,w3,w4,w5] [q23,q46,q66,q75,q88,q166,q171,q272] [n797] (by decide +kernel)
def n799 := cc 7 [w85,w0,w1,w386,w2,w3,w4,w5] [q33,q265] [] (by decide +kernel)
def n800 := cc 6 [w0,w1,w387,w2,w3,w4,w5] [q23,q24,q38,q40] [] (by decide +kernel)
def v936 : Closed T 6 := rotateClosed n800 auto2 auto2ok
def n801 := cc 7 [w377,w0,w380,w1,w2,w3,w4,w5] [q0,q7,q31,q118,q163,q262,q272] [v936] (by decide +kernel)
def n802 := cc 7 [w375,w371,w0,w1,w2,w3,w4,w5] [q7,q163,q271] [] (by decide +kernel)
def n803 := cc 6 [w85,w0,w1,w388,w3,w4,w5] [q190,q262] [] (by decide +kernel)
def v937 : Closed T 6 := rotateClosed n803 auto10 auto10ok
def v938 : Closed T 6 := rotateClosed n797 auto2 auto2ok
def n804 := cc 7 [w377,w0,w274,w1,w2,w41,w4,w5] [q8,q113,q118,q271,q272] [v937,v938] (by decide +kernel)
def v939 : Closed T 7 := rotateClosed n802 auto3 auto3ok
def v940 : Closed T 7 := rotateClosed n799 auto10 auto10ok
def v941 : Closed T 7 := rotateClosed n798 auto2 auto2ok
def n805 := cc 8 [w377,w0,w274,w1,w2,w3,w4,w5] [q2,q7,q14,q113,q118,q271,q272] [v939,n801,n804,v940,v941] (by decide +kernel)
def v942 : Closed T 6 := rotateClosed n803 auto8 auto8ok
def v943 : Closed T 6 := rotateClosed n803 auto14 auto14ok
def n806 := cc 7 [w0,w1,w2,w389,w3,w4,w5] [q0,q7,q112,q184,q271] [v942,v943] (by decide +kernel)
def n807 := cc 7 [w0,w1,w42,w2,w389,w3,w4,w5] [q24,q25,q184] [] (by decide +kernel)
def n808 := cc 7 [w221,w0,w374,w1,w2,w3,w4,w5] [q0,q79,q148,q265] [] (by decide +kernel)
def v944 : Closed T 7 := rotateClosed n808 auto8 auto8ok
def v945 : Closed T 7 := rotateClosed n781 auto10 auto10ok
def v946 : Closed T 7 := rotateClosed n804 auto1 auto1ok
def v947 : Closed T 7 := rotateClosed n807 auto2 auto2ok
def v948 : Closed T 7 := rotateClosed n806 auto2 auto2ok
def n809 := cc 8 [w377,w0,w1,w2,w41,w3,w4,w5] [q2,q10,q113,q178,q271,q272] [v944,v945,n801,n804,v946,v947,v948] (by decide +kernel)
def v949 : Closed T 8 := rotateClosed n773 auto2 auto2ok
def v950 : Closed T 8 := rotateClosed n774 auto2 auto2ok
def v951 : Closed T 8 := rotateClosed n786 auto10 auto10ok
def v952 : Closed T 8 := rotateClosed n785 auto10 auto10ok
def v953 : Closed T 8 := rotateClosed n782 auto10 auto10ok
def v954 : Closed T 8 := rotateClosed n788 auto8 auto8ok
def v955 : Closed T 8 := rotateClosed n788 auto14 auto14ok
def v956 : Closed T 8 := rotateClosed n789 auto8 auto8ok
def v957 : Closed T 8 := rotateClosed n789 auto14 auto14ok
def v958 : Closed T 8 := rotateClosed n795 auto10 auto10ok
def v959 : Closed T 8 := rotateClosed n795 auto11 auto11ok
def v960 : Closed T 8 := rotateClosed n796 auto10 auto10ok
def v961 : Closed T 8 := rotateClosed n796 auto11 auto11ok
def v962 : Closed T 8 := rotateClosed n793 auto10 auto10ok
def v963 : Closed T 8 := rotateClosed n793 auto11 auto11ok
def v964 : Closed T 8 := rotateClosed n749 auto3 auto3ok
def v965 : Closed T 8 := rotateClosed n805 auto1 auto1ok
def v966 : Closed T 8 := rotateClosed n792 auto1 auto1ok
def v967 : Closed T 8 := rotateClosed n780 auto8 auto8ok
def n810 := cc 9 [w377,w0,w1,w2,w3,w4,w5] [q2,q4,q14,q103,q113,q178,q262,q271] [v949,v950,n496,v951,v952,v953,v954,v955,v956,v957,v958,v959,v960,v961,v962,v963,n54,v903,v964,n805,v965,n809,n792,v966,n779,v967,n775] (by decide +kernel)
def n811 := cc 8 [w221,w370,w1,w2,w3,w4,w5] [q0,q14,q272] [v923] (by decide +kernel)
def n812 := cc 6 [w376,w390,w3,w4,w161] [q124,q187] [] (by decide +kernel)
def v968 : Closed T 6 := rotateClosed n812 auto14 auto14ok
def n813 := cc 7 [w0,w203,w2,w3,w4,w391] [q0,q179,q232] [v968] (by decide +kernel)
def n814 := cc 7 [w85,w203,w154,w3,w4,w5] [q0,q27,q114,q167] [v968] (by decide +kernel)
def n815 := cc 8 [w85,w0,w203,w2,w3,w4,w5] [q2,q4,q271] [v926,n814,n813] (by decide +kernel)
def n816 := cc 7 [w38,w274,w2,w392,w4,w5] [q2,q7,q35,q170] [] (by decide +kernel)
def n817 := cc 8 [w38,w274,w1,w2,w3,w4,w5] [q7,q13,q265] [n816] (by decide +kernel)
def n818 := cc 8 [w375,w0,w158,w1,w3,w4,w5] [q10,q14,q262] [n787] (by decide +kernel)
def n819 := cc 7 [w346,w0,w274,w392,w4,w5] [q7,q170,q193] [] (by decide +kernel)
def n820 := cc 8 [w346,w0,w274,w1,w3,w4,w5] [q7,q13,q265] [n819] (by decide +kernel)
def n821 := cc 7 [w394,w0,w1,w2,w4,w5] [q7,q10,q11,q189] [] (by decide +kernel)
def n822 := cc 6 [w394,w0,w2,w395,w5] [] [] (by decide +kernel)
def v969 : Closed T 6 := rotateClosed n822 auto10 auto10ok
def v970 : Closed T 6 := rotateClosed n812 auto8 auto8ok
def n823 := cc 7 [w377,w1,w396,w3,w4,w152] [q181,q271] [v969,v970] (by decide +kernel)
def v971 : Closed T 7 := rotateClosed n821 auto12 auto12ok
def v972 : Closed T 7 := rotateClosed n823 auto6 auto6ok
def n824 := cc 8 [w377,w0,w1,w2,w3,w4,w391] [q0,q178,q271] [v971,v972,n813] (by decide +kernel)
def n825 := cc 6 [w397,w0,w2,w398,w5] [q10,q11,q34,q191] [] (by decide +kernel)
def n826 := cc 7 [w397,w0,w274,w2,w4,w5] [q10,q11,q31,q189] [n825] (by decide +kernel)
def n827 := cc 7 [w162,w0,w374,w2,w3,w4] [q13,q165,q185,q236] [] (by decide +kernel)
def v973 : Closed T 7 := rotateClosed n816 auto10 auto10ok
def v974 : Closed T 7 := rotateClosed n819 auto10 auto10ok
def v975 : Closed T 7 := rotateClosed n819 auto11 auto11ok
def v976 : Closed T 7 := rotateClosed n827 auto14 auto14ok
def v977 : Closed T 7 := rotateClosed n826 auto10 auto10ok
def n828 := cc 8 [w377,w85,w1,w154,w3,w4,w5] [q26,q113,q271] [v973,v974,v975,v976,v977,v972,n814] (by decide +kernel)
def v978 : Closed T 8 := rotateClosed n811 auto2 auto2ok
def v979 : Closed T 8 := rotateClosed n817 auto10 auto10ok
def v980 : Closed T 8 := rotateClosed n818 auto8 auto8ok
def v981 : Closed T 8 := rotateClosed n820 auto10 auto10ok
def v982 : Closed T 8 := rotateClosed n820 auto11 auto11ok
def n829 := cc 9 [w377,w85,w0,w1,w2,w3,w4,w5] [q2,q4,q14,q103,q171,q271] [v978,v979,v955,v980,v981,v982,n828,n824,n815] (by decide +kernel)
def n830 := cc 7 [w162,w0,w2,w390,w3,w4] [q7,q204,q249,q262] [] (by decide +kernel)
def v983 : Closed T 7 := rotateClosed n830 auto14 auto14ok
def n831 := cc 8 [w85,w1,w154,w3,w4,w5,w391] [q181,q262,q271] [v983,v972] (by decide +kernel)
def n832 := cc 8 [w85,w0,w1,w42,w3,w4,w391] [q6,q178,q231,q271] [] (by decide +kernel)
def n833 := cc 8 [w85,w0,w1,w153,w3,w4,w5] [q6,q178,q231,q271] [n732] (by decide +kernel)
def n834 := cc 9 [w85,w0,w1,w2,w3,w4,w5,w391] [q14,q178,q231,q262,q271] [v957,n824,n832,n833,n831] (by decide +kernel)
def v984 : Closed T 7 := rotateClosed n747 auto10 auto10ok
def n835 := cc 8 [w377,w0,w1,w2,w3,w4,w5] [q0,q26,q113,q271] [v22,v984,v909,n408] (by decide +kernel)
def n836 := cc 8 [w85,w400,w1,w2,w3,w4,w5] [q0,q113,q178] [] (by decide +kernel)
def n837 := cc 8 [w85,w0,w1,w401,w3,w4,w5] [q0,q13,q14,q178,q231] [] (by decide +kernel)
def n838 := cc 8 [w399,w402,w0,w1,w2,w3,w4] [q0,q178,q271] [v971] (by decide +kernel)
def n839 := cc 7 [w85,w1,w403,w3,w4,w5] [q0,q83,q271] [] (by decide +kernel)
def n840 := cc 7 [w399,w312,w1,w3,w4,w5] [q0,q83,q150,q271] [] (by decide +kernel)
def n841 := cc 8 [w399,w85,w1,w154,w3,w4,w5] [q83,q150,q271] [n840,n839] (by decide +kernel)
def n842 := cc 9 [w399,w85,w0,w1,w2,w3,w4,w5] [q0,q178,q231,q271] [n838,n841,n835,n836,n837] (by decide +kernel)
def n843 := cc 8 [w0,w404,w1,w2,w3,w4,w5] [q7,q14,q262,q265] [] (by decide +kernel)
def n844 := cc 7 [w156,w406,w0,w3,w4,w5] [] [] (by decide +kernel)
def v985 : Closed T 7 := rotateClosed n844 auto14 auto14ok
def n845 := cc 8 [w407,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q88,q171] [v985,v23] (by decide +kernel)
def n846 := cc 8 [w408,w0,w1,w2,w3,w4,w5] [q6,q7,q95,q168,q271] [] (by decide +kernel)
def n847 := cc 7 [w375,w0,w1,w194,w3,w4] [q0,q7,q37,q122,q166] [] (by decide +kernel)
def n848 := cc 8 [w375,w0,w1,w154,w3,w4,w5] [q0,q7,q37,q122,q163,q166] [n701,n847] (by decide +kernel)
def n849 := cc 8 [w156,w405,w0,w1,w3,w4,w5] [q260,q261,q271,q276] [n52] (by decide +kernel)
def n850 := cc 7 [w375,w373,w0,w1,w2,w3,w4,w5] [q2,q7,q163] [] (by decide +kernel)
def n851 := cc 7 [w375,w370,w0,w1,w2,w41,w4,w5] [q8,q110,q122,q169,q262] [] (by decide +kernel)
def v986 : Closed T 7 := rotateClosed n850 auto1 auto1ok
def n852 := cc 8 [w375,w370,w0,w1,w2,w3,w4,w5] [q122,q262,q269] [v986,n802,n851] (by decide +kernel)
def n853 := cc 8 [w86,w402,w0,w1,w2,w3,w4] [q178,q231,q262] [] (by decide +kernel)
def n854 := cc 8 [w375,w0,w1,w42,w3,w4,w5] [q7,q222,q258,q262] [v933] (by decide +kernel)
def n855 := cc 8 [w43,w382,w0,w1,w2,w3,w4] [q13,q99,q160,q166] [] (by decide +kernel)
def n856 := cc 7 [w221,w375,w0,w1,w2,w3,w4,w5] [q7,q163] [] (by decide +kernel)
def v987 : Closed T 7 := rotateClosed n851 auto1 auto1ok
def n857 := cc 8 [w375,w0,w1,w2,w41,w3,w4,w5] [q14,q122,q168,q262,q269,q276] [n856,n802,n851,v987] (by decide +kernel)
def v988 : Closed T 8 := rotateClosed n853 auto14 auto14ok
def v989 : Closed T 8 := rotateClosed n855 auto6 auto6ok
def v990 : Closed T 8 := rotateClosed n681 auto8 auto8ok
def v991 : Closed T 8 := rotateClosed n757 auto1 auto1ok
def v992 : Closed T 8 := rotateClosed n849 auto8 auto8ok
def v993 : Closed T 8 := rotateClosed n852 auto1 auto1ok
def v994 : Closed T 8 := rotateClosed n845 auto6 auto6ok
def v995 : Closed T 8 := rotateClosed n846 auto14 auto14ok
def v996 : Closed T 8 := rotateClosed n846 auto15 auto15ok
def v997 : Closed T 8 := rotateClosed n835 auto8 auto8ok
def n858 := cc 9 [w375,w0,w1,w2,w3,w4,w5] [q14,q171,q258,q262,q269,q271] [v988,v989,v990,n702,n757,v991,n737,v992,n852,v993,n788,n818,n854,n857,n848,v994,v995,v996,v997,v894,n843] (by decide +kernel)
def n859 := cc 7 [w399,w402,w1,w154,w3,w4] [] [] (by decide +kernel)
def n860 := cc 7 [w375,w162,w0,w2,w3,w4] [q7,q222,q258,q262] [] (by decide +kernel)
def v998 : Closed T 7 := rotateClosed n859 auto14 auto14ok
def n861 := cc 8 [w375,w0,w160,w2,w3,w4,w161] [q7,q163,q222,q258] [v998,n860] (by decide +kernel)
def n862 := cc 8 [w375,w0,w160,w1,w42,w3,w4] [q122,q262,q269] [] (by decide +kernel)
def v999 : Closed T 8 := rotateClosed n838 auto14 auto14ok
def v1000 : Closed T 8 := rotateClosed n733 auto6 auto6ok
def n863 := cc 9 [w375,w0,w160,w1,w2,w3,w4,w5] [q122,q171,q262,q269,q270] [v999,v1000,n788,n862,n861] (by decide +kernel)
def n864 := cc 7 [w409,w162,w0,w2,w3,w4] [q6,q7,q195,q207,q250,q271] [] (by decide +kernel)
def n865 := cc 7 [w162,w0,w410,w2,w3,w4] [q13,q218,q256,q262] [] (by decide +kernel)
def n866 := cc 7 [w411,w271,w1,w2,w3,w4] [] [] (by decide +kernel)
def n867 := cc 6 [w411,w412,w2,w3,w4] [] [] (by decide +kernel)
def n868 := cc 6 [w162,w0,w414,w3,w4] [q6,q7,q173,q227] [] (by decide +kernel)
def n869 := cc 6 [w162,w415,w0,w3,w4] [q6,q13,q176,q229] [] (by decide +kernel)
def v1001 : Closed T 6 := rotateClosed n867 auto8 auto8ok
def n870 := cc 7 [w162,w413,w0,w2,w3,w4] [q6,q7,q13,q163,q172,q226] [v1001,n869,n868] (by decide +kernel)
def n871 := cc 6 [w416,w0,w417,w3,w4] [q7,q163,q215,q255] [] (by decide +kernel)
def n872 := cc 7 [w416,w162,w0,w2,w3,w4] [q7,q13,q222,q258,q262] [n871] (by decide +kernel)
def n873 := cc 7 [w162,w0,w2,w417,w3,w4] [q6,q7,q13,q214,q254,q262] [n871] (by decide +kernel)
def n874 := cc 7 [w419,w418,w0,w3,w4,w5] [] [] (by decide +kernel)
def n875 := cc 7 [w162,w0,w420,w2,w3,w4] [q13,q185,q236,q262] [] (by decide +kernel)
def n876 := cc 5 [w162,w312,w3,w4] [q262,q267,q268] [] (by decide +kernel)
def n877 := cc 6 [w162,w85,w154,w3,w4] [q6,q7,q181,q233] [n876] (by decide +kernel)
def n878 := cc 7 [w162,w85,w0,w2,w3,w4] [q6,q178,q231,q271] [n877] (by decide +kernel)
def n879 := cc 6 [w421,w162,w0,w2,w3,w4] [q202,q248,q262] [] (by decide +kernel)
def n880 := cc 7 [w162,w0,w2,w154,w3,w4] [q7,q13,q200,q246,q262] [n879,n877] (by decide +kernel)
def n881 := cc 7 [w86,w418,w0,w3,w4,w5] [] [] (by decide +kernel)
def n882 := cc 7 [w156,w271,w1,w2,w3,w4] [] [] (by decide +kernel)
def v1002 : Closed T 7 := rotateClosed n874 auto6 auto6ok
def v1003 : Closed T 7 := rotateClosed n881 auto6 auto6ok
def v1004 : Closed T 7 := rotateClosed n866 auto8 auto8ok
def v1005 : Closed T 7 := rotateClosed n882 auto8 auto8ok
def n883 := cc 8 [w162,w0,w2,w3,w4] [q171,q225] [v1002,v1003,v1004,n864,v1005,n872,n870,n878,n865,n875,n873,n880] (by decide +kernel)
def n884 := cc 7 [w409,w162,w0,w160,w2,w3,w4] [q6,q195,q207,q250,q262] [] (by decide +kernel)
def v1006 : Closed T 7 := rotateClosed n840 auto14 auto14ok
def v1007 : Closed T 7 := rotateClosed n698 auto14 auto14ok
def n885 := cc 8 [w162,w0,w160,w2,w3,w4] [q7,q13,q171,q225,q262] [v1006,v1007,n884,n725,n860,n664,n827,n683,n830] (by decide +kernel)
def n886 := cc 6 [w422,w191,w3,w4,w152] [q28,q115,q187] [] (by decide +kernel)
def n887 := cc 7 [w0,w422,w191,w3,w4,w5] [q0,q27,q114,q166] [n886] (by decide +kernel)
def v1008 : Closed T 6 := rotateClosed n877 auto14 auto14ok
def v1009 : Closed T 6 := rotateClosed n886 auto6 auto6ok
def n888 := cc 7 [w85,w160,w154,w3,w4,w161] [q6,q7,q41] [n877,v1008,v1009] (by decide +kernel)
def v1010 : Closed T 7 := rotateClosed n701 auto14 auto14ok
def v1011 : Closed T 7 := rotateClosed n887 auto6 auto6ok
def n889 := cc 8 [w85,w0,w160,w2,w3,w4,w161] [q178,q231,q262] [v1010,n878,n888,v1011] (by decide +kernel)
def v1012 : Closed T 7 := rotateClosed n880 auto14 auto14ok
def n890 := cc 8 [w85,w1,w154,w3,w4,w5,w161] [q6,q7,q67,q99,q141] [v1012,n888] (by decide +kernel)
def n891 := cc 8 [w86,w0,w158,w191,w3,w4,w5] [q0,q13,q83,q150] [] (by decide +kernel)
def n892 := cc 8 [w156,w233,w1,w2,w3,w4,w152] [q0,q13,q222,q258,q262] [] (by decide +kernel)
def v1013 : Closed T 8 := rotateClosed n891 auto8 auto8ok
def v1014 : Closed T 8 := rotateClosed n726 auto14 auto14ok
def v1015 : Closed T 8 := rotateClosed n892 auto6 auto6ok
def v1016 : Closed T 8 := rotateClosed n861 auto14 auto14ok
def v1017 : Closed T 8 := rotateClosed n885 auto14 auto14ok
def v1018 : Closed T 8 := rotateClosed n883 auto14 auto14ok
def v1019 : Closed T 8 := rotateClosed n889 auto14 auto14ok
def n893 := cc 9 [w85,w1,w154,w3,w4,w5] [q14,q103] [n841,v1013,n699,v1014,v1015,v1016,v1017,v1018,n665,n828,v1019,n684,n831,n890] (by decide +kernel)
def n894 := cc 7 [w409,w162,w0,w1,w2,w3,w4] [q6,q13,q207,q250,q271] [] (by decide +kernel)
def n895 := cc 7 [w411,w271,w0,w1,w2,w3,w4] [q13,q195,q243,q262] [] (by decide +kernel)
def n896 := cc 7 [w162,w0,w158,w2,w3,w4] [q13,q165,q185,q236] [] (by decide +kernel)
def n897 := cc 7 [w162,w0,w2,w191,w3,w4] [q6,q204,q249,q262,q271] [] (by decide +kernel)
def n898 := cc 7 [w86,w312,w1,w3,w4,w5] [q0,q83,q150,q262] [] (by decide +kernel)
def n899 := cc 7 [w156,w162,w0,w2,w3,w4] [q7,q222,q258,q262] [] (by decide +kernel)
def v1020 : Closed T 7 := rotateClosed n898 auto14 auto14ok
def v1021 : Closed T 7 := rotateClosed n895 auto8 auto8ok
def v1022 : Closed T 7 := rotateClosed n580 auto8 auto8ok
def n900 := cc 8 [w162,w0,w1,w2,w3,w4] [q7,q171,q225,q271] [v1020,v1021,n601,v1022,n894,n899,n307,n896,n383,n897] (by decide +kernel)
def n901 := cc 8 [w162,w0,w160,w1,w2,w3,w4] [q7,q171,q225,q271] [n727,n685] (by decide +kernel)
def v1023 : Closed T 7 := rotateClosed n896 auto8 auto8ok
def n902 := cc 8 [w85,w233,w1,w2,w3,w4,w152] [q178,q231,q271] [v1023] (by decide +kernel)
def n903 := cc 7 [w85,w1,w194,w3,w4,w152] [q59,q136,q262] [] (by decide +kernel)
def v1024 : Closed T 7 := rotateClosed n897 auto14 auto14ok
def n904 := cc 8 [w85,w1,w154,w3,w4,w5,w152] [q6,q7,q136,q181,q271] [v1024,n903,n732] (by decide +kernel)
def n905 := cc 7 [w86,w85,w1,w194,w3,w4] [q83,q150,q262] [] (by decide +kernel)
def n906 := cc 8 [w86,w85,w1,w154,w3,w4,w5] [q150,q181,q262] [n898,n905] (by decide +kernel)
def n907 := cc 8 [w156,w0,w160,w2,w3,w4,w161] [q7,q163,q222,q258] [n899] (by decide +kernel)
def n908 := cc 7 [w85,w1,w194,w183,w3,w4] [q59,q136,q262] [] (by decide +kernel)
def n909 := cc 8 [w85,w0,w1,w194,w3,w4] [q0,q14,q103,q262,q271] [n905,n908] (by decide +kernel)
def n910 := cc 8 [w85,w0,w1,w194,w3,w4,w5] [q6,q14,q103,q262] [n905,n903,n732] (by decide +kernel)
def v1025 : Closed T 8 := rotateClosed n594 auto8 auto8ok
def v1026 : Closed T 8 := rotateClosed n728 auto14 auto14ok
def v1027 : Closed T 8 := rotateClosed n736 auto8 auto8ok
def v1028 : Closed T 8 := rotateClosed n907 auto14 auto14ok
def v1029 : Closed T 8 := rotateClosed n901 auto14 auto14ok
def v1030 : Closed T 8 := rotateClosed n900 auto14 auto14ok
def v1031 : Closed T 8 := rotateClosed n902 auto6 auto6ok
def n911 := cc 9 [w85,w0,w1,w154,w3,w4,w5] [q6,q14,q103,q262] [n906,n581,v1025,v1026,v1027,v1028,v1029,v1030,n308,v1031,n686,n909,n910,n384,n904] (by decide +kernel)
def v1032 : Closed T 8 := rotateClosed n595 auto8 auto8ok
def v1033 : Closed T 8 := rotateClosed n713 auto11 auto11ok
def v1034 : Closed T 8 := rotateClosed n713 auto14 auto14ok
def v1035 : Closed T 8 := rotateClosed n752 auto12 auto12ok
def n912 := cc 9 [w85,w370,w0,w1,w2,w3,w4,w5] [q4,q6,q14,q271,q272] [v1032,v1033,v1034,v905,v1035] (by decide +kernel)
def v1036 : Closed T 8 := rotateClosed n714 auto3 auto3ok
def n913 := cc 9 [w156,w0,w274,w1,w2,w3,w4,w5] [q14,q222,q262,q270,q271,q272] [v1036] (by decide +kernel)
def n914 := cc 7 [w85,w233,w1,w183,w3,w4] [q3,q5,q262] [] (by decide +kernel)
def n915 := cc 8 [w85,w233,w0,w1,w42,w3,w4] [q3,q5,q14,q171,q262,q271] [n914] (by decide +kernel)
def v1037 : Closed T 8 := rotateClosed n818 auto14 auto14ok
def n916 := cc 9 [w85,w233,w0,w1,w2,w3,w4,w5] [q2,q4,q14,q171,q271] [v980,v1037,n835,n915,n902,v1031] (by decide +kernel)
def n917 := cc 8 [w423,w0,w1,w2,w3,w4,w5] [q7,q122,q163,q222] [] (by decide +kernel)
def v1038 : Closed T 7 := rotateClosed n674 auto14 auto14ok
def v1039 : Closed T 7 := rotateClosed n675 auto6 auto6ok
def n918 := cc 8 [w85,w0,w424,w1,w2,w3,w4,w5] [q6,q7,q178,q231] [v1038,v1039] (by decide +kernel)
def v1040 : Closed T 8 := rotateClosed n917 auto14 auto14ok
def v1041 : Closed T 8 := rotateClosed n676 auto8 auto8ok
def n919 := cc 9 [w85,w0,w1,w2,w3,w4,w5,w152] [q6,q13,q14,q59,q163,q178,q231,q271] [v1040,n902,n918,n833,n904,v1041] (by decide +kernel)
def n920 := cc 8 [w86,w166,w85,w1,w2,w3,w4] [q0,q6,q13,q178,q231] [v1023] (by decide +kernel)
def n921 := cc 7 [w86,w85,w1,w183,w3,w4] [q181,q233,q262] [] (by decide +kernel)
def n922 := cc 8 [w86,w85,w0,w1,w42,w3,w4] [q13,q178,q231,q262] [n921] (by decide +kernel)
def n923 := cc 9 [w86,w85,w0,w1,w2,w3,w4,w5] [q13,q14,q178,q231,q262] [n920,n853,n922,n906,n677,n835,n837] (by decide +kernel)
def n924 := cc 8 [w0,w1,w2,w426,w3,w4,w5] [q13,q214,q262] [] (by decide +kernel)
def v1042 : Closed T 8 := rotateClosed n924 auto6 auto6ok
def n925 := cc 9 [w156,w0,w160,w1,w2,w3,w4,w5] [q171,q262,q269,q270] [v1000,n907,v1042] (by decide +kernel)
def v1043 : Closed T 8 := rotateClosed n647 auto14 auto14ok
def v1044 : Closed T 8 := rotateClosed n667 auto8 auto8ok
def n926 := cc 9 [w85,w0,w158,w1,w2,w3,w4,w5] [q14,q103,q262,q271] [n22,v101,v845,v1043,n117,n667,v1044,n432] (by decide +kernel)
def n927 := cc 8 [w85,w212,w1,w2,w3,w4,w5] [q7,q88,q163] [] (by decide +kernel)
def v1045 : Closed T 8 := rotateClosed n712 auto14 auto14ok
def n928 := cc 9 [w156,w85,w0,w1,w2,w3,w4,w5] [q14,q103,q262,q271] [n393,n22,v1045,n668,n117,v873,n927,n23] (by decide +kernel)
def n929 := cc 6 [w0,w1,w427,w42,w41,w4,w5] [q111,q171,q262,q272] [] (by decide +kernel)
def n930 := cc 7 [w0,w1,w427,w42,w3,w4,w5] [q103,q186,q262,q272] [n929] (by decide +kernel)
def v1046 : Closed T 7 := rotateClosed n930 auto10 auto10ok
def n931 := cc 8 [w0,w1,w427,w2,w3,w4,w5] [q46,q186,q261,q262,q272] [n930,v1046] (by decide +kernel)
def n932 := cc 7 [w85,w0,w1,w428,w2,w41,w4,w5] [q119,q265,q271] [] (by decide +kernel)
def n933 := cc 8 [w85,w0,w1,w428,w2,w3,w4,w5] [q46,q119,q265,q267,q271] [n932] (by decide +kernel)
def n934 := cc 8 [w85,w0,w274,w1,w428,w2,w3,w4,w5] [q265,q271] [] (by decide +kernel)
def v1047 : Closed T 6 := rotateClosed n929 auto2 auto2ok
def n935 := cc 7 [w85,w0,w274,w1,w42,w41,w4,w5] [q118,q178,q265,q271] [v1047] (by decide +kernel)
def v1048 : Closed T 7 := rotateClosed n851 auto3 auto3ok
def v1049 : Closed T 7 := rotateClosed n804 auto10 auto10ok
def v1050 : Closed T 7 := rotateClosed n932 auto10 auto10ok
def v1051 : Closed T 7 := rotateClosed n930 auto8 auto8ok
def n936 := cc 8 [w85,w0,w274,w1,w42,w3,w4,w5] [q118,q171,q265,q267,q271] [v1048,v1049,n935,v1050,v1051] (by decide +kernel)
def v1052 : Closed T 8 := rotateClosed n721 auto1 auto1ok
def v1053 : Closed T 8 := rotateClosed n721 auto12 auto12ok
def v1054 : Closed T 8 := rotateClosed n704 auto1 auto1ok
def v1055 : Closed T 8 := rotateClosed n704 auto12 auto12ok
def v1056 : Closed T 8 := rotateClosed n852 auto3 auto3ok
def v1057 : Closed T 8 := rotateClosed n852 auto14 auto14ok
def v1058 : Closed T 8 := rotateClosed n805 auto10 auto10ok
def v1059 : Closed T 8 := rotateClosed n936 auto10 auto10ok
def v1060 : Closed T 8 := rotateClosed n933 auto10 auto10ok
def v1061 : Closed T 8 := rotateClosed n931 auto2 auto2ok
def n937 := cc 9 [w85,w0,w274,w1,w2,w3,w4,w5] [q7,q14,q118,q171,q262,q265,q267,q271,q272] [v1052,v1053,v1054,v1055,v1056,v1057,n40,n805,v1058,n934,n936,v1059,n933,v1060,v1061] (by decide +kernel)
def n938 := cc 8 [w0,w429,w1,w2,w3,w4,w5] [q10,q265,q271] [] (by decide +kernel)
def n939 := cc 7 [w431,w0,w1,w3,w4,w5] [q6,q7,q229] [] (by decide +kernel)
def v1062 : Closed T 7 := rotateClosed n939 auto12 auto12ok
def n940 := cc 8 [w433,w0,w1,w2,w3,w4,w5] [q2,q6,q88,q104] [v1062,v18] (by decide +kernel)
def n941 := cc 8 [w85,w0,w434,w1,w2,w3,w4,w5] [q169,q265,q270,q271] [] (by decide +kernel)
def v1063 : Closed T 8 := rotateClosed n679 auto1 auto1ok
def v1064 : Closed T 8 := rotateClosed n763 auto1 auto1ok
def v1065 : Closed T 8 := rotateClosed n940 auto4 auto4ok
def v1066 : Closed T 8 := rotateClosed n941 auto4 auto4ok
def v1067 : Closed T 8 := rotateClosed n938 auto2 auto2ok
def n942 := cc 9 [w156,w370,w0,w1,w2,w3,w4,w5] [q0,q14,q222,q262,q265,q272] [v1063,n493,v1064,v1065,v1066,v1067] (by decide +kernel)
def n943 := cc 7 [w0,w1,w422,w42,w3,w4] [q103,q262,q271,q276] [] (by decide +kernel)
def v1068 : Closed T 7 := rotateClosed n887 auto14 auto14ok
def n944 := cc 8 [w0,w1,w422,w2,w3,w4,w5] [q103,q169,q262,q271,q276] [n943,n887,v1068] (by decide +kernel)
def v1069 : Closed T 7 := rotateClosed n943 auto6 auto6ok
def n945 := cc 8 [w85,w0,w160,w1,w42,w3,w4] [q122,q178,q262,q269,q270,q276] [v1069] (by decide +kernel)
def v1070 : Closed T 8 := rotateClosed n702 auto14 auto14ok
def v1071 : Closed T 8 := rotateClosed n944 auto6 auto6ok
def n946 := cc 9 [w85,w0,w160,w1,w2,w3,w4,w5] [q262,q271,q276,q277] [n702,v1070,n54,n945,n889,v1019,v1071] (by decide +kernel)
def n947 := cc 7 [w437,w0,w1,w3,w4,w5] [q7,q11,q193] [] (by decide +kernel)
def v1072 : Closed T 7 := rotateClosed n947 auto12 auto12ok
def v1073 : Closed T 7 := rotateClosed n947 auto13 auto13ok
def n948 := cc 8 [w438,w0,w1,w2,w3,w4,w5] [q0,q178,q231,q271] [v1072,v1073,n408] (by decide +kernel)
def n949 := cc 8 [w439,w0,w1,w2,w3,w4,w5] [q7,q37,q122,q163,q166,q207] [] (by decide +kernel)
def n950 := cc 7 [w85,w1,w440,w3,w4,w5] [q181,q233,q262] [] (by decide +kernel)
def v1074 : Closed T 7 := rotateClosed n706 auto14 auto14ok
def v1075 : Closed T 7 := rotateClosed n847 auto14 auto14ok
def n951 := cc 8 [w85,w0,w1,w276,w3,w4,w5] [q6,q178,q231,q271] [v1074,v1075,n950,n670] (by decide +kernel)
def v1076 : Closed T 8 := rotateClosed n707 auto14 auto14ok
def v1077 : Closed T 8 := rotateClosed n848 auto14 auto14ok
def v1078 : Closed T 8 := rotateClosed n949 auto14 auto14ok
def n952 := cc 9 [w85,w0,w1,w2,w3,w4,w5,w161] [q6,q14,q178,q231,q271] [v1076,v1077,v1078,n948,n889,n951,n890,n671] (by decide +kernel)
def n953 := cc 8 [w442,w0,w1,w2,w3,w4,w5] [q6,q178,q271] [] (by decide +kernel)
def n954 := cc 8 [w443,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q178,q231] [v22] (by decide +kernel)
def n955 := cc 7 [w85,w1,w445,w3,w4,w5] [q6,q7,q181] [] (by decide +kernel)
def v1079 : Closed T 7 := rotateClosed n708 auto14 auto14ok
def n956 := cc 8 [w85,w0,w1,w444,w3,w4,w5] [q6,q7,q178,q231] [v1079,n955] (by decide +kernel)
def n957 := cc 8 [w86,w0,w158,w1,w42,w3,w4] [q13,q150,q185,q262] [n710] (by decide +kernel)
def v1080 : Closed T 8 := rotateClosed n954 auto8 auto8ok
def v1081 : Closed T 8 := rotateClosed n956 auto8 auto8ok
def v1082 : Closed T 8 := rotateClosed n953 auto8 auto8ok
def n958 := cc 9 [w86,w0,w158,w1,w2,w3,w4,w5] [q13,q14,q185,q236,q262] [n711,n957,n891,n672,v1080,v1081,v1082] (by decide +kernel)
def n959 := cc 8 [w0,w446,w1,w2,w3,w4,w5] [q262,q273] [] (by decide +kernel)
def n960 := cc 8 [w447,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q88,q171] [v23] (by decide +kernel)
def v1083 : Closed T 8 := rotateClosed n960 auto6 auto6ok
def v1084 : Closed T 8 := rotateClosed n959 auto6 auto6ok
def n961 := cc 9 [w156,w233,w0,w1,w2,w3,w4,w5] [q14,q262,q271,q276,q277] [n681,n496,n849,n892,v1083,v1084] (by decide +kernel)
def n962 := cc 7 [w448,w0,w160,w2,w3,w4] [q7,q163,q222,q258] [] (by decide +kernel)
def n963 := cc 6 [w86,w449,w1,w3,w4] [] [] (by decide +kernel)
def v1085 : Closed T 6 := rotateClosed n963 auto14 auto14ok
def n964 := cc 7 [w448,w0,w2,w209,w3,w4] [q271,q272] [v1085] (by decide +kernel)
def n965 := cc 7 [w85,w450,w1,w183,w3,w4,w5] [q265,q271] [] (by decide +kernel)
def v1086 : Closed T 7 := rotateClosed n962 auto14 auto14ok
def v1087 : Closed T 7 := rotateClosed n964 auto14 auto14ok
def n966 := cc 8 [w85,w1,w183,w3,w4,w5] [q136,q181,q262,q265,q271] [n921,v1086,v1087,n965,n908] (by decide +kernel)
def n967 := cc 7 [w448,w0,w1,w2,w3,w4] [q7,q163,q222,q258] [v1085] (by decide +kernel)
def v1088 : Closed T 7 := rotateClosed n967 auto14 auto14ok
def n968 := cc 8 [w85,w0,w1,w183,w3,w4,w5] [q6,q14,q262,q265] [n921,v1088,n914] (by decide +kernel)
def n969 := cc 8 [w85,w1,w42,w183,w3,w4,w5] [q136,q262,q265,q271,q276] [] (by decide +kernel)
def v1089 : Closed T 7 := rotateClosed n732 auto2 auto2ok
def n970 := cc 8 [w221,w370,w1,w2,w41,w4,w5] [q261,q265,q268] [v1089] (by decide +kernel)
def n971 := cc 7 [w0,w1,w42,w2,w3,w451,w4] [q7,q116,q260,q265,q276] [] (by decide +kernel)
def n972 := cc 7 [w0,w1,w42,w2,w452,w41,w4,w5] [q59,q112,q262,q275] [] (by decide +kernel)
def n973 := cc 7 [w221,w0,w158,w1,w42,w3,w4,w5] [q0,q212,q272] [] (by decide +kernel)
def v1090 : Closed T 7 := rotateClosed n973 auto8 auto8ok
def v1091 : Closed T 7 := rotateClosed n935 auto1 auto1ok
def v1092 : Closed T 7 := rotateClosed n972 auto2 auto2ok
def v1093 : Closed T 7 := rotateClosed n971 auto6 auto6ok
def n974 := cc 8 [w85,w0,w1,w42,w41,w3,w4,w5] [q14,q103,q171,q265,q267,q271,q273,q276] [v1090,v1049,n935,v1091,v1092,v1093] (by decide +kernel)
def v1094 : Closed T 8 := rotateClosed n957 auto8 auto8ok
def v1095 : Closed T 8 := rotateClosed n970 auto2 auto2ok
def v1096 : Closed T 8 := rotateClosed n715 auto14 auto14ok
def v1097 : Closed T 8 := rotateClosed n733 auto8 auto8ok
def v1098 : Closed T 8 := rotateClosed n862 auto14 auto14ok
def v1099 : Closed T 8 := rotateClosed n936 auto1 auto1ok
def n975 := cc 9 [w85,w0,w1,w42,w3,w4,w5] [q14,q103,q171,q262,q267,q271,q276,q277] [n922,v1094,v1095,v1096,v1097,v1098,n60,n915,n936,v1099,n945,n974,n832,n833,n968,n969,n966] (by decide +kernel)
def n976 := cc 8 [w85,w1,w2,w183,w3,w4,w5] [q59,q262,q271] [] (by decide +kernel)
def v1100 : Closed T 8 := rotateClosed n737 auto8 auto8ok
def v1101 : Closed T 8 := rotateClosed n854 auto14 auto14ok
def n977 := cc 9 [w85,w0,w1,w42,w2,w3,w4,w5] [q14,q103,q171,q262,q271] [v978,v1100,v1101,n835,n976] (by decide +kernel)
def n978 := cc 8 [w85,w453,w1,w2,w3,w4,w5] [q6,q95,q156] [] (by decide +kernel)
def n979 := cc 8 [w85,w0,w1,w42,w3,w4,w5] [q13,q103,q178,q262] [n732] (by decide +kernel)
def v1102 : Closed T 8 := rotateClosed n855 auto8 auto8ok
def n980 := cc 9 [w43,w85,w0,w1,w2,w3,w4,w5] [q103,q178,q262,q271] [v1102,n835,n836,n979,n978,n738] (by decide +kernel)
def n981 := cc 8 [w85,w0,w454,w1,w3,w4,w5] [q0,q14,q271] [] (by decide +kernel)
def n982 := cc 8 [w85,w0,w455,w1,w3,w4,w5] [q0,q6,q14,q103] [] (by decide +kernel)
def v1103 : Closed T 8 := rotateClosed n716 auto8 auto8ok
def v1104 : Closed T 8 := rotateClosed n981 auto6 auto6ok
def v1105 : Closed T 8 := rotateClosed n982 auto6 auto6ok
def v1106 : Closed T 8 := rotateClosed n979 auto6 auto6ok
def n983 := cc 9 [w43,w233,w0,w1,w2,w3,w4] [q0,q113,q171,q225,q262,q271] [v1103,n62,v1104,v1105,v1106] (by decide +kernel)
def n984 := cc 5 [w458,w0,w2,w3,w4,w5] [] [] (by decide +kernel)
def v1107 : Closed T 5 := rotateClosed n984 auto11 auto11ok
def n985 := cc 6 [w460,w1,w2,w461,w3,w4,w5] [] [v1107] (by decide +kernel)
def n986 := cc 7 [w460,w0,w1,w2,w459,w3,w4,w5] [q0,q68,q89,q120,q271,q275] [n985] (by decide +kernel)
def v1108 : Closed T 6 := rotateClosed n985 auto8 auto8ok
def n987 := cc 7 [w0,w1,w2,w452,w462,w3,w4,w5] [q59,q91,q112,q200,q262,q271,q275] [v1108] (by decide +kernel)
def v1109 : Closed T 5 := rotateClosed n984 auto8 auto8ok
def n988 := cc 6 [w463,w464,w1,w2,w3,w4,w5] [] [v1109] (by decide +kernel)
def n989 := cc 7 [w463,w0,w1,w2,w3,w329,w4,w5] [q0,q198] [n988] (by decide +kernel)
def v1110 : Closed T 6 := rotateClosed n988 auto11 auto11ok
def n990 := cc 7 [w465,w0,w1,w2,w452,w3,w4,w5] [q60,q271] [v1110] (by decide +kernel)
def v1111 : Closed T 7 := rotateClosed n989 auto11 auto11ok
def v1112 : Closed T 7 := rotateClosed n986 auto8 auto8ok
def v1113 : Closed T 7 := rotateClosed n971 auto3 auto3ok
def n991 := cc 8 [w0,w1,w2,w452,w3,w4,w5] [q6,q7,q59,q235,q261,q262,q271,q275] [v1111,n990,v1112,v1113,n987] (by decide +kernel)
def v1114 : Closed T 7 := rotateClosed n729 auto14 auto14ok
def n992 := cc 8 [w85,w0,w1,w2,w3,w466,w4,w5] [q7,q135,q265,q267,q271] [v1114,v869] (by decide +kernel)
def n993 := cc 7 [w0,w1,w2,w452,w209,w3,w4,w5] [q0,q7,q61,q262,q271,q275] [] (by decide +kernel)
def n994 := cc 7 [w221,w0,w1,w2,w3,w307,w4,w5] [q0,q265] [] (by decide +kernel)
def v1115 : Closed T 7 := rotateClosed n994 auto10 auto10ok
def n995 := cc 8 [w0,w1,w42,w2,w452,w3,w4,w5] [q7,q59,q112,q200,q262,q271,q275] [v1115,n972,n993] (by decide +kernel)
def n996 := cc 8 [w85,w0,w1,w2,w41,w3,w466,w4,w5] [q2,q56,q265] [] (by decide +kernel)
def n997 := cc 8 [w467,w0,w1,w2,w3,w4,w5] [q0,q79,q148,q271] [] (by decide +kernel)
def n998 := cc 7 [w467,w468,w0,w1,w2,w3,w4,w5] [q7,q272] [] (by decide +kernel)
def n999 := cc 8 [w467,w0,w1,w2,w41,w3,w4,w5] [q10,q56,q148,q265,q267,q271,q272] [n998] (by decide +kernel)
def n1000 := cc 7 [w469,w0,w1,w42,w2,w3,w4,w5] [q32,q36,q138,q145,q146,q193] [] (by decide +kernel)
def v1116 : Closed T 7 := rotateClosed n718 auto14 auto14ok
def v1117 : Closed T 7 := rotateClosed n1000 auto12 auto12ok
def v1118 : Closed T 7 := rotateClosed n993 auto2 auto2ok
def n1001 := cc 8 [w85,w0,w1,w2,w41,w3,w470,w4,w5] [q2,q65,q84,q140,q265,q271,q272,q276] [v1116,v1117,v1118] (by decide +kernel)
def n1002 := cc 7 [w85,w471,w0,w1,w2,w3,w4,w5] [q85,q90] [] (by decide +kernel)
def v1119 : Closed T 7 := rotateClosed n856 auto6 auto6ok
def v1120 : Closed T 7 := rotateClosed n1002 auto8 auto8ok
def n1003 := cc 8 [w221,w0,w158,w1,w2,w3,w4,w5] [q0,q7,q148,q166,q185,q212,q265,q272] [v1119,n808,n973,n689,v1120] (by decide +kernel)
def v1121 : Closed T 7 := rotateClosed n998 auto8 auto8ok
def n1004 := cc 8 [w221,w0,w158,w1,w2,w41,w3,w4,w5] [q56,q148,q260,q265,q272] [v1121,n994] (by decide +kernel)
def v1122 : Closed T 8 := rotateClosed n1004 auto8 auto8ok
def v1123 : Closed T 8 := rotateClosed n1003 auto8 auto8ok
def v1124 : Closed T 8 := rotateClosed n730 auto14 auto14ok
def v1125 : Closed T 8 := rotateClosed n719 auto14 auto14ok
def v1126 : Closed T 8 := rotateClosed n857 auto14 auto14ok
def v1127 : Closed T 8 := rotateClosed n768 auto12 auto12ok
def v1128 : Closed T 8 := rotateClosed n761 auto12 auto12ok
def v1129 : Closed T 8 := rotateClosed n769 auto12 auto12ok
def v1130 : Closed T 8 := rotateClosed n769 auto13 auto13ok
def v1131 : Closed T 8 := rotateClosed n766 auto12 auto12ok
def v1132 : Closed T 8 := rotateClosed n766 auto13 auto13ok
def v1133 : Closed T 8 := rotateClosed n936 auto11 auto11ok
def v1134 : Closed T 8 := rotateClosed n995 auto2 auto2ok
def v1135 : Closed T 8 := rotateClosed n991 auto2 auto2ok
def n1005 := cc 9 [w85,w0,w1,w2,w41,w3,w4,w5] [q4,q14,q103,q231,q262,q265,q267,q271,q272,q276] [n999,n997,v1122,v1123,v1124,v1125,v1126,v1127,v1128,v1129,v1130,v1131,v1132,n65,n749,v1058,n809,v1059,v1133,n691,n974,n996,n1001,n992,v1134,v1135] (by decide +kernel)
def v1136 : Closed T 8 := rotateClosed n757 auto14 auto14ok
def n1006 := cc 9 [w85,w0,w1,w2,w472,w3,w4,w5] [q14,q127,q178,q262,q265,q271] [v1136,v903] (by decide +kernel)
def n1007 := cc 8 [w473,w0,w1,w2,w3,w4,w5] [q6,q7,q95,q231,q271] [] (by decide +kernel)
def n1008 := cc 7 [w475,w0,w1,w3,w4,w5] [q7,q193,q241] [] (by decide +kernel)
def v1137 : Closed T 7 := rotateClosed n1008 auto12 auto12ok
def n1009 := cc 8 [w476,w0,w1,w2,w3,w4,w5] [q0,q113,q178,q271] [v1137,v909] (by decide +kernel)
def n1010 := cc 7 [w85,w1,w477,w3,w4,w5] [q136,q181,q262] [] (by decide +kernel)
def v1138 : Closed T 7 := rotateClosed n764 auto13 auto13ok
def n1011 := cc 8 [w85,w0,w1,w113,w3,w4,w5] [q6,q103,q178,q271] [v1138,n1010] (by decide +kernel)
def v1139 : Closed T 8 := rotateClosed n765 auto8 auto8ok
def v1140 : Closed T 8 := rotateClosed n1009 auto1 auto1ok
def v1141 : Closed T 8 := rotateClosed n1011 auto1 auto1ok
def n1012 := cc 9 [w74,w85,w0,w1,w2,w3,w4,w5] [q6,q13,q14,q231,q272,q276] [v1139,v1140,v1141,n1007] (by decide +kernel)
def v1142 : Closed T 9 := rotateClosed n958 auto8 auto8ok
def v1143 : Closed T 9 := rotateClosed n983 auto6 auto6ok
def v1144 : Closed T 9 := rotateClosed n1012 auto1 auto1ok
def v1145 : Closed T 9 := rotateClosed n596 auto8 auto8ok
def v1146 : Closed T 9 := rotateClosed n731 auto14 auto14ok
def v1147 : Closed T 9 := rotateClosed n720 auto14 auto14ok
def v1148 : Closed T 9 := rotateClosed n942 auto2 auto2ok
def v1149 : Closed T 9 := rotateClosed n942 auto3 auto3ok
def v1150 : Closed T 9 := rotateClosed n961 auto6 auto6ok
def v1151 : Closed T 9 := rotateClosed n740 auto8 auto8ok
def v1152 : Closed T 9 := rotateClosed n735 auto8 auto8ok
def v1153 : Closed T 9 := rotateClosed n913 auto10 auto10ok
def v1154 : Closed T 9 := rotateClosed n913 auto11 auto11ok
def v1155 : Closed T 9 := rotateClosed n925 auto14 auto14ok
def v1156 : Closed T 9 := rotateClosed n739 auto8 auto8ok
def v1157 : Closed T 9 := rotateClosed n863 auto14 auto14ok
def v1158 : Closed T 9 := rotateClosed n858 auto14 auto14ok
def v1159 : Closed T 9 := rotateClosed n770 auto12 auto12ok
def v1160 : Closed T 9 := rotateClosed n770 auto13 auto13ok
def v1161 : Closed T 9 := rotateClosed n767 auto12 auto12ok
def v1162 : Closed T 9 := rotateClosed n767 auto13 auto13ok
def v1163 : Closed T 9 := rotateClosed n753 auto1 auto1ok
def v1164 : Closed T 9 := rotateClosed n751 auto1 auto1ok
def v1165 : Closed T 9 := rotateClosed n912 auto1 auto1ok
def v1166 : Closed T 9 := rotateClosed n937 auto1 auto1ok
def v1167 : Closed T 9 := rotateClosed n1006 auto1 auto1ok
def v1168 : Closed T 9 := rotateClosed n682 auto8 auto8ok
def n1013 := cc 10 [w85,w0,w1,w2,w3,w4,w5] [q14,q103,q171] [n842,n923,v1142,n980,v1143,n1012,v1144,n700,n498,n582,v1145,v1146,v1147,n928,v1148,v1149,v1150,v1151,v1152,v1153,v1154,v1155,v1156,v1157,v1158,v1159,v1160,v1161,v1162,n666,n66,n309,n753,v1163,n751,v1164,n829,n810,n912,v1165,n916,n926,n937,v1166,n946,n692,n386,n977,n975,n1005,n1006,v1167,n834,n919,n952,n911,n893,v1168] (by decide +kernel)
def n1014 := cc 8 [w193,w0,w1,w2,w3,w4,w5,w152] [q7,q136,q202,q262,q271] [] (by decide +kernel)
def n1015 := cc 7 [w0,w1,w153,w194,w3,w4] [q59,q136,q262] [] (by decide +kernel)
def v1169 : Closed T 7 := rotateClosed n903 auto6 auto6ok
def n1016 := cc 8 [w0,w1,w153,w154,w3,w4,w5] [q13,q59,q136,q171,q262,q271] [v1169,n1015] (by decide +kernel)
def v1170 : Closed T 7 := rotateClosed n732 auto6 auto6ok
def n1017 := cc 8 [w0,w1,w2,w183,w3,w4,w5] [q7,q59,q136,q171,q262,q271] [n732,v1170] (by decide +kernel)
def v1171 : Closed T 8 := rotateClosed n1014 auto6 auto6ok
def v1172 : Closed T 8 := rotateClosed n904 auto6 auto6ok
def v1173 : Closed T 8 := rotateClosed n1016 auto6 auto6ok
def n1018 := cc 9 [w0,w1,w2,w154,w3,w4,w5,w152] [q7,q13,q59,q136,q171,q262] [n583,n1014,v1171,n904,v1172,n1016,v1173,n1017] (by decide +kernel)
def n1019 := cc 8 [w86,w193,w0,w1,w2,w3,w4,w5] [q150,q202,q262] [] (by decide +kernel)
def n1020 := cc 8 [w86,w0,w1,w2,w194,w3,w4] [q0,q150,q200,q262] [n905] (by decide +kernel)
def v1174 : Closed T 8 := rotateClosed n924 auto14 auto14ok
def n1021 := cc 9 [w86,w0,w1,w2,w154,w3,w4,w5] [q0,q13,q150,q200,q262] [n1019,n906,n1020,v1174] (by decide +kernel)
def n1022 := cc 7 [w0,w479,w1,w2,w3,w4,w5] [q13,q55,q100,q161] [] (by decide +kernel)
def v1175 : Closed T 7 := rotateClosed n1022 auto6 auto6ok
def n1023 := cc 8 [w0,w212,w1,w2,w3,w4,w5,w161] [q7,q223,q259,q262] [v1175] (by decide +kernel)
def n1024 := cc 7 [w331,w0,w1,w194,w3,w4] [q6,q95,q156,q166] [] (by decide +kernel)
def n1025 := cc 8 [w331,w0,w1,w154,w3,w4,w5] [q6,q95,q156] [v1088,n1024] (by decide +kernel)
def n1026 := cc 8 [w156,w480,w0,w1,w2,w3,w4,w5] [q0,q88,q222,q258,q262] [] (by decide +kernel)
def n1027 := cc 8 [w86,w166,w1,w2,w154,w3,w4] [] [] (by decide +kernel)
def v1176 : Closed T 7 := rotateClosed n1024 auto14 auto14ok
def n1028 := cc 8 [w156,w0,w1,w276,w3,w4,w5] [q67,q222,q258,q262] [v1176] (by decide +kernel)
def v1177 : Closed T 8 := rotateClosed n1027 auto14 auto14ok
def v1178 : Closed T 8 := rotateClosed n1025 auto14 auto14ok
def n1029 := cc 9 [w156,w0,w1,w2,w3,w4,w5,w161] [q6,q14,q222,q258,q262,q271] [v1177,n737,n1026,n907,n1028,v1178,n1023] (by decide +kernel)
def n1030 := cc 8 [w481,w0,w1,w2,w3,w4,w5] [q7,q163,q222,q258] [] (by decide +kernel)
def v1179 : Closed T 8 := rotateClosed n584 auto8 auto8ok
def v1180 : Closed T 8 := rotateClosed n1026 auto6 auto6ok
def v1181 : Closed T 8 := rotateClosed n1030 auto14 auto14ok
def v1182 : Closed T 8 := rotateClosed n948 auto6 auto6ok
def v1183 : Closed T 8 := rotateClosed n918 auto14 auto14ok
def n1031 := cc 9 [w192,w0,w1,w2,w3,w4,w5] [q6,q14,q103,q171] [n22,n513,v1179,v594,v1180,v1181,n4,v1182,v1183,n673,n388,n387,v480] (by decide +kernel)
def n1032 := cc 8 [w483,w0,w1,w2,w3,w4,w5] [q13,q204,q222,q258,q262] [] (by decide +kernel)
def n1033 := cc 8 [w485,w0,w1,w2,w3,w4,w5] [q6,q88,q163,q166,q178,q231] [] (by decide +kernel)
def v1184 : Closed T 8 := rotateClosed n597 auto8 auto8ok
def v1185 : Closed T 8 := rotateClosed n1032 auto6 auto6ok
def v1186 : Closed T 8 := rotateClosed n1033 auto14 auto14ok
def n1034 := cc 9 [w193,w0,w1,w2,w3,w4,w5] [q7,q14,q103,q171,q271] [n1019,n393,v1184,n2,v1185,n1014,n389,n4,v1186,n437] (by decide +kernel)
def n1035 := cc 7 [w0,w1,w153,w486,w3,w4] [q7,q59,q136,q262] [] (by decide +kernel)
def n1036 := cc 8 [w0,w1,w153,w191,w3,w4,w5] [q0,q6,q13,q59,q136,q204,q262] [n1035] (by decide +kernel)
def n1037 := cc 8 [w0,w1,w2,w487,w3,w4,w5] [q6,q7,q67,q141,q200,q262] [] (by decide +kernel)
def v1187 : Closed T 8 := rotateClosed n890 auto14 auto14ok
def v1188 : Closed T 8 := rotateClosed n1036 auto6 auto6ok
def v1189 : Closed T 8 := rotateClosed n1036 auto8 auto8ok
def n1038 := cc 9 [w0,w1,w2,w154,w3,w4,w5,w161] [q0,q6,q7,q13,q67,q141,q200,q262,q271] [n890,v1187,v1188,v1189,n1037] (by decide +kernel)
def n1039 := cc 8 [w0,w1,w2,w488,w3,w4,w5] [q0,q13,q59,q95,q136,q171] [] (by decide +kernel)
def n1040 := cc 8 [w86,w0,w1,w2,w486,w3,w4] [q150,q204,q262] [] (by decide +kernel)
def v1190 : Closed T 8 := rotateClosed n1039 auto14 auto14ok
def n1041 := cc 9 [w86,w0,w1,w2,w191,w3,w4,w5] [q0,q7,q13,q150,q204,q222,q271] [n891,n1040,v1190] (by decide +kernel)
def n1042 := cc 8 [w489,w0,w1,w2,w3,w4,w5] [q6,q95,q156,q166] [] (by decide +kernel)
def n1043 := cc 7 [w491,w492,w1,w2,w3,w5] [q4,q82,q213] [] (by decide +kernel)
def v1191 : Closed T 7 := rotateClosed n1043 auto12 auto12ok
def n1044 := cc 8 [w156,w0,w1,w153,w3,w4,w5] [q7,q59,q222,q258,q262] [v1191] (by decide +kernel)
def v1192 : Closed T 8 := rotateClosed n1042 auto14 auto14ok
def n1045 := cc 9 [w156,w0,w1,w2,w3,w4,w5,w152] [q7,q13,q14,q59,q222,q258,q262,q271] [n1032,n892,n1044,v1192] (by decide +kernel)
def v1193 : Closed T 7 := rotateClosed n908 auto6 auto6ok
def n1046 := cc 8 [w0,w1,w153,w183,w3,w4,w5] [q13,q200,q246,q262,q271] [v1193,n732,n1015] (by decide +kernel)
def n1047 := cc 8 [w168,w0,w1,w276,w3,w4,w5] [q13,q204,q222,q258,q262] [v1176] (by decide +kernel)
def n1048 := cc 7 [w0,w203,w276,w3,w4,w5] [q179,q232,q262] [] (by decide +kernel)
def n1049 := cc 7 [w437,w0,w1,w3,w493,w5] [q10,q262] [] (by decide +kernel)
def n1050 := cc 6 [w495,w0,w2,w3,w5] [q265,q269,q272] [] (by decide +kernel)
def v1194 : Closed T 6 := rotateClosed n1050 auto12 auto12ok
def n1051 := cc 7 [w438,w1,w440,w3,w4,w5] [q181,q233,q262] [v1194] (by decide +kernel)
def v1195 : Closed T 7 := rotateClosed n1049 auto12 auto12ok
def v1196 : Closed T 7 := rotateClosed n1049 auto13 auto13ok
def n1052 := cc 8 [w438,w0,w1,w276,w3,w4,w5] [q6,q178,q231,q271] [v1074,v1075,v1195,v1196,n1051,n1048] (by decide +kernel)
def v1197 : Closed T 7 := rotateClosed n1051 auto8 auto8ok
def n1053 := cc 8 [w0,w1,w153,w496,w3,w4,w5] [q6,q204,q249,q262,q271] [v1197,n1035] (by decide +kernel)
def v1198 : Closed T 6 := rotateClosed n1050 auto8 auto8ok
def n1054 := cc 7 [w491,w497,w1,w2,w3,w5] [q82,q213,q265] [v1198] (by decide +kernel)
def n1055 := cc 8 [w491,w0,w1,w2,w3,w490,w5] [q2,q79,q212,q265] [n1054] (by decide +kernel)
def v1199 : Closed T 7 := rotateClosed n1054 auto12 auto12ok
def n1056 := cc 8 [w483,w0,w1,w153,w3,w4,w5] [q13,q204,q222,q258,q262] [v1199] (by decide +kernel)
def v1200 : Closed T 8 := rotateClosed n1020 auto6 auto6ok
def v1201 : Closed T 8 := rotateClosed n1055 auto12 auto12ok
def v1202 : Closed T 8 := rotateClosed n598 auto8 auto8ok
def v1203 : Closed T 8 := rotateClosed n1047 auto8 auto8ok
def v1204 : Closed T 8 := rotateClosed n1052 auto8 auto8ok
def v1205 : Closed T 8 := rotateClosed n909 auto6 auto6ok
def n1057 := cc 9 [w0,w1,w153,w3,w4,w5] [q171,q225] [v1200,v1201,n585,v1202,v1203,n1056,n312,v1204,n833,v1205,n394,n1046,n1053] (by decide +kernel)
def n1058 := cc 8 [w0,w1,w2,w440,w3,w4,w5] [q14,q200,q246,q262,q271] [n950] (by decide +kernel)
def n1059 := cc 8 [w491,w0,w1,w2,w3,w4,w5] [q0,q212,q265] [n1043] (by decide +kernel)
def v1206 : Closed T 8 := rotateClosed n1040 auto14 auto14ok
def v1207 : Closed T 8 := rotateClosed n1059 auto12 auto12ok
def v1208 : Closed T 8 := rotateClosed n1028 auto8 auto8ok
def v1209 : Closed T 8 := rotateClosed n948 auto8 auto8ok
def v1210 : Closed T 8 := rotateClosed n951 auto8 auto8ok
def v1211 : Closed T 8 := rotateClosed n910 auto6 auto6ok
def v1212 : Closed T 8 := rotateClosed n1058 auto8 auto8ok
def n1060 := cc 9 [w0,w1,w153,w2,w3,w4,w5] [q14,q171,q225,q262,q271] [v1200,v1206,v1207,v1100,n1032,n1044,v1208,n313,v1209,n833,v1210,v1211,n1016,n1036,n1017,v1212] (by decide +kernel)
def n1061 := cc 9 [w155,w0,w1,w2,w3,w4] [q14,q103,q171] [n586,n599,n314,n395] (by decide +kernel)
def v1213 : Closed T 9 := rotateClosed n1041 auto8 auto8ok
def v1214 : Closed T 9 := rotateClosed n600 auto8 auto8ok
def v1215 : Closed T 9 := rotateClosed n1045 auto6 auto6ok
def v1216 : Closed T 9 := rotateClosed n1029 auto14 auto14ok
def v1217 : Closed T 9 := rotateClosed n919 auto6 auto6ok
def v1218 : Closed T 9 := rotateClosed n952 auto14 auto14ok
def v1219 : Closed T 9 := rotateClosed n1031 auto8 auto8ok
def v1220 : Closed T 9 := rotateClosed n1060 auto6 auto6ok
def v1221 : Closed T 9 := rotateClosed n1057 auto6 auto6ok
def n1062 := cc 10 [w0,w1,w2,w154,w3,w4,w5] [q14,q103,q171] [n1021,v1213,n1061,n587,v1214,v1156,v1215,v1216,n1034,n315,v1217,v1218,n911,n893,v1219,n396,v1220,v1221,n1018,n1038] (by decide +kernel)
def n1063 := cc 9 [w85,w0,w1,w2,w3,w4,w5] [q0,q14,q103,q178,q262,q271] [n22,v39,v1027,v957,n117,n835,n979,v480] (by decide +kernel)
def n1064 := cc 8 [w499,w0,w1,w2,w3,w4,w5] [q6,q7,q46,q178,q219,q231] [] (by decide +kernel)
def n1065 := cc 8 [w500,w0,w1,w2,w3,w4,w5] [q0,q13,q222,q258,q262] [] (by decide +kernel)
def v1222 : Closed T 8 := rotateClosed n22 auto14 auto14ok
def v1223 : Closed T 8 := rotateClosed n514 auto8 auto8ok
def v1224 : Closed T 8 := rotateClosed n1065 auto8 auto8ok
def v1225 : Closed T 8 := rotateClosed n316 auto8 auto8ok
def v1226 : Closed T 8 := rotateClosed n127 auto8 auto8ok
def n1066 := cc 9 [w0,w498,w1,w2,w3,w4,w5] [q6,q14,q171,q225,q262,q271] [v1222,n2,v1223,v1224,v1225,v1226,n1064,n21] (by decide +kernel)
def n1067 := cc 8 [w502,w0,w1,w2,w3,w4,w5] [q7,q163,q222,q258] [] (by decide +kernel)
def n1068 := cc 8 [w63,w0,w1,w42,w3,w4,w5] [q6,q14,q103,q171,q271] [] (by decide +kernel)
def v1227 : Closed T 8 := rotateClosed n589 auto8 auto8ok
def v1228 : Closed T 8 := rotateClosed n588 auto8 auto8ok
def v1229 : Closed T 8 := rotateClosed n1067 auto14 auto14ok
def v1230 : Closed T 8 := rotateClosed n954 auto6 auto6ok
def n1069 := cc 9 [w63,w0,w1,w2,w3,w4,w5] [q6,q14,q103,q171,q271] [v1227,v1228,n2,v39,v1229,n117,n118,v1230,n1068,n21] (by decide +kernel)
def n1070 := cc 8 [w0,w1,w2,w445,w3,w4,w5] [q6,q7,q14,q200,q219,q246] [n955] (by decide +kernel)
def n1071 := cc 8 [w505,w0,w1,w2,w3,w4,w5] [q0,q11,q79,q212] [] (by decide +kernel)
def n1072 := cc 8 [w86,w0,w1,w2,w506,w3,w4] [q0,q13,q83,q103] [] (by decide +kernel)
def n1073 := cc 8 [w86,w0,w1,w2,w320,w3,w4] [q0,q150,q210,q262] [] (by decide +kernel)
def v1231 : Closed T 8 := rotateClosed n1072 auto6 auto6ok
def v1232 : Closed T 8 := rotateClosed n1073 auto14 auto14ok
def v1233 : Closed T 8 := rotateClosed n1071 auto4 auto4ok
def v1234 : Closed T 8 := rotateClosed n774 auto10 auto10ok
def v1235 : Closed T 8 := rotateClosed n837 auto8 auto8ok
def n1074 := cc 9 [w0,w1,w444,w2,w3,w4,w5] [q7,q14,q171,q225,q262,q271] [v1231,v1232,v1233,v1234,v1224,v997,n954,n956,v1235,n1070] (by decide +kernel)
def n1075 := cc 8 [w86,w319,w197,w1,w3,w4,w5] [q150,q211,q262] [n898] (by decide +kernel)
def n1076 := cc 8 [w86,w319,w0,w1,w42,w3,w4] [q0,q83,q150,q262] [] (by decide +kernel)
def v1236 : Closed T 8 := rotateClosed n1073 auto6 auto6ok
def n1077 := cc 9 [w86,w319,w0,w1,w2,w3,w4,w5] [q0,q83,q150,q210,q262] [n1075,n1076,n1073,v1236,v950] (by decide +kernel)
def v1237 : Closed T 7 := rotateClosed n967 auto8 auto8ok
def n1078 := cc 8 [w86,w507,w0,w1,w2,w3,w4] [q0,q163,q219,q257] [v1237] (by decide +kernel)
def v1238 : Closed T 7 := rotateClosed n899 auto8 auto8ok
def n1079 := cc 8 [w86,w197,w166,w1,w2,w3,w4] [q0,q219,q257,q262] [v1238] (by decide +kernel)
def v1239 : Closed T 8 := rotateClosed n917 auto8 auto8ok
def n1080 := cc 9 [w86,w197,w0,w1,w2,w3,w4,w5] [q0,q219,q257,q262] [n1075,n1078,n1079,v1239] (by decide +kernel)
def n1081 := cc 8 [w156,w418,w0,w1,w3,w4,w5] [q7,q14,q103,q271] [] (by decide +kernel)
def n1082 := cc 8 [w86,w331,w0,w1,w2,w3,w4] [q0,q6,q178,q231] [] (by decide +kernel)
def v1240 : Closed T 8 := rotateClosed n1081 auto14 auto14ok
def v1241 : Closed T 8 := rotateClosed n736 auto14 auto14ok
def v1242 : Closed T 8 := rotateClosed n900 auto8 auto8ok
def n1083 := cc 9 [w86,w166,w0,w1,w2,w3,w4] [q0,q6,q171,q225,q262] [n602,n1078,n1079,n317,n920,n1082,v1240,v1241,v1242] (by decide +kernel)
def n1084 := cc 8 [w510,w0,w1,w2,w3,w4,w5] [q4,q31,q84,q216] [] (by decide +kernel)
def n1085 := cc 8 [w86,w195,w0,w1,w42,w3,w4] [q0,q13,q59,q150,q204,q214] [] (by decide +kernel)
def v1243 : Closed T 8 := rotateClosed n1072 auto14 auto14ok
def v1244 : Closed T 8 := rotateClosed n1084 auto4 auto4ok
def n1086 := cc 9 [w86,w195,w0,w1,w2,w3,w4,w5] [q0,q13,q150,q214] [n1085,n1072,v1243,v1244] (by decide +kernel)
def n1087 := cc 8 [w511,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q222,q258] [] (by decide +kernel)
def n1088 := cc 9 [w86,w156,w0,w1,w2,w3,w4,w5] [q0,q13,q222,q258,q262] [n1065,n1087] (by decide +kernel)
def n1089 := cc 7 [w0,w1,w512,w2,w209,w3,w4] [q7,q61,q262] [] (by decide +kernel)
def n1090 := cc 8 [w0,w1,w42,w512,w2,w3,w4] [q7,q59,q136,q171,q262] [n1089] (by decide +kernel)
def n1091 := cc 8 [w86,w0,w1,w2,w183,w3,w4] [q0,q14,q200,q246,q262] [n921,v1170] (by decide +kernel)
def n1092 := cc 8 [w86,w0,w1,w42,w2,w209,w3,w4] [q13,q204,q249,q262] [n1089] (by decide +kernel)
def n1093 := cc 8 [w86,w222,w0,w1,w42,w2,w3,w4] [q13,q214,q254,q262] [] (by decide +kernel)
def v1245 : Closed T 8 := rotateClosed n1068 auto14 auto14ok
def n1094 := cc 9 [w86,w0,w1,w42,w2,w3,w4] [q0,q14,q171,q225,q262] [n1076,n1085,n1093,n1078,n922,n957,n1092,n1091,v1106,v1245,n1090] (by decide +kernel)
def v1246 : Closed T 9 := rotateClosed n1063 auto6 auto6ok
def v1247 : Closed T 9 := rotateClosed n1069 auto14 auto14ok
def v1248 : Closed T 9 := rotateClosed n1066 auto8 auto8ok
def v1249 : Closed T 9 := rotateClosed n1074 auto8 auto8ok
def n1095 := cc 10 [w86,w0,w1,w2,w3,w4,w5] [q14,q171,q225] [n1077,n1086,n590,n1088,n603,n1080,n1083,n318,n923,n958,n398,n1094,n1021,n1041,v1246,v1247,v1248,v1249] (by decide +kernel)
def n1096 := cc 6 [w86,w514,w2,w3,w4] [] [] (by decide +kernel)
def v1250 : Closed T 6 := rotateClosed n1096 auto8 auto8ok
def n1097 := cc 7 [w516,w1,w2,w3,w4,w5] [q262,q272] [v1250] (by decide +kernel)
def v1251 : Closed T 7 := rotateClosed n1097 auto6 auto6ok
def n1098 := cc 8 [w11,w212,w1,w2,w3,w4,w5] [q163,q269] [v1251] (by decide +kernel)
def n1099 := cc 9 [w11,w156,w0,w1,w2,w3,w4,w5] [q262,q272] [n393,n489,n1098,n531,n668] (by decide +kernel)
def n1100 := cc 8 [w156,w0,w198,w2,w3,w4,w5] [q0,q72,q163] [n435] (by decide +kernel)
def n1101 := cc 8 [w0,w518,w1,w2,w3,w4,w5] [q88,q158,q262,q265] [] (by decide +kernel)
def n1102 := cc 8 [w520,w0,w1,w2,w3,w4,w5] [q4,q14,q168,q271] [] (by decide +kernel)
def n1103 := cc 8 [w0,w521,w1,w2,w3,w4,w5] [q13,q100,q161,q204,q262,q265] [] (by decide +kernel)
def n1104 := cc 8 [w522,w0,w1,w2,w3,w4,w5] [q163,q166,q267,q268] [] (by decide +kernel)
def v1252 : Closed T 8 := rotateClosed n1104 auto14 auto14ok
def v1253 : Closed T 8 := rotateClosed n1102 auto12 auto12ok
def v1254 : Closed T 8 := rotateClosed n1102 auto13 auto13ok
def v1255 : Closed T 8 := rotateClosed n1100 auto8 auto8ok
def v1256 : Closed T 8 := rotateClosed n1101 auto2 auto2ok
def v1257 : Closed T 8 := rotateClosed n1101 auto3 auto3ok
def v1258 : Closed T 8 := rotateClosed n1103 auto6 auto6ok
def n1105 := cc 9 [w0,w212,w1,w2,w3,w4,w5] [q7,q14,q88,q153,q171,q262,q265] [n393,v494,v101,v1252,v1253,v1254,n605,v594,n604,v1255,n4,n927,v1256,v1257,v1258,n23,n1023,v459] (by decide +kernel)
def n1106 := cc 9 [w156,w0,w212,w1,w2,w3,w4,w5] [q262,q269,q270] [v494,n1098,v108] (by decide +kernel)
def n1107 := cc 8 [w129,w236,w1,w2,w3,w4,w5] [q163,q269] [v1251] (by decide +kernel)
def n1108 := cc 9 [w129,w156,w0,w1,w2,w3,w4,w5] [q262,q272] [n1107,v494,n22,n403,n1100] (by decide +kernel)
def n1109 := cc 8 [w524,w0,w1,w2,w3,w4,w5] [q262,q269] [] (by decide +kernel)
def n1110 := cc 8 [w526,w0,w1,w2,w3,w4,w5] [q7,q163,q260] [] (by decide +kernel)
def n1111 := cc 8 [w156,w527,w0,w2,w3,w4,w5] [q0,q7,q13,q15,q104] [] (by decide +kernel)
def n1112 := cc 8 [w65,w0,w1,w2,w41,w3,w4,w5] [q172,q260,q262,q272] [] (by decide +kernel)
def v1259 : Closed T 8 := rotateClosed n489 auto6 auto6ok
def v1260 : Closed T 8 := rotateClosed n1111 auto14 auto14ok
def v1261 : Closed T 8 := rotateClosed n1110 auto12 auto12ok
def v1262 : Closed T 8 := rotateClosed n1110 auto13 auto13ok
def v1263 : Closed T 8 := rotateClosed n1109 auto8 auto8ok
def v1264 : Closed T 8 := rotateClosed n940 auto2 auto2ok
def v1265 : Closed T 8 := rotateClosed n940 auto3 auto3ok
def n1113 := cc 9 [w65,w0,w1,w2,w3,w4,w5] [q103,q171,q260,q262,q273,q274] [v1259,v5,n499,v594,v1260,v1261,v1262,v1263,v597,v85,n960,v1264,v1265,n4,n693,n1112,n401] (by decide +kernel)
def n1114 := cc 9 [w156,w236,w0,w1,w2,w3,w4,w5] [q262,q269] [n1107,n489,n437] (by decide +kernel)
def n1115 := cc 8 [w0,w529,w1,w2,w3,w4,w5] [q262,q265,q269] [] (by decide +kernel)
def n1116 := cc 8 [w531,w0,w1,w2,w3,w4,w5] [q2,q226,q262] [] (by decide +kernel)
def n1117 := cc 7 [w533,w0,w534,w1,w3,w5] [q0,q163,q169] [] (by decide +kernel)
def v1266 : Closed T 7 := rotateClosed n1117 auto9 auto9ok
def n1118 := cc 8 [w528,w0,w535,w1,w3,w4,w5] [q10,q14,q163,q168] [v1266] (by decide +kernel)
def n1119 := cc 8 [w536,w0,w1,w2,w3,w4,w5] [q65,q98,q157,q262] [] (by decide +kernel)
def n1120 := cc 8 [w538,w0,w1,w2,w3,w4,w5] [q93,q156,q166,q262,q265] [] (by decide +kernel)
def v1267 : Closed T 8 := rotateClosed n1119 auto2 auto2ok
def v1268 : Closed T 8 := rotateClosed n1118 auto2 auto2ok
def v1269 : Closed T 8 := rotateClosed n1116 auto5 auto5ok
def v1270 : Closed T 8 := rotateClosed n1120 auto13 auto13ok
def v1271 : Closed T 8 := rotateClosed n1120 auto15 auto15ok
def n1121 := cc 9 [w528,w0,w1,w2,w3,w4,w5] [q14,q157,q222,q262,q265,q269,q271] [n438,n493,n1119,v1267,n1118,v1268,v1269,v1270,v1271,n1115] (by decide +kernel)
def v1272 : Closed T 7 := rotateClosed n1117 auto8 auto8ok
def n1122 := cc 8 [w156,w0,w540,w1,w3,w4,w5] [q11,q14,q262] [v1272] (by decide +kernel)
def v1273 : Closed T 8 := rotateClosed n1122 auto1 auto1ok
def n1123 := cc 9 [w528,w156,w0,w1,w2,w3,w4,w5] [q14,q262,q269] [v1268,v1273] (by decide +kernel)
def n1124 := cc 8 [w0,w1,w541,w2,w3,w4,w5] [q143,q262,q265] [] (by decide +kernel)
def n1125 := cc 8 [w543,w0,w1,w2,w3,w4,w5] [q2,q6,q46,q143] [] (by decide +kernel)
def n1126 := cc 8 [w547,w0,w1,w2,w3,w4,w5] [q6,q168,q271] [] (by decide +kernel)
def n1127 := cc 8 [w549,w0,w1,w2,w3,w4,w5] [q101,q141,q160,q262,q265] [] (by decide +kernel)
def n1128 := cc 7 [w553,w0,w1,w3,w4,w5] [q13,q163,q193,q241] [] (by decide +kernel)
def v1274 : Closed T 7 := rotateClosed n1128 auto10 auto10ok
def n1129 := cc 8 [w554,w0,w1,w2,w3,w4,w5] [q4,q14,q168,q271] [v1274,v909] (by decide +kernel)
def n1130 := cc 8 [w556,w0,w1,w2,w3,w4,w5] [q262,q269] [] (by decide +kernel)
def n1131 := cc 7 [w182,w0,w558,w1,w4,w5] [q163,q261] [] (by decide +kernel)
def v1275 : Closed T 7 := rotateClosed n1131 auto3 auto3ok
def n1132 := cc 8 [w533,w0,w1,w42,w3,w4,w5] [q14,q231,q262,q271] [v1275] (by decide +kernel)
def v1276 : Closed T 8 := rotateClosed n1125 auto13 auto13ok
def v1277 : Closed T 8 := rotateClosed n1118 auto9 auto9ok
def v1278 : Closed T 8 := rotateClosed n1130 auto15 auto15ok
def v1279 : Closed T 8 := rotateClosed n1122 auto8 auto8ok
def v1280 : Closed T 8 := rotateClosed n1127 auto12 auto12ok
def v1281 : Closed T 8 := rotateClosed n940 auto8 auto8ok
def v1282 : Closed T 8 := rotateClosed n1126 auto2 auto2ok
def v1283 : Closed T 8 := rotateClosed n1124 auto8 auto8ok
def n1133 := cc 9 [w533,w0,w1,w2,w3,w4,w5] [q4,q92,q103,q231,q262,q271,q275] [n1102,v1276,v1277,v1278,v1279,v1280,v1281,v1282,n1129,n1132,v1283] (by decide +kernel)
def n1134 := cc 9 [w156,w0,w1,w559,w2,w3,w4,w5] [q14,q270,q276] [v1268] (by decide +kernel)
def n1135 := cc 8 [w0,w560,w1,w2,w3,w4,w5] [q7,q262,q265,q271] [] (by decide +kernel)
def n1136 := cc 8 [w562,w0,w1,w2,w3,w4,w5] [q0,q6,q265] [] (by decide +kernel)
def n1137 := cc 7 [w331,w1,w183,w3,w4,w5] [q181,q233,q262] [] (by decide +kernel)
def v1284 : Closed T 7 := rotateClosed n1137 auto8 auto8ok
def v1285 : Closed T 7 := rotateClosed n1137 auto14 auto14ok
def n1138 := cc 8 [w168,w0,w2,w209,w3,w4,w5] [q14,q262,q271,q272] [v1284,v1285] (by decide +kernel)
def n1139 := cc 7 [w331,w0,w330,w1,w3,w4] [q6,q260,q261] [] (by decide +kernel)
def v1286 : Closed T 7 := rotateClosed n1139 auto8 auto8ok
def n1140 := cc 8 [w168,w0,w563,w1,w3,w4,w5] [q13,q14,q272] [v1286,v1284] (by decide +kernel)
def n1141 := cc 8 [w565,w0,w1,w2,w3,w4,w5] [q92,q262,q271] [] (by decide +kernel)
def v1287 : Closed T 8 := rotateClosed n1078 auto8 auto8ok
def v1288 : Closed T 8 := rotateClosed n1078 auto14 auto14ok
def v1289 : Closed T 8 := rotateClosed n1119 auto3 auto3ok
def v1290 : Closed T 8 := rotateClosed n1140 auto6 auto6ok
def v1291 : Closed T 8 := rotateClosed n1136 auto2 auto2ok
def v1292 : Closed T 8 := rotateClosed n738 auto8 auto8ok
def v1293 : Closed T 8 := rotateClosed n1141 auto10 auto10ok
def v1294 : Closed T 8 := rotateClosed n1141 auto11 auto11ok
def v1295 : Closed T 8 := rotateClosed n1017 auto8 auto8ok
def n1142 := cc 9 [w168,w0,w1,w2,w3,w4,w5] [q99,q258,q262,q272] [v1287,v1288,n440,n496,v1267,v1289,n321,n733,v1000,n1140,v1290,n1138,v1291,v1292,v894,v1293,v1294,n1135,v1295] (by decide +kernel)
def n1143 := cc 8 [w156,w0,w2,w209,w3,w4,w5] [q7,q67,q141,q262] [v892,v1285] (by decide +kernel)
def n1144 := cc 8 [w156,w0,w563,w1,w3,w4,w5] [q14,q262,q272] [v1286] (by decide +kernel)
def n1145 := cc 7 [w567,w0,w1,w3,w4,w5] [q6,q95,q156,q166] [] (by decide +kernel)
def v1296 : Closed T 7 := rotateClosed n1145 auto14 auto14ok
def n1146 := cc 8 [w168,w0,w1,w2,w3,w4,w568] [q7,q163,q222,q258] [v1296] (by decide +kernel)
def n1147 := cc 9 [w168,w156,w0,w1,w2,w3,w4,w5] [q171,q262,q272] [n733,v1290,n1146,n1144,n1143] (by decide +kernel)
def n1148 := cc 9 [w156,w0,w1,w2,w3,w4,w5,w568] [q7,q222,q262] [n1146,v894] (by decide +kernel)
def n1149 := cc 8 [w156,w0,w570,w2,w3,w4,w5] [q99,q160,q163,q166,q171] [] (by decide +kernel)
def n1150 := cc 8 [w569,w0,w1,w571,w2,w3,w4] [q7,q222,q258] [v1176,v1296] (by decide +kernel)
def n1151 := cc 9 [w569,w156,w0,w1,w2,w3,w4,w5] [q222,q258,q262,q271] [n1150,n737,n1028,n1149] (by decide +kernel)
def n1152 := cc 8 [w0,w1,w572,w2,w3,w4,w5] [q14,q207,q262,q265] [] (by decide +kernel)
def n1153 := cc 8 [w573,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q46,q171] [] (by decide +kernel)
def n1154 := cc 8 [w574,w0,w1,w2,w3,w4,w5] [q37,q163,q265] [] (by decide +kernel)
def n1155 := cc 8 [w331,w0,w1,w42,w3,w4,w5] [q6,q166,q178,q231] [n1137] (by decide +kernel)
def n1156 := cc 8 [w43,w0,w330,w1,w2,w3,w4] [q0,q113,q163,q219] [] (by decide +kernel)
def n1157 := cc 7 [w221,w0,w563,w1,w2,w3,w4,w5] [q0,q13,q166] [] (by decide +kernel)
def v1297 : Closed T 7 := rotateClosed n1157 auto8 auto8ok
def n1158 := cc 8 [w331,w0,w1,w2,w41,w3,w4,w5] [q10,q14,q156,q166,q265,q267,q271,q272] [v1297] (by decide +kernel)
def v1298 : Closed T 8 := rotateClosed n1156 auto6 auto6ok
def v1299 : Closed T 8 := rotateClosed n1153 auto14 auto14ok
def v1300 : Closed T 8 := rotateClosed n1154 auto14 auto14ok
def v1301 : Closed T 8 := rotateClosed n1154 auto15 auto15ok
def v1302 : Closed T 8 := rotateClosed n1140 auto8 auto8ok
def v1303 : Closed T 8 := rotateClosed n1144 auto8 auto8ok
def v1304 : Closed T 8 := rotateClosed n960 auto8 auto8ok
def v1305 : Closed T 8 := rotateClosed n1126 auto1 auto1ok
def v1306 : Closed T 8 := rotateClosed n734 auto6 auto6ok
def v1307 : Closed T 8 := rotateClosed n941 auto10 auto10ok
def v1308 : Closed T 8 := rotateClosed n941 auto11 auto11ok
def v1309 : Closed T 8 := rotateClosed n1152 auto8 auto8ok
def n1159 := cc 9 [w331,w0,w1,w2,w3,w4,w5] [q6,q14,q156,q166,q171,q178,q262,q271] [n1082,v1298,n1104,v1299,v1300,v1301,v1302,v1100,v1303,v957,v1304,n1126,v1305,n835,v1306,v1307,v1308,n1155,n1158,n1025,v1309] (by decide +kernel)
def n1160 := cc 9 [w156,w0,w1,w571,w2,w3,w4,w5] [q163,q171,q262,q269] [n1150,v1290,v893] (by decide +kernel)
def v1310 : Closed T 8 := rotateClosed n1111 auto8 auto8ok
def n1161 := cc 9 [w156,w197,w0,w1,w2,w3,w4,w5] [q14,q103,q262,q271] [n393,n22,v101,n1111,v1310,n1100,v1255,n37] (by decide +kernel)
def n1162 := cc 8 [w575,w0,w1,w2,w3,w4,w5] [q10,q166,q171,q261] [] (by decide +kernel)
def v1311 : Closed T 8 := rotateClosed n1102 auto1 auto1ok
def v1312 : Closed T 8 := rotateClosed n1162 auto2 auto2ok
def n1163 := cc 9 [w156,w544,w0,w1,w2,w3,w4,w5] [q14,q262,q272] [n438,v1311,v1253,v1312] (by decide +kernel)
def n1164 := cc 8 [w576,w0,w1,w2,w3,w4,w5] [q13,q103,q169,q260] [] (by decide +kernel)
def v1313 : Closed T 8 := rotateClosed n1164 auto6 auto6ok
def n1165 := cc 9 [w156,w166,w0,w1,w2,w3,w4,w5] [q156,q262,q265,q271,q272,q276] [n440,n1104,v1252,v1313] (by decide +kernel)
def v1314 : Closed T 8 := rotateClosed n1122 auto4 auto4ok
def n1166 := cc 9 [w156,w323,w0,w1,w2,w3,w4,w5] [q14,q269,q271,q272] [v1273,v1314] (by decide +kernel)
def v1315 : Closed T 8 := rotateClosed n1079 auto8 auto8ok
def v1316 : Closed T 8 := rotateClosed n1144 auto6 auto6ok
def n1167 := cc 9 [w156,w425,w0,w1,w2,w3,w4,w5] [q14,q171,q262,q272] [v1315,n737,n1144,v1316] (by decide +kernel)
def n1168 := cc 8 [w221,w544,w1,w2,w3,w4,w5] [q2,q79,q168,q212] [] (by decide +kernel)
def v1317 : Closed T 8 := rotateClosed n1168 auto10 auto10ok
def v1318 : Closed T 8 := rotateClosed n979 auto8 auto8ok
def v1319 : Closed T 8 := rotateClosed n1155 auto14 auto14ok
def n1169 := cc 9 [w156,w0,w1,w42,w2,w3,w4,w5] [q14,q103,q171,q262,q271] [v1317,n737,n1143,v997,v1318,v1319] (by decide +kernel)
def n1170 := cc 8 [w156,w0,w577,w2,w3,w4,w5] [q7,q122,q163,q222] [] (by decide +kernel)
def v1320 : Closed T 8 := rotateClosed n1156 auto8 auto8ok
def n1171 := cc 9 [w43,w156,w0,w1,w2,w3,w4,w5] [q103,q222,q262,q271] [v1320,n737,n1170,n1149,n789] (by decide +kernel)
def n1172 := cc 8 [w0,w1,w2,w578,w3,w4,w5] [q0,q10,q86,q159,q214,q262,q275] [] (by decide +kernel)
def n1173 := cc 8 [w579,w0,w1,w2,w3,w4,w5] [q65,q98,q140,q262] [] (by decide +kernel)
def v1321 : Closed T 7 := rotateClosed n1157 auto6 auto6ok
def n1174 := cc 8 [w221,w156,w0,w1,w2,w3,w4,w5] [q0,q7,q163,q166,q212,q272] [v1321] (by decide +kernel)
def n1175 := cc 7 [w156,w0,w580,w3,w4,w5] [q7,q13,q31,q118] [] (by decide +kernel)
def v1322 : Closed T 7 := rotateClosed n1131 auto8 auto8ok
def v1323 : Closed T 7 := rotateClosed n1131 auto9 auto9ok
def n1176 := cc 8 [w182,w156,w0,w1,w3,w4,w5] [q7,q14,q103,q262] [v1322,v1323,n1175,n747] (by decide +kernel)
def v1324 : Closed T 8 := rotateClosed n1112 auto6 auto6ok
def v1325 : Closed T 8 := rotateClosed n1158 auto14 auto14ok
def v1326 : Closed T 8 := rotateClosed n1129 auto12 auto12ok
def v1327 : Closed T 8 := rotateClosed n1132 auto12 auto12ok
def v1328 : Closed T 8 := rotateClosed n1132 auto13 auto13ok
def v1329 : Closed T 8 := rotateClosed n1172 auto2 auto2ok
def n1177 := cc 9 [w156,w0,w1,w2,w41,w3,w4,w5] [q14,q103,q222,q262,q265,q272,q276] [n1173,n1174,n1176,n1119,v1324,v1325,v1326,v1327,v1328,v1329] (by decide +kernel)
def v1330 : Closed T 8 := rotateClosed n1126 auto14 auto14ok
def n1178 := cc 9 [w156,w0,w1,w2,w472,w3,w4,w5] [q14,q127,q222,q262,q265,q271] [v1267,v1330] (by decide +kernel)
def n1179 := cc 8 [w581,w0,w1,w2,w3,w4,w5] [q7,q37,q163,q258] [] (by decide +kernel)
def n1180 := cc 8 [w582,w0,w1,w2,w3,w4,w5] [q141,q160,q222,q262] [] (by decide +kernel)
def n1181 := cc 7 [w583,w492,w1,w2,w3,w5] [q4,q82,q213] [] (by decide +kernel)
def v1331 : Closed T 7 := rotateClosed n1181 auto13 auto13ok
def n1182 := cc 8 [w156,w0,w1,w113,w3,w4,w5] [q7,q103,q222,q262] [v1331] (by decide +kernel)
def v1332 : Closed T 8 := rotateClosed n1180 auto1 auto1ok
def v1333 : Closed T 8 := rotateClosed n1182 auto1 auto1ok
def n1183 := cc 9 [w74,w156,w0,w1,w2,w3,w4,w5] [q6,q13,q14,q258,q265,q271,q276] [v1332,v1333,n1179] (by decide +kernel)
def v1334 : Closed T 9 := rotateClosed n1080 auto8 auto8ok
def v1335 : Closed T 9 := rotateClosed n1083 auto14 auto14ok
def v1336 : Closed T 9 := rotateClosed n1183 auto1 auto1ok
def v1337 : Closed T 9 := rotateClosed n592 auto8 auto8ok
def v1338 : Closed T 9 := rotateClosed n1123 auto1 auto1ok
def v1339 : Closed T 9 := rotateClosed n1121 auto1 auto1ok
def v1340 : Closed T 9 := rotateClosed n1166 auto1 auto1ok
def v1341 : Closed T 9 := rotateClosed n1163 auto1 auto1ok
def v1342 : Closed T 9 := rotateClosed n942 auto1 auto1ok
def v1343 : Closed T 9 := rotateClosed n913 auto1 auto1ok
def v1344 : Closed T 9 := rotateClosed n1134 auto1 auto1ok
def v1345 : Closed T 9 := rotateClosed n1178 auto1 auto1ok
def v1346 : Closed T 9 := rotateClosed n1113 auto6 auto6ok
def v1347 : Closed T 9 := rotateClosed n1063 auto8 auto8ok
def v1348 : Closed T 9 := rotateClosed n1159 auto14 auto14ok
def v1349 : Closed T 9 := rotateClosed n1133 auto12 auto12ok
def v1350 : Closed T 9 := rotateClosed n1133 auto13 auto13ok
def n1184 := cc 10 [w156,w0,w1,w2,w3,w4,w5] [q14,q103,q171] [n1151,n1088,v1334,v1335,n1171,n1183,v1336,n1108,n442,n1099,n498,n606,v1337,n1123,v1338,n1121,v1339,n1147,n1142,n1166,v1340,n1167,n1161,n1163,v1341,n1165,n322,n1114,n928,n942,v1342,n961,n1106,n740,n735,n913,v1343,n925,n1134,v1344,n1160,n404,n1169,n1177,n1178,v1345,n1148,n1045,n1029,v1346,v1347,v1348,v1349,v1350,n1105] (by decide +kernel)
def n1185 := cc 8 [w0,w1,w2,w584,w3,w4,w5] [q7,q56,q135,q262,q271] [] (by decide +kernel)
def n1186 := cc 8 [w586,w0,w1,w2,w3,w4,w5] [q0,q212,q252,q262] [] (by decide +kernel)
def n1187 := cc 8 [w182,w0,w1,w170,w3,w4,w5] [q14,q103,q262,q271] [] (by decide +kernel)
def n1188 := cc 7 [w0,w2,w588,w3,w4,w5] [q44,q128,q262] [] (by decide +kernel)
def n1189 := cc 7 [w589,w1,w2,w3,w4,w5] [q0,q45,q129,q194] [] (by decide +kernel)
def v1351 : Closed T 7 := rotateClosed n1189 auto8 auto8ok
def v1352 : Closed T 7 := rotateClosed n1188 auto8 auto8ok
def n1190 := cc 8 [w0,w1,w587,w2,w3,w4,w5] [q43,q87,q262,q271] [n1189,v1351,n1188,v1352] (by decide +kernel)
def n1191 := cc 8 [w590,w0,w1,w2,w3,w4,w5] [q43,q127,q166,q262] [] (by decide +kernel)
def v1353 : Closed T 8 := rotateClosed n1186 auto6 auto6ok
def v1354 : Closed T 8 := rotateClosed n1186 auto14 auto14ok
def v1355 : Closed T 8 := rotateClosed n1191 auto6 auto6ok
def v1356 : Closed T 8 := rotateClosed n1119 auto8 auto8ok
def v1357 : Closed T 8 := rotateClosed n749 auto8 auto8ok
def v1358 : Closed T 8 := rotateClosed n1185 auto8 auto8ok
def n1192 := cc 9 [w0,w1,w170,w2,w3,w4,w5] [q14,q103,q171,q262,q271] [v1353,v1354,n1187,v1355,n1119,v1356,n324,n749,v1357,n1190,n1185,v1358] (by decide +kernel)
def v1359 : Closed T 7 := rotateClosed n607 auto8 auto8ok
def n1193 := cc 8 [w138,w0,w1,w2,w3] [q103,q171,q225] [n607,v1359,n325,n445] (by decide +kernel)
def v1360 : Closed T 8 := rotateClosed n1193 auto5 auto5ok
def v1361 : Closed T 8 := rotateClosed n608 auto8 auto8ok
def n1194 := cc 9 [w0,w1,w104,w71,w4,w5] [q14,q103,q171] [v1360,n608,v1361,n326,n446] (by decide +kernel)
def n1195 := cc 9 [w0,w1,w104,w2,w3,w137,w4,w5] [q43,q103,q242,q262] [n1190] (by decide +kernel)
def v1362 : Closed T 9 := rotateClosed n609 auto8 auto8ok
def v1363 : Closed T 9 := rotateClosed n1121 auto8 auto8ok
def v1364 : Closed T 9 := rotateClosed n1178 auto3 auto3ok
def v1365 : Closed T 9 := rotateClosed n1178 auto6 auto6ok
def v1366 : Closed T 9 := rotateClosed n1178 auto11 auto11ok
def v1367 : Closed T 9 := rotateClosed n1178 auto14 auto14ok
def v1368 : Closed T 9 := rotateClosed n751 auto8 auto8ok
def v1369 : Closed T 9 := rotateClosed n1006 auto3 auto3ok
def v1370 : Closed T 9 := rotateClosed n1006 auto6 auto6ok
def v1371 : Closed T 9 := rotateClosed n1006 auto11 auto11ok
def v1372 : Closed T 9 := rotateClosed n1006 auto14 auto14ok
def v1373 : Closed T 9 := rotateClosed n1192 auto2 auto2ok
def n1196 := cc 10 [w0,w1,w104,w2,w3,w4,w5] [q14,q103,q171] [n609,v1362,n1121,v1363,v1364,v1365,v1366,v1367,n327,n751,v1368,v1369,v1370,v1371,v1372,n447,n1192,v1373,n1195,n1194] (by decide +kernel)
def n1197 := cc 8 [w0,w1,w177,w2,w3,w4,w5] [q0,q7,q46,q130,q195] [n331] (by decide +kernel)
def n1198 := cc 8 [w178,w0,w1,w591,w2,w3,w4,w5] [q0,q7,q130,q195] [] (by decide +kernel)
def n1199 := cc 8 [w593,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q143,q207] [] (by decide +kernel)
def n1200 := cc 8 [w593,w0,w592,w1,w2,w3,w4,w5] [q4,q7,q130,q207] [] (by decide +kernel)
def v1374 : Closed T 8 := rotateClosed n613 auto8 auto8ok
def v1375 : Closed T 8 := rotateClosed n612 auto8 auto8ok
def v1376 : Closed T 8 := rotateClosed n1200 auto13 auto13ok
def v1377 : Closed T 8 := rotateClosed n1199 auto13 auto13ok
def v1378 : Closed T 8 := rotateClosed n1197 auto8 auto8ok
def n1201 := cc 9 [w178,w0,w1,w2,w3,w4,w5] [q0,q103,q171] [n610,v1374,v1375,v1376,v1377,n329,n332,n1198,n448,v1378] (by decide +kernel)
def n1202 := cc 8 [w0,w279,w1,w2,w3,w4,w5] [q0,q7,q46,q153,q218] [n614] (by decide +kernel)
def n1203 := cc 8 [w595,w0,w1,w2,w3,w4,w5] [q0,q11,q172] [] (by decide +kernel)
def v1379 : Closed T 8 := rotateClosed n1203 auto5 auto5ok
def n1204 := cc 9 [w179,w0,w1,w2,w3,w4,w5] [q7,q14,q103,q171,q271] [n451,n610,n615,n333,v1379,n1202] (by decide +kernel)
def v1380 : Closed T 9 := rotateClosed n616 auto8 auto8ok
def v1381 : Closed T 9 := rotateClosed n1204 auto8 auto8ok
def v1382 : Closed T 9 := rotateClosed n1201 auto8 auto8ok
def n1205 := cc 10 [w0,w1,w2,w3,w71,w4,w5] [q103,q171] [n616,v1380,n1204,v1381,n334,n1201,v1382,n452,n1194] (by decide +kernel)
def n1206 := cc 8 [w597,w0,w1,w2,w3,w4,w5] [q0,q13,q172,q226] [] (by decide +kernel)
def n1207 := cc 8 [w599,w0,w1,w2,w3,w4,w5] [q6,q96,q207,q250,q262] [] (by decide +kernel)
def n1208 := cc 8 [w600,w0,w1,w2,w3,w4,w5] [q95,q231,q271] [] (by decide +kernel)
def v1383 : Closed T 8 := rotateClosed n618 auto15 auto15ok
def v1384 : Closed T 8 := rotateClosed n1180 auto9 auto9ok
def v1385 : Closed T 8 := rotateClosed n1206 auto8 auto8ok
def n1209 := cc 9 [w0,w598,w1,w2,w3,w4,w5] [q6,q95,q171,q225,q262] [v1383,n1207,v1384,v1385,n1208,n453] (by decide +kernel)
def n1210 := cc 8 [w0,w1,w602,w2,w3,w4,w5] [q0,q7,q46,q130,q262] [] (by decide +kernel)
def n1211 := cc 8 [w604,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q207,q250] [] (by decide +kernel)
def n1212 := cc 8 [w605,w0,w1,w2,w3,w4,w5] [q7,q163,q222,q258] [] (by decide +kernel)
def v1386 : Closed T 8 := rotateClosed n1211 auto15 auto15ok
def v1387 : Closed T 8 := rotateClosed n1212 auto15 auto15ok
def v1388 : Closed T 8 := rotateClosed n1009 auto6 auto6ok
def v1389 : Closed T 8 := rotateClosed n1210 auto8 auto8ok
def n1213 := cc 9 [w606,w0,w1,w2,w3,w4,w5] [q6,q14,q103,q171,q265,q277] [n618,v1386,v1387,n336,v1388,v1389] (by decide +kernel)
def v1390 : Closed T 8 := rotateClosed n619 auto8 auto8ok
def n1214 := cc 9 [w0,w1,w2,w3,w4,w111] [q103,q171] [n619,v1390,n337,n455] (by decide +kernel)
def n1215 := cc 7 [w475,w0,w1,w607,w3,w5] [q10,q262] [] (by decide +kernel)
def n1216 := cc 7 [w346,w0,w1,w609,w4,w5] [q11,q163,q168] [] (by decide +kernel)
def n1217 := cc 6 [w612,w0,w2,w3,w5] [q265,q269,q271] [] (by decide +kernel)
def v1391 : Closed T 6 := rotateClosed n1217 auto13 auto13ok
def n1218 := cc 7 [w476,w1,w477,w3,w4,w5] [q181,q233,q262] [v1391] (by decide +kernel)
def v1392 : Closed T 7 := rotateClosed n1215 auto12 auto12ok
def v1393 : Closed T 7 := rotateClosed n1216 auto11 auto11ok
def n1219 := cc 8 [w476,w0,w1,w113,w3,w4,w5] [q6,q178,q231,q271] [v1392,v1393,n1218] (by decide +kernel)
def n1220 := cc 8 [w0,w1,w113,w477,w3,w4,w5] [q13,q103,q200,q246,q262,q271] [n1218] (by decide +kernel)
def v1394 : Closed T 6 := rotateClosed n1217 auto8 auto8ok
def n1221 := cc 7 [w583,w613,w1,w2,w3,w5] [q2,q82,q169,q213] [v1394] (by decide +kernel)
def n1222 := cc 8 [w583,w0,w1,w2,w3,w368,w5] [q2,q79,q212,q265] [n1221] (by decide +kernel)
def v1395 : Closed T 7 := rotateClosed n1221 auto13 auto13ok
def n1223 := cc 8 [w582,w0,w1,w113,w3,w4,w5] [q13,q204,q222,q258,q262] [v1395] (by decide +kernel)
def v1396 : Closed T 8 := rotateClosed n1222 auto5 auto5ok
def v1397 : Closed T 8 := rotateClosed n1222 auto13 auto13ok
def v1398 : Closed T 8 := rotateClosed n620 auto8 auto8ok
def v1399 : Closed T 8 := rotateClosed n1223 auto8 auto8ok
def v1400 : Closed T 8 := rotateClosed n1219 auto8 auto8ok
def v1401 : Closed T 8 := rotateClosed n1220 auto8 auto8ok
def n1224 := cc 9 [w0,w1,w113,w3,w4,w5] [q171,q225] [v1396,v1397,n620,v1398,n1223,v1399,n338,n1219,v1400,n456,n1220,v1401] (by decide +kernel)
def n1225 := cc 8 [w0,w1,w2,w477,w3,w4,w5] [q7,q136,q200,q262,q271] [n1010] (by decide +kernel)
def n1226 := cc 8 [w583,w0,w1,w2,w3,w4,w5] [q0,q212,q265] [n1181] (by decide +kernel)
def v1402 : Closed T 8 := rotateClosed n1226 auto5 auto5ok
def v1403 : Closed T 8 := rotateClosed n1226 auto13 auto13ok
def v1404 : Closed T 8 := rotateClosed n1180 auto8 auto8ok
def v1405 : Closed T 8 := rotateClosed n1182 auto8 auto8ok
def v1406 : Closed T 8 := rotateClosed n1009 auto8 auto8ok
def v1407 : Closed T 8 := rotateClosed n1011 auto8 auto8ok
def v1408 : Closed T 8 := rotateClosed n1225 auto8 auto8ok
def n1227 := cc 9 [w0,w1,w113,w2,w3,w4,w5] [q103,q171,q262,q271] [v1402,v1403,n1180,v1404,n1182,v1405,n339,n1009,v1406,n1011,v1407,n1225,v1408] (by decide +kernel)
def v1409 : Closed T 8 := rotateClosed n621 auto8 auto8ok
def v1410 : Closed T 8 := rotateClosed n1193 auto1 auto1ok
def n1228 := cc 9 [w74,w114,w0,w1,w2,w4] [q14,q171,q225] [n621,v1409,n340,n457,v1410] (by decide +kernel)
def v1411 : Closed T 9 := rotateClosed n622 auto8 auto8ok
def v1412 : Closed T 9 := rotateClosed n1183 auto8 auto8ok
def v1413 : Closed T 9 := rotateClosed n1012 auto8 auto8ok
def v1414 : Closed T 9 := rotateClosed n1213 auto7 auto7ok
def v1415 : Closed T 9 := rotateClosed n1213 auto15 auto15ok
def v1416 : Closed T 9 := rotateClosed n1209 auto8 auto8ok
def v1417 : Closed T 9 := rotateClosed n1227 auto1 auto1ok
def v1418 : Closed T 9 := rotateClosed n1224 auto1 auto1ok
def v1419 : Closed T 9 := rotateClosed n1214 auto6 auto6ok
def n1229 := cc 10 [w74,w0,w1,w2,w3,w4,w5] [q14,q171,q225] [n1228,n622,v1411,n1183,v1412,n341,n1012,v1413,n458,v1414,v1415,n1209,v1416,v1417,v1418,v1419] (by decide +kernel)
def n1230 := cc 6 [w376,w209,w3,w4,w82] [q39,q124,q262] [] (by decide +kernel)
def n1231 := cc 7 [w376,w2,w209,w3,w4,w5] [q124,q166,q262,q271,q276] [n1230] (by decide +kernel)
def n1232 := cc 6 [w116,w0,w372,w2,w5] [q2,q23,q168,q183] [] (by decide +kernel)
def v1420 : Closed T 6 := rotateClosed n1232 auto2 auto2ok
def v1421 : Closed T 6 := rotateClosed n1230 auto8 auto8ok
def n1233 := cc 7 [w0,w203,w42,w3,w4,w82] [q27,q114,q262] [v1420,v1421] (by decide +kernel)
def v1422 : Closed T 7 := rotateClosed n1231 auto8 auto8ok
def n1234 := cc 8 [w0,w203,w42,w2,w3,w4,w5] [q114,q166,q262,q271,q272,q276] [v924,n1233,v1422] (by decide +kernel)
def n1235 := cc 6 [w116,w38,w1,w2,w5] [q2,q10,q35,q192] [] (by decide +kernel)
def n1236 := cc 7 [w38,w1,w2,w41,w79,w5] [q2,q10,q35,q168,q192] [n1235] (by decide +kernel)
def n1237 := cc 8 [w38,w1,w2,w41,w3,w4,w5] [q265,q269,q272,q275,q278] [n1236] (by decide +kernel)
def n1238 := cc 6 [w116,w346,w0,w1,w5] [q10,q193,q265] [] (by decide +kernel)
def n1239 := cc 7 [w346,w0,w1,w41,w79,w5] [q10,q193,q265] [n1238] (by decide +kernel)
def n1240 := cc 8 [w346,w0,w1,w41,w3,w4,w5] [q169,q193,q265,q269,q271,q272,q275] [n1239] (by decide +kernel)
def n1241 := cc 6 [w614,w0,w2,w79,w5] [q265,q269,q272] [] (by decide +kernel)
def n1242 := cc 7 [w614,w0,w2,w3,w4,w5] [q168,q169,q265,q272,q275] [n1241] (by decide +kernel)
def n1243 := cc 6 [w615,w0,w2,w470,w5] [q34,q191,q265] [] (by decide +kernel)
def v1423 : Closed T 6 := rotateClosed n1243 auto10 auto10ok
def n1244 := cc 7 [w377,w1,w183,w3,w4,w82] [q30,q262,q271] [v1423,v1421] (by decide +kernel)
def v1424 : Closed T 7 := rotateClosed n1242 auto10 auto10ok
def n1245 := cc 8 [w377,w1,w2,w183,w3,w4,w5] [q117,q166,q262,q271,q276] [v1424,n1244,v1422] (by decide +kernel)
def n1246 := cc 7 [w615,w0,w1,w2,w41,w5] [q1,q10,q31,q168,q189] [n1243] (by decide +kernel)
def v1425 : Closed T 6 := rotateClosed n1235 auto8 auto8ok
def v1426 : Closed T 6 := rotateClosed n1238 auto8 auto8ok
def v1427 : Closed T 6 := rotateClosed n1238 auto14 auto14ok
def n1247 := cc 7 [w116,w371,w0,w1,w2,w5] [q2,q22,q182,q272] [v1425,v1426,v1427,n1232] (by decide +kernel)
def v1428 : Closed T 7 := rotateClosed n1247 auto2 auto2ok
def v1429 : Closed T 7 := rotateClosed n1236 auto10 auto10ok
def v1430 : Closed T 7 := rotateClosed n1239 auto10 auto10ok
def v1431 : Closed T 7 := rotateClosed n1239 auto11 auto11ok
def v1432 : Closed T 7 := rotateClosed n1246 auto10 auto10ok
def n1248 := cc 8 [w377,w0,w1,w42,w3,w4,w82] [q26,q113,q262,q271] [v1428,v1429,v1430,v1431,v1432,n1244,n1233] (by decide +kernel)
def v1433 : Closed T 8 := rotateClosed n1237 auto10 auto10ok
def v1434 : Closed T 8 := rotateClosed n854 auto8 auto8ok
def v1435 : Closed T 8 := rotateClosed n1240 auto10 auto10ok
def v1436 : Closed T 8 := rotateClosed n1240 auto11 auto11ok
def n1249 := cc 9 [w377,w0,w1,w42,w2,w3,w4,w5] [q14,q103,q262,q271,q276,q277] [v949,v1433,v1100,v1434,v1101,v1435,v1436,n1248,n1245,n1234] (by decide +kernel)
def n1250 := cc 8 [w220,w0,w1,w2,w3,w4,w5] [q2,q4,q6,q88,q271] [n459,n408] (by decide +kernel)
def v1437 : Closed T 7 := rotateClosed n965 auto8 auto8ok
def v1438 : Closed T 7 := rotateClosed n965 auto14 auto14ok
def n1251 := cc 8 [w220,w0,w1,w2,w209,w3,w4,w5] [q0,q6,q262,q271,q272] [v1437,v1438] (by decide +kernel)
def n1252 := cc 8 [w616,w0,w1,w2,w3,w4,w5] [q15,q103,q265,q271] [] (by decide +kernel)
def n1253 := cc 8 [w616,w0,w1,w2,w183,w3,w4,w5] [q7,q265,q271] [] (by decide +kernel)
def n1254 := cc 8 [w0,w1,w617,w2,w3,w4,w5] [q56,q262,q271] [] (by decide +kernel)
def v1439 : Closed T 8 := rotateClosed n1091 auto6 auto6ok
def v1440 : Closed T 8 := rotateClosed n626 auto10 auto10ok
def v1441 : Closed T 8 := rotateClosed n1173 auto10 auto10ok
def v1442 : Closed T 8 := rotateClosed n1173 auto11 auto11ok
def v1443 : Closed T 8 := rotateClosed n1138 auto8 auto8ok
def v1444 : Closed T 8 := rotateClosed n1143 auto8 auto8ok
def v1445 : Closed T 8 := rotateClosed n1143 auto14 auto14ok
def v1446 : Closed T 8 := rotateClosed n968 auto6 auto6ok
def v1447 : Closed T 8 := rotateClosed n976 auto6 auto6ok
def v1448 : Closed T 8 := rotateClosed n966 auto6 auto6ok
def v1449 : Closed T 8 := rotateClosed n1251 auto8 auto8ok
def v1450 : Closed T 8 := rotateClosed n1250 auto8 auto8ok
def v1451 : Closed T 8 := rotateClosed n1254 auto2 auto2ok
def v1452 : Closed T 8 := rotateClosed n1254 auto3 auto3ok
def v1453 : Closed T 8 := rotateClosed n1046 auto6 auto6ok
def n1255 := cc 9 [w0,w1,w2,w183,w3,w4,w5] [q14,q59,q171,q246,q262,q265] [n1091,v1439,v1440,v1441,v1442,n629,n628,v1100,v1443,v1444,v1445,n1253,n1252,n358,n968,v1446,n976,v1447,n966,v1448,v1449,v1450,v1451,v1452,n1046,v1453,n466,v525] (by decide +kernel)
def n1256 := cc 7 [w220,w1,w2,w183,w3,w4,w5] [q6,q260,q261,q262,q271] [] (by decide +kernel)
def n1257 := cc 7 [w0,w1,w2,w325,w470,w79,w5] [q2,q10,q57,q265,q272] [] (by decide +kernel)
def v1454 : Closed T 7 := rotateClosed n1256 auto8 auto8ok
def v1455 : Closed T 7 := rotateClosed n1257 auto2 auto2ok
def n1258 := cc 8 [w0,w1,w2,w183,w209,w3,w4,w5] [q61,q137,q201,q247,q262,q265,q271,q272] [n1256,v1454,n96,v1455] (by decide +kernel)
def n1259 := cc 7 [w221,w0,w1,w618,w2,w3,w4,w5] [q51,q65,q75,q163] [] (by decide +kernel)
def v1456 : Closed T 7 := rotateClosed n1259 auto6 auto6ok
def n1260 := cc 8 [w221,w0,w1,w2,w3,w470,w4,w5] [q0,q65,q205,q212,q265,q271,q272] [n1259,v1456] (by decide +kernel)
def n1261 := cc 8 [w220,w0,w1,w42,w2,w3,w4,w5] [q6,q260,q261,q271] [n1256,n96] (by decide +kernel)
def n1262 := cc 7 [w619,w1,w2,w41,w325,w5] [q56,q265,q272] [] (by decide +kernel)
def n1263 := cc 6 [w621,w1,w183,w3,w4] [q30,q117,q262] [] (by decide +kernel)
def v1457 : Closed T 6 := rotateClosed n1263 auto2 auto2ok
def n1264 := cc 7 [w116,w0,w1,w2,w325,w5] [q10,q56,q203,q265,q272] [v1457] (by decide +kernel)
def n1265 := cc 7 [w0,w1,w42,w622,w3,w4] [q59,q103,q262,q271] [] (by decide +kernel)
def v1458 : Closed T 7 := rotateClosed n1264 auto2 auto2ok
def v1459 : Closed T 7 := rotateClosed n1262 auto2 auto2ok
def n1266 := cc 8 [w0,w1,w42,w183,w3,w4,w82] [q7,q59,q136,q262,q271] [v1458,n1244,v1459,n1265,v1455] (by decide +kernel)
def v1460 : Closed T 7 := rotateClosed n1259 auto8 auto8ok
def n1267 := cc 8 [w0,w1,w617,w2,w41,w3,w4,w5] [q10,q135,q265,q271,q272,q276] [v1460] (by decide +kernel)
def n1268 := cc 7 [w221,w1,w42,w2,w183,w3,w4,w5] [q0,q163] [] (by decide +kernel)
def n1269 := cc 7 [w0,w1,w2,w183,w3,w117,w4,w5] [q0,q62,q142,q262,q275,q276] [] (by decide +kernel)
def n1270 := cc 7 [w623,w0,w1,w42,w2,w3,w4,w5] [q64,q81,q102,q139,q217,q265] [] (by decide +kernel)
def n1271 := cc 8 [w0,w1,w42,w2,w183,w41,w3,w4,w5] [q59,q83,q136,q163,q262,q265,q275,q276] [n1268,n1270,n1269] (by decide +kernel)
def v1461 : Closed T 8 := rotateClosed n1092 auto8 auto8ok
def v1462 : Closed T 8 := rotateClosed n1092 auto14 auto14ok
def v1463 : Closed T 8 := rotateClosed n1260 auto10 auto10ok
def v1464 : Closed T 8 := rotateClosed n1001 auto10 auto10ok
def v1465 : Closed T 8 := rotateClosed n1001 auto11 auto11ok
def v1466 : Closed T 8 := rotateClosed n969 auto6 auto6ok
def v1467 : Closed T 8 := rotateClosed n1261 auto8 auto8ok
def v1468 : Closed T 8 := rotateClosed n1267 auto2 auto2ok
def v1469 : Closed T 8 := rotateClosed n1267 auto3 auto3ok
def n1272 := cc 9 [w0,w1,w42,w2,w183,w3,w4,w5] [q14,q59,q136,q171,q200,q246,q262,q265,q271] [v1461,v1462,v1463,v950,v1443,n1245,v1464,v1465,n969,v1466,v1467,v1468,v1469,n1271,n1266,n1258] (by decide +kernel)
def n1273 := cc 8 [w0,w624,w1,w2,w3,w4,w5] [q7,q72,q262,q265] [] (by decide +kernel)
def v1470 : Closed T 7 := rotateClosed n630 auto8 auto8ok
def n1274 := cc 8 [w625,w0,w1,w2,w3,w4,w5] [q0,q2,q4,q6,q7,q46] [v1470,v22] (by decide +kernel)
def n1275 := cc 8 [w0,w1,w626,w2,w3,w4,w5] [q7,q84,q152,q163] [] (by decide +kernel)
def n1276 := cc 7 [w0,w1,w42,w2,w627,w3,w4,w5] [q80,q81,q171] [] (by decide +kernel)
def n1277 := cc 7 [w221,w222,w0,w1,w2,w3,w4,w5] [q0,q7,q265,q271] [n461] (by decide +kernel)
def v1471 : Closed T 7 := rotateClosed n973 auto6 auto6ok
def n1278 := cc 8 [w221,w0,w1,w42,w2,w3,w4,w5] [q0,q7,q148,q212,q265,q271,q272] [n1277,n808,n973,v1471,n463,n1268,n1276] (by decide +kernel)
def v1472 : Closed T 8 := rotateClosed n997 auto6 auto6ok
def v1473 : Closed T 8 := rotateClosed n1174 auto6 auto6ok
def v1474 : Closed T 8 := rotateClosed n1168 auto1 auto1ok
def v1475 : Closed T 8 := rotateClosed n811 auto1 auto1ok
def v1476 : Closed T 8 := rotateClosed n1003 auto6 auto6ok
def v1477 : Closed T 8 := rotateClosed n835 auto2 auto2ok
def v1478 : Closed T 8 := rotateClosed n1274 auto10 auto10ok
def v1479 : Closed T 8 := rotateClosed n1273 auto8 auto8ok
def v1480 : Closed T 8 := rotateClosed n1275 auto8 auto8ok
def v1481 : Closed T 8 := rotateClosed n1275 auto14 auto14ok
def n1279 := cc 9 [w221,w0,w1,w2,w3,w4,w5] [q0,q14,q103,q148,q212,q265] [n626,n356,n997,v1472,n631,n1174,v1473,n1168,v1474,n773,n811,v1475,n1003,v1476,n1278,n464,v1477,v1478,v1479,v1480,v1481] (by decide +kernel)
def n1280 := cc 6 [w221,w628,w1,w2,w5] [q2,q82,q168,q213] [] (by decide +kernel)
def v1482 : Closed T 6 := rotateClosed n1241 auto8 auto8ok
def n1281 := cc 7 [w221,w564,w1,w2,w79,w5] [q82,q213,q265] [n1280,v1482] (by decide +kernel)
def v1483 : Closed T 7 := rotateClosed n1242 auto8 auto8ok
def n1282 := cc 8 [w221,w564,w1,w2,w3,w4,w5] [q168,q169,q265,q272,q275] [n1281,v1483] (by decide +kernel)
def v1484 : Closed T 7 := rotateClosed n998 auto6 auto6ok
def v1485 : Closed T 7 := rotateClosed n998 auto14 auto14ok
def n1283 := cc 8 [w221,w468,w0,w1,w2,w3,w4,w5] [q0,q7,q212,q216,q265,q272] [n998,v1484,v1121,v1485] (by decide +kernel)
def n1284 := cc 7 [w221,w629,w0,w1,w2,w3,w4,w5] [q0,q265] [] (by decide +kernel)
def n1285 := cc 7 [w221,w182,w0,w1,w42,w3,w4,w5] [q212,q260,q265] [] (by decide +kernel)
def n1286 := cc 8 [w221,w182,w0,w1,w2,w3,w4,w5] [q148,q212,q260,q265,q272,q275] [v1121,n1284,n1285] (by decide +kernel)
def n1287 := cc 7 [w221,w0,w1,w2,w3,w117,w4,w5] [q0,q265] [] (by decide +kernel)
def v1486 : Closed T 7 := rotateClosed n1285 auto6 auto6ok
def n1288 := cc 8 [w221,w0,w1,w42,w2,w41,w3,w4,w5] [q56,q148,q260,q265,q267,q275] [n1284,n1285,v1486,n1287] (by decide +kernel)
def n1289 := cc 7 [w630,w0,w1,w2,w41,w5] [q1,q8,q212,q265] [] (by decide +kernel)
def n1290 := cc 7 [w221,w619,w1,w2,w41,w5] [q1,q212,q265] [] (by decide +kernel)
def n1291 := cc 7 [w221,w116,w0,w1,w2,w5] [q2,q79,q212,q265] [] (by decide +kernel)
def n1292 := cc 8 [w221,w0,w1,w2,w41,w79,w5] [q2,q79,q212,q265] [n1289,n1291,n1281,n1290] (by decide +kernel)
def v1487 : Closed T 8 := rotateClosed n1093 auto10 auto10ok
def v1488 : Closed T 8 := rotateClosed n1093 auto11 auto11ok
def v1489 : Closed T 8 := rotateClosed n999 auto6 auto6ok
def v1490 : Closed T 8 := rotateClosed n1286 auto6 auto6ok
def v1491 : Closed T 8 := rotateClosed n970 auto1 auto1ok
def v1492 : Closed T 8 := rotateClosed n1004 auto6 auto6ok
def v1493 : Closed T 8 := rotateClosed n1017 auto2 auto2ok
def n1293 := cc 9 [w221,w0,w1,w2,w41,w3,w4,w5] [q14,q79,q103,q148,q212,q252,q265,q272] [v1487,v1488,n357,n999,v1489,n1283,n1286,v1490,n1282,n773,n970,v1491,n1004,v1492,n1288,n1292,n1260,v1493] (by decide +kernel)
def n1294 := cc 7 [w0,w628,w1,w2,w41,w5] [q92,q168,q265,q272] [n1280] (by decide +kernel)
def n1295 := cc 7 [w116,w561,w0,w1,w2,w5] [q8,q65,q98,q224,q265] [] (by decide +kernel)
def v1494 : Closed T 7 := rotateClosed n1281 auto10 auto10ok
def v1495 : Closed T 7 := rotateClosed n1295 auto2 auto2ok
def v1496 : Closed T 7 := rotateClosed n1294 auto10 auto10ok
def n1296 := cc 8 [w168,w0,w1,w42,w3,w4,w82] [q7,q67,q99,q160,q262] [v1494,v1495,v1496] (by decide +kernel)
def v1497 : Closed T 8 := rotateClosed n1282 auto10 auto10ok
def v1498 : Closed T 8 := rotateClosed n1155 auto8 auto8ok
def n1297 := cc 9 [w168,w0,w1,w42,w2,w3,w4,w5] [q262,q271,q276,q277] [v1497,n1296,n1138,v997,v1498,v1319] (by decide +kernel)
def n1298 := cc 9 [w0,w1,w170,w2,w41,w3,w4,w5] [q14,q103,q265,q272,q278] [n1187] (by decide +kernel)
def n1299 := cc 8 [w0,w631,w1,w2,w3,w4,w5] [q7,q92,q154,q262,q271] [] (by decide +kernel)
def v1499 : Closed T 7 := rotateClosed n1175 auto11 auto11ok
def n1300 := cc 8 [w633,w0,w1,w2,w3,w4,w5] [q0,q231,q265] [v1499,v909] (by decide +kernel)
def n1301 := cc 8 [w629,w0,w1,w2,w3,w4,w5] [q102,q162,q262,q271] [] (by decide +kernel)
def n1302 := cc 8 [w0,w1,w635,w2,w3,w4,w5] [q102,q162,q166,q262] [] (by decide +kernel)
def n1303 := cc 7 [w182,w636,w0,w1,w4,w5] [q168,q262] [] (by decide +kernel)
def v1500 : Closed T 7 := rotateClosed n1303 auto1 auto1ok
def n1304 := cc 8 [w182,w0,w1,w42,w3,w4,w5] [q103,q217,q262,q271] [n1303,v1500] (by decide +kernel)
def v1501 : Closed T 8 := rotateClosed n1173 auto8 auto8ok
def v1502 : Closed T 8 := rotateClosed n997 auto8 auto8ok
def v1503 : Closed T 8 := rotateClosed n1176 auto8 auto8ok
def v1504 : Closed T 8 := rotateClosed n1300 auto4 auto4ok
def v1505 : Closed T 8 := rotateClosed n1300 auto12 auto12ok
def v1506 : Closed T 8 := rotateClosed n1299 auto8 auto8ok
def v1507 : Closed T 8 := rotateClosed n1302 auto6 auto6ok
def n1305 := cc 9 [w182,w0,w1,w2,w3,w4,w5] [q14,q103,q171,q262,q271] [n1173,v1501,n997,v1502,n1301,n1176,v1503,n359,n1187,n1304,v1504,v1505,n1299,v1506,v1507] (by decide +kernel)
def v1508 : Closed T 7 := rotateClosed n1284 auto8 auto8ok
def n1306 := cc 8 [w629,w0,w1,w2,w41,w3,w4,w5] [q2,q10,q69,q162,q262,q265,q271,q272,q275,q276] [n1284,v1508] (by decide +kernel)
def v1509 : Closed T 7 := rotateClosed n1285 auto8 auto8ok
def n1307 := cc 8 [w182,w0,w1,w42,w41,w3,w4,w5] [q14,q103,q217,q262,q265,q271,q272,q275,q276] [n1285,v1509] (by decide +kernel)
def v1510 : Closed T 8 := rotateClosed n999 auto8 auto8ok
def v1511 : Closed T 8 := rotateClosed n1286 auto8 auto8ok
def n1308 := cc 9 [w182,w0,w1,w2,w41,w3,w4,w5] [q14,q103,q217,q262,q265,q271,q272,q275,q276] [n999,v1510,n1286,v1511,n1306,n360,n1187,n1307] (by decide +kernel)
def n1309 := cc 7 [w638,w0,w1,w42,w3,w4] [q0,q72,q143,q262] [] (by decide +kernel)
def v1512 : Closed T 7 := rotateClosed n1309 auto10 auto10ok
def v1513 : Closed T 7 := rotateClosed n1265 auto2 auto2ok
def n1310 := cc 8 [w619,w0,w1,w2,w41,w5] [q1,q14,q171,q265,q272] [n1289,n1290,v1512,n361,n1262,v1513] (by decide +kernel)
def n1311 := cc 5 [w641,w1,w3,w4] [] [] (by decide +kernel)
def v1514 : Closed T 5 := rotateClosed n1311 auto2 auto2ok
def n1312 := cc 6 [w630,w642,w1,w2,w5] [q2,q82,q168,q213] [v1514] (by decide +kernel)
def n1313 := cc 7 [w630,w116,w0,w1,w2,w5] [q79,q212,q265,q272] [n1312] (by decide +kernel)
def n1314 := cc 7 [w116,w0,w642,w1,w2,w5] [q10,q92,q221,q265,q272] [n1312] (by decide +kernel)
def n1315 := cc 6 [w643,w0,w644,w2,w5] [q10,q34,q265] [] (by decide +kernel)
def n1316 := cc 7 [w643,w116,w0,w1,w2,w5] [q10,q65,q98,q205,q265] [n1315] (by decide +kernel)
def v1515 : Closed T 6 := rotateClosed n1315 auto8 auto8ok
def n1317 := cc 7 [w116,w645,w0,w1,w2,w5] [q2,q22,q182,q265] [v1515] (by decide +kernel)
def v1516 : Closed T 7 := rotateClosed n1316 auto8 auto8ok
def v1517 : Closed T 7 := rotateClosed n1313 auto8 auto8ok
def v1518 : Closed T 7 := rotateClosed n633 auto8 auto8ok
def v1519 : Closed T 7 := rotateClosed n1317 auto8 auto8ok
def v1520 : Closed T 7 := rotateClosed n1314 auto8 auto8ok
def n1318 := cc 8 [w116,w0,w1,w2,w5] [q14,q171] [n1316,v1516,n1313,v1517,n633,v1518,n362,n1317,v1519,n1314,v1520,n471] (by decide +kernel)
def n1319 := cc 7 [w621,w0,w1,w42,w3,w4] [q0,q7,q26,q113,q163] [n1263] (by decide +kernel)
def v1521 : Closed T 7 := rotateClosed n1289 auto8 auto8ok
def v1522 : Closed T 7 := rotateClosed n1291 auto8 auto8ok
def v1523 : Closed T 7 := rotateClosed n1295 auto8 auto8ok
def v1524 : Closed T 7 := rotateClosed n1247 auto8 auto8ok
def v1525 : Closed T 7 := rotateClosed n1264 auto8 auto8ok
def v1526 : Closed T 7 := rotateClosed n1319 auto2 auto2ok
def v1527 : Closed T 7 := rotateClosed n1319 auto10 auto10ok
def n1320 := cc 8 [w116,w0,w1,w2,w41,w5] [q14,q171,q265,q272] [n1289,v1521,n1291,v1522,n1295,v1523,n363,n1247,v1524,n1264,v1525,v1526,v1527] (by decide +kernel)
def v1528 : Closed T 8 := rotateClosed n1292 auto2 auto2ok
def v1529 : Closed T 8 := rotateClosed n1292 auto10 auto10ok
def v1530 : Closed T 8 := rotateClosed n1320 auto2 auto2ok
def v1531 : Closed T 8 := rotateClosed n1318 auto2 auto2ok
def v1532 : Closed T 8 := rotateClosed n634 auto8 auto8ok
def v1533 : Closed T 8 := rotateClosed n1296 auto8 auto8ok
def v1534 : Closed T 8 := rotateClosed n1248 auto8 auto8ok
def v1535 : Closed T 8 := rotateClosed n1310 auto2 auto2ok
def v1536 : Closed T 8 := rotateClosed n1310 auto10 auto10ok
def v1537 : Closed T 8 := rotateClosed n1266 auto8 auto8ok
def n1321 := cc 9 [w0,w1,w42,w3,w4,w82] [q14,q103] [v1528,v1529,v1530,v1531,n634,v1532,n1296,v1533,n364,n1248,v1534,v1535,v1536,n472,n1266,v1537] (by decide +kernel)
def n1322 := cc 5 [w647,w2,w3,w648,w4,w5] [] [n262] (by decide +kernel)
def v1538 : Closed T 5 := rotateClosed n1322 auto8 auto8ok
def n1323 := cc 6 [w0,w650,w2,w3,w117,w4,w5] [q0] [v1538] (by decide +kernel)
def n1324 := cc 6 [w651,w1,w2,w3,w117,w4,w5] [] [] (by decide +kernel)
def n1325 := cc 5 [w652,w0,w2,w3,w4,w5] [] [] (by decide +kernel)
def n1326 := cc 5 [w649,w654,w2,w3,w4,w5] [] [n262] (by decide +kernel)
def v1539 : Closed T 5 := rotateClosed n1325 auto8 auto8ok
def n1327 := cc 6 [w649,w1,w2,w3,w653,w4,w5] [] [v1539,n1326,v1538] (by decide +kernel)
def v1540 : Closed T 6 := rotateClosed n1324 auto8 auto8ok
def n1328 := cc 7 [w649,w0,w1,w2,w3,w117,w4,w5] [q0,q71,q94,q97,q155,q220] [v1540,n1327,n1323] (by decide +kernel)
def v1541 : Closed T 5 := rotateClosed n1326 auto8 auto8ok
def n1329 := cc 6 [w655,w1,w2,w3,w117,w4,w5] [q271] [v1541] (by decide +kernel)
def n1330 := cc 6 [w656,w0,w2,w3,w117,w4,w5] [] [] (by decide +kernel)
def v1542 : Closed T 6 := rotateClosed n1329 auto8 auto8ok
def n1331 := cc 7 [w0,w1,w2,w3,w117,w653,w4,w5] [q69,q81,q142,q206,q262] [n1330,n1327,v1542] (by decide +kernel)
def n1332 := cc 6 [w657,w658,w1,w2,w3,w4,w5] [] [v1539] (by decide +kernel)
def n1333 := cc 7 [w657,w0,w1,w2,w3,w117,w4,w5] [q0,q58] [n1332] (by decide +kernel)
def v1543 : Closed T 6 := rotateClosed n1332 auto8 auto8ok
def n1334 := cc 7 [w659,w0,w1,w2,w3,w117,w4,w5] [q70,q271] [v1543] (by decide +kernel)
def v1544 : Closed T 7 := rotateClosed n1333 auto8 auto8ok
def v1545 : Closed T 7 := rotateClosed n636 auto8 auto8ok
def v1546 : Closed T 7 := rotateClosed n1334 auto8 auto8ok
def v1547 : Closed T 7 := rotateClosed n1328 auto8 auto8ok
def v1548 : Closed T 7 := rotateClosed n1331 auto8 auto8ok
def n1335 := cc 8 [w0,w1,w2,w3,w117,w4,w5] [q0,q7,q69,q142,q206,q262,q271] [n1333,v1544,n636,v1545,n1334,v1546,n366,n1328,v1547,n474,n1331,v1548] (by decide +kernel)
def v1549 : Closed T 7 := rotateClosed n1287 auto2 auto2ok
def v1550 : Closed T 7 := rotateClosed n1287 auto10 auto10ok
def v1551 : Closed T 7 := rotateClosed n1269 auto8 auto8ok
def n1336 := cc 8 [w0,w1,w42,w2,w3,w117,w4,w5] [q0,q7,q142,q206,q262,q271,q275,q276] [v1549,v1550,n1269,v1551] (by decide +kernel)
def n1337 := cc 8 [w0,w1,w42,w2,w41,w3,w117,w4,w5] [q69,q142,q275,q276] [] (by decide +kernel)
def v1552 : Closed T 8 := rotateClosed n1288 auto2 auto2ok
def v1553 : Closed T 8 := rotateClosed n1288 auto8 auto8ok
def v1554 : Closed T 8 := rotateClosed n1288 auto10 auto10ok
def v1555 : Closed T 8 := rotateClosed n1278 auto2 auto2ok
def v1556 : Closed T 8 := rotateClosed n1278 auto8 auto8ok
def v1557 : Closed T 8 := rotateClosed n1278 auto10 auto10ok
def v1558 : Closed T 8 := rotateClosed n1306 auto2 auto2ok
def v1559 : Closed T 8 := rotateClosed n1301 auto2 auto2ok
def v1560 : Closed T 8 := rotateClosed n1307 auto2 auto2ok
def v1561 : Closed T 8 := rotateClosed n1307 auto3 auto3ok
def v1562 : Closed T 8 := rotateClosed n1307 auto6 auto6ok
def v1563 : Closed T 8 := rotateClosed n1304 auto2 auto2ok
def v1564 : Closed T 8 := rotateClosed n1304 auto3 auto3ok
def v1565 : Closed T 8 := rotateClosed n1304 auto6 auto6ok
def v1566 : Closed T 8 := rotateClosed n637 auto8 auto8ok
def v1567 : Closed T 8 := rotateClosed n809 auto2 auto2ok
def v1568 : Closed T 8 := rotateClosed n809 auto8 auto8ok
def v1569 : Closed T 8 := rotateClosed n809 auto10 auto10ok
def v1570 : Closed T 8 := rotateClosed n974 auto2 auto2ok
def v1571 : Closed T 8 := rotateClosed n974 auto3 auto3ok
def v1572 : Closed T 8 := rotateClosed n974 auto6 auto6ok
def v1573 : Closed T 8 := rotateClosed n974 auto8 auto8ok
def v1574 : Closed T 8 := rotateClosed n974 auto10 auto10ok
def v1575 : Closed T 8 := rotateClosed n974 auto11 auto11ok
def v1576 : Closed T 8 := rotateClosed n974 auto14 auto14ok
def v1577 : Closed T 8 := rotateClosed n1271 auto2 auto2ok
def v1578 : Closed T 8 := rotateClosed n1271 auto8 auto8ok
def v1579 : Closed T 8 := rotateClosed n1271 auto10 auto10ok
def v1580 : Closed T 8 := rotateClosed n1336 auto2 auto2ok
def n1338 := cc 9 [w0,w1,w42,w2,w41,w3,w4,w5] [q14,q103,q171,q262,q265,q271,q272,q275,q276] [n1288,v1552,v1553,v1554,n1278,v1555,v1556,v1557,n1306,v1558,n1301,v1559,n1307,v1560,v1561,v1562,n1304,v1563,v1564,v1565,n637,v1566,n367,n809,v1567,v1568,v1569,n974,v1570,v1571,v1572,v1573,v1574,v1575,v1576,n475,n1190,n1271,v1577,v1578,v1579,n1337,n1336,v1580,n1335] (by decide +kernel)
def v1581 : Closed T 9 := rotateClosed n1094 auto6 auto6ok
def v1582 : Closed T 9 := rotateClosed n1094 auto8 auto8ok
def v1583 : Closed T 9 := rotateClosed n1094 auto14 auto14ok
def v1584 : Closed T 9 := rotateClosed n1293 auto2 auto2ok
def v1585 : Closed T 9 := rotateClosed n1293 auto10 auto10ok
def v1586 : Closed T 9 := rotateClosed n1279 auto2 auto2ok
def v1587 : Closed T 9 := rotateClosed n1279 auto10 auto10ok
def v1588 : Closed T 9 := rotateClosed n1308 auto2 auto2ok
def v1589 : Closed T 9 := rotateClosed n1308 auto3 auto3ok
def v1590 : Closed T 9 := rotateClosed n1305 auto2 auto2ok
def v1591 : Closed T 9 := rotateClosed n1305 auto3 auto3ok
def v1592 : Closed T 9 := rotateClosed n638 auto8 auto8ok
def v1593 : Closed T 9 := rotateClosed n1297 auto8 auto8ok
def v1594 : Closed T 9 := rotateClosed n1142 auto8 auto8ok
def v1595 : Closed T 9 := rotateClosed n1169 auto6 auto6ok
def v1596 : Closed T 9 := rotateClosed n1169 auto8 auto8ok
def v1597 : Closed T 9 := rotateClosed n1169 auto14 auto14ok
def v1598 : Closed T 9 := rotateClosed n1177 auto2 auto2ok
def v1599 : Closed T 9 := rotateClosed n1177 auto3 auto3ok
def v1600 : Closed T 9 := rotateClosed n1177 auto10 auto10ok
def v1601 : Closed T 9 := rotateClosed n1177 auto11 auto11ok
def v1602 : Closed T 9 := rotateClosed n1249 auto8 auto8ok
def v1603 : Closed T 9 := rotateClosed n810 auto8 auto8ok
def v1604 : Closed T 9 := rotateClosed n977 auto6 auto6ok
def v1605 : Closed T 9 := rotateClosed n977 auto8 auto8ok
def v1606 : Closed T 9 := rotateClosed n977 auto14 auto14ok
def v1607 : Closed T 9 := rotateClosed n975 auto6 auto6ok
def v1608 : Closed T 9 := rotateClosed n975 auto8 auto8ok
def v1609 : Closed T 9 := rotateClosed n975 auto14 auto14ok
def v1610 : Closed T 9 := rotateClosed n1005 auto2 auto2ok
def v1611 : Closed T 9 := rotateClosed n1005 auto3 auto3ok
def v1612 : Closed T 9 := rotateClosed n1005 auto10 auto10ok
def v1613 : Closed T 9 := rotateClosed n1005 auto11 auto11ok
def v1614 : Closed T 9 := rotateClosed n1298 auto2 auto2ok
def v1615 : Closed T 9 := rotateClosed n1298 auto3 auto3ok
def v1616 : Closed T 9 := rotateClosed n1192 auto3 auto3ok
def v1617 : Closed T 9 := rotateClosed n1272 auto8 auto8ok
def v1618 : Closed T 9 := rotateClosed n1255 auto8 auto8ok
def n1339 := cc 10 [w0,w1,w42,w2,w3,w4,w5] [q14,q103,q171,q225] [n1094,v1581,v1582,v1583,v1584,v1585,v1586,v1587,v1588,v1589,v1590,v1591,n638,v1592,n1297,v1593,n1142,v1594,n1169,v1595,v1596,v1597,v1598,v1599,v1600,v1601,n368,n1249,v1602,n810,v1603,n977,v1604,v1605,v1606,n975,v1607,v1608,v1609,v1610,v1611,v1612,v1613,n476,v1614,v1615,v1373,v1616,n1272,v1617,n1338,n1321,n1255,v1618] (by decide +kernel)
def n1340 := cc 8 [w0,w1,w661,w2,w3,w4,w5] [q2,q7,q46,q130,q195] [] (by decide +kernel)
def n1341 := cc 8 [w638,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q143,q207] [n1309] (by decide +kernel)
def v1619 : Closed T 8 := rotateClosed n1341 auto10 auto10ok
def v1620 : Closed T 8 := rotateClosed n1340 auto8 auto8ok
def n1342 := cc 9 [w619,w0,w1,w2,w3,w4,w5] [q0,q14,q103,q171,q265,q272] [n639,v1619,n370,n1310,v1620] (by decide +kernel)
def n1343 := cc 8 [w0,w663,w1,w2,w3,w4,w5] [q10,q46,q153,q218] [] (by decide +kernel)
def n1344 := cc 8 [w665,w0,w1,w2,w3,w4,w5] [q0,q7,q104,q172] [] (by decide +kernel)
def v1621 : Closed T 8 := rotateClosed n1344 auto2 auto2ok
def n1345 := cc 9 [w662,w0,w1,w2,w3,w4,w5] [q10,q14,q103,q171,q265,q271] [n478,n639,v1621,n1343] (by decide +kernel)
def v1622 : Closed T 9 := rotateClosed n641 auto8 auto8ok
def v1623 : Closed T 9 := rotateClosed n1345 auto8 auto8ok
def v1624 : Closed T 9 := rotateClosed n1342 auto8 auto8ok
def v1625 : Closed T 9 := rotateClosed n1321 auto2 auto2ok
def n1346 := cc 10 [w0,w1,w2,w3,w4,w79,w5] [q14,q103,q171] [n641,v1622,n1345,v1623,n372,n1342,v1624,n479,v1625] (by decide +kernel)
def n1347 := cc 8 [w666,w0,w1,w2,w3,w4,w5] [q0,q13,q172,q226] [] (by decide +kernel)
def n1348 := cc 8 [w667,w0,w1,w2,w3,w4,w5] [q6,q96,q207,q250,q262] [] (by decide +kernel)
def v1626 : Closed T 8 := rotateClosed n643 auto14 auto14ok
def v1627 : Closed T 8 := rotateClosed n1149 auto8 auto8ok
def v1628 : Closed T 8 := rotateClosed n1347 auto8 auto8ok
def n1349 := cc 9 [w0,w453,w1,w2,w3,w4,w5] [q6,q95,q171,q225,q262] [v1626,n1348,v1100,v1627,v1628,v1105,n978,n738,n480] (by decide +kernel)
def n1350 := cc 8 [w0,w1,w670,w2,w3,w4,w5] [q0,q7,q46,q130,q262] [] (by decide +kernel)
def n1351 := cc 8 [w671,w0,w1,w2,w3,w4,w5] [q0,q7,q46,q207,q250] [] (by decide +kernel)
def v1629 : Closed T 8 := rotateClosed n1351 auto14 auto14ok
def v1630 : Closed T 8 := rotateClosed n1170 auto14 auto14ok
def v1631 : Closed T 8 := rotateClosed n836 auto6 auto6ok
def v1632 : Closed T 8 := rotateClosed n1350 auto8 auto8ok
def n1352 := cc 9 [w673,w0,w1,w2,w3,w4,w5] [q6,q14,q103,q171,q262] [n643,v1629,v1630,v957,n374,n835,v1631,v1632] (by decide +kernel)
def v1633 : Closed T 8 := rotateClosed n979 auto14 auto14ok
def n1353 := cc 9 [w0,w1,w42,w2,w3,w4,w5] [q14,q103,q171,q262,q271] [v950,v1234,n737,v1100,n375,n835,v997,n979,v1106,v1318,v1633,n1017,v1295] (by decide +kernel)
def v1634 : Closed T 8 := rotateClosed n644 auto8 auto8ok
def n1354 := cc 9 [w43,w119,w0,w1,w3,w4] [q14,q103,q171] [n644,v1634,n376,n482,v1531] (by decide +kernel)
def v1635 : Closed T 9 := rotateClosed n645 auto8 auto8ok
def v1636 : Closed T 9 := rotateClosed n1171 auto8 auto8ok
def v1637 : Closed T 9 := rotateClosed n980 auto8 auto8ok
def v1638 : Closed T 9 := rotateClosed n983 auto8 auto8ok
def v1639 : Closed T 9 := rotateClosed n1352 auto6 auto6ok
def v1640 : Closed T 9 := rotateClosed n1352 auto14 auto14ok
def v1641 : Closed T 9 := rotateClosed n1349 auto8 auto8ok
def n1355 := cc 10 [w43,w0,w1,w2,w3,w4,w5] [q103,q171,q225] [n1354,n645,v1635,n1171,v1636,n377,n980,v1637,n983,v1638,n483,v1639,v1640,n1349,v1641,n1353] (by decide +kernel)
def v1642 : Closed T 10 := rotateClosed n1095 auto2 auto2ok
def v1643 : Closed T 10 := rotateClosed n1095 auto3 auto3ok
def v1644 : Closed T 10 := rotateClosed n1095 auto6 auto6ok
def v1645 : Closed T 10 := rotateClosed n1095 auto8 auto8ok
def v1646 : Closed T 10 := rotateClosed n1095 auto10 auto10ok
def v1647 : Closed T 10 := rotateClosed n1095 auto11 auto11ok
def v1648 : Closed T 10 := rotateClosed n1095 auto14 auto14ok
def v1649 : Closed T 10 := rotateClosed n1355 auto2 auto2ok
def v1650 : Closed T 10 := rotateClosed n1355 auto3 auto3ok
def v1651 : Closed T 10 := rotateClosed n1355 auto6 auto6ok
def v1652 : Closed T 10 := rotateClosed n1229 auto1 auto1ok
def v1653 : Closed T 10 := rotateClosed n1229 auto2 auto2ok
def v1654 : Closed T 10 := rotateClosed n1229 auto3 auto3ok
def v1655 : Closed T 10 := rotateClosed n1229 auto4 auto4ok
def v1656 : Closed T 10 := rotateClosed n1229 auto5 auto5ok
def v1657 : Closed T 10 := rotateClosed n1229 auto6 auto6ok
def v1658 : Closed T 10 := rotateClosed n1229 auto7 auto7ok
def v1659 : Closed T 10 := rotateClosed n646 auto8 auto8ok
def v1660 : Closed T 10 := rotateClosed n1184 auto2 auto2ok
def v1661 : Closed T 10 := rotateClosed n1184 auto3 auto3ok
def v1662 : Closed T 10 := rotateClosed n1184 auto6 auto6ok
def v1663 : Closed T 10 := rotateClosed n1184 auto8 auto8ok
def v1664 : Closed T 10 := rotateClosed n1184 auto10 auto10ok
def v1665 : Closed T 10 := rotateClosed n1184 auto11 auto11ok
def v1666 : Closed T 10 := rotateClosed n1184 auto14 auto14ok
def v1667 : Closed T 10 := rotateClosed n1013 auto2 auto2ok
def v1668 : Closed T 10 := rotateClosed n1013 auto3 auto3ok
def v1669 : Closed T 10 := rotateClosed n1013 auto6 auto6ok
def v1670 : Closed T 10 := rotateClosed n1013 auto8 auto8ok
def v1671 : Closed T 10 := rotateClosed n1013 auto10 auto10ok
def v1672 : Closed T 10 := rotateClosed n1013 auto11 auto11ok
def v1673 : Closed T 10 := rotateClosed n1013 auto14 auto14ok
def v1674 : Closed T 10 := rotateClosed n1196 auto1 auto1ok
def v1675 : Closed T 10 := rotateClosed n1196 auto4 auto4ok
def v1676 : Closed T 10 := rotateClosed n1196 auto5 auto5ok
def v1677 : Closed T 10 := rotateClosed n1339 auto2 auto2ok
def v1678 : Closed T 10 := rotateClosed n1062 auto2 auto2ok
def v1679 : Closed T 10 := rotateClosed n1062 auto3 auto3ok
def v1680 : Closed T 10 := rotateClosed n1062 auto6 auto6ok
def v1681 : Closed T 10 := rotateClosed n1062 auto8 auto8ok
def v1682 : Closed T 10 := rotateClosed n1062 auto10 auto10ok
def v1683 : Closed T 10 := rotateClosed n1062 auto11 auto11ok
def v1684 : Closed T 10 := rotateClosed n1062 auto14 auto14ok
def v1685 : Closed T 10 := rotateClosed n1205 auto1 auto1ok
def v1686 : Closed T 10 := rotateClosed n1205 auto4 auto4ok
def v1687 : Closed T 10 := rotateClosed n1205 auto5 auto5ok
def v1688 : Closed T 10 := rotateClosed n1346 auto2 auto2ok
def n1356 := cc 11 [w0,w1,w2,w3,w4,w5] [] [n1095,v1642,v1643,v1644,v1645,v1646,v1647,v1648,n1355,v1649,v1650,v1651,n1229,v1652,v1653,v1654,v1655,v1656,v1657,v1658,n646,v1659,n1184,v1660,v1661,v1662,v1663,v1664,v1665,v1666,n378,n1013,v1667,v1668,v1669,v1670,v1671,v1672,v1673,n484,n1196,v1674,v1675,v1676,n1339,v1677,n1062,v1678,v1679,v1680,v1681,v1682,v1683,v1684,n1205,v1685,v1686,v1687,n1346,v1688] (by decide +kernel)
theorem independentlyEnumeratedBound : Lower true R T 12 :=
  fromClosed n1356 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 7, 6), (0xcccccccccccccccc, 7, 5), (0xf0f0f0f0f0f0f0f0, 7, 3), (0xff00ff00ff00ff00, 11, 3), (0xffff0000ffff0000, 19, 3), (0xffffffff00000000, 35, 3)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide +kernel)
end B51

def fullRoots : List Sig := inputs
def fullWord : Sig := 0xfee8e8e8ee888880
theorem fullBound : Lower true fullRoots fullWord 12 := by
  intro p bank h hit
  have hlow := B51.independentlyEnumeratedBound p bank h hit
  omega
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276676840 * 2 ^ 32 + 4001925248)
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
  unfold PEqualNP.Outside.L_meta_47959.Model.Repr at out
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

def mono : List Gate := [⟨.or, [3, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [0, 12]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [14, 17]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 18⟩ (List.ofFn x) = posted x := by decide +kernel

theorem solve (low : Lower true fullRoots fullWord 12) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4001925248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4001925248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_47959

open PEqualNP.Outside.L_meta_47959 in
theorem PEqualNP.Outside.L_meta_47959 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4001925248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4001925248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact solve fullBound

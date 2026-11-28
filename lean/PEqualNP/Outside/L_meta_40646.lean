import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40646.Model
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

abbrev SwapList (T : Sig) := {xs : List Move // autoOK T xs = true}

structure Archive (raw : List Sig) (T : Sig) (p q : Fin 128 → Row) where
  wires : Array (Observed p q)
  pools : Array (ChosenPool raw T)
  maps : Array (SwapList T)
  width : Nat
  count : Nat → Nat
  row : Nat → Nat → Nat
  address : Nat → Nat → Nat
  candidates : Nat → Nat → Nat → List Nat

def indices (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, v => if v=0 then [] else ((v &&& ((1 <<< width)-1))-1)::indices width n (v >>> width)

def Archive.items {raw T p q} (g : Archive raw T p q) (k i : Nat) :=
  (indices g.width 20 (g.row k i)).filterMap (fun j => g.wires[j]?)

def Archive.vals {raw T p q} (g : Archive raw T p q) (k i : Nat) :=
  ((g.items k i).map Subtype.val).map Prod.fst

def Archive.pick {raw T p q} (g : Archive raw T p q) (k i tag : Nat) :=
  ((g.candidates k i tag).filterMap (fun n => g.pools[n]?)).map Subtype.val

def Archive.links {raw T p q} (g : Archive raw T p q) (k tag : Nat) : List (List Sig) :=
  let a := g.address k tag
  let n := a/16-1
  let j := n/g.maps.size
  if a<16 ∨ a % 16 ≠ tag % 13 ∨ g.count k ≤ j then [] else
    match g.maps[n % g.maps.size]? with
    | none => []
    | some m => [(g.vals k j).map (movedWord m.val.reverse)]

def Archive.check {raw T p q} (g : Archive raw T p q) (k i : Nat) : Bool :=
  let ws := (g.items k i).map Subtype.val
  decide (g.vals k i).Nodup && !(g.vals k i).contains T &&
    testAll (k,ws.length,ws,preCov true ws,g.pick k i,g.links (k-1)) ws

theorem Archive.sound {raw T p q} (g : Archive raw T p q) (pn : properPairs T p q) (k : Nat)
    (all : ∀ j ≤ k, ∀ i < g.count j, g.check j i = true) :
    ∀ i < g.count k, Impossible true T k (g.vals k i).toFinset := by
  induction k with
  | zero =>
    intro i hi t ht run
    have e : t=0 := by omega
    subst t
    have h := all 0 (by omega) i hi
    simp only [Archive.check,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    generalize he : (g.vals 0 i).toFinset = S at run
    obtain ⟨eq,_⟩ := run
    exact h.1.2 (List.mem_toFinset.mp (by rw [he,eq]; exact Finset.mem_singleton_self _))
  | succ k ih =>
    intro i hi
    have h := all (k+1) (by omega) i hi
    simp only [Archive.check,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    apply node_sound (raw := raw) pn _ h.1.1 h.1.2 _ _ h.2
    · intro x hx
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
      exact w.property
    · intro tag c hc
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hc
      exact v.property
    · intro tag xs hx
      unfold Archive.links at hx
      dsimp only at hx
      split at hx
      · simp at hx
      · rename_i hlt
        simp only [not_or,not_le] at hlt
        split at hx
        · simp at hx
        · rename_i m hm
          obtain rfl := List.mem_singleton.mp hx
          exact rotate_excluded (ih (fun j hj => all j (by omega)) _ hlt.2.2) m.val m.property

def scan (f : Nat → Bool) (a : Nat) : Nat → Bool
  | 0 => true
  | n+1 => f (a+n) && scan f a n

def Span (f : Nat → Bool) (a n : Nat) := ∀ i, a ≤ i → i < a+n → f i = true
theorem scan_ok {f a n} (ok : scan f a n = true) : Span f a n := by
  induction n with
  | zero => intro i lo hi; omega
  | succ n ih =>
    intro i lo hi
    simp only [scan,Bool.and_eq_true] at ok
    by_cases h : i=a+n
    · exact h ▸ ok.1
    · exact ih ok.2 i lo (by omega)

theorem adjacent {f a b c} (x : Span f a b) (y : Span f (a+b) c) : Span f a (b+c) := by
  intro i lo hi
  by_cases h : i<a+b
  · exact x i lo h
  · exact y i (by omega) (by omega)

def fourWords (a b c d : Nat) := (((a <<< 64 ||| b) <<< 64 ||| c) <<< 64) ||| d
def packedEntry (w : Nat → Nat) (pos width : Nat) : Nat :=
  let j := pos/256
  let s := pos % 256
  let mask := (1 <<< width)-1
  let lo := w j >>> s
  if s+width ≤ 256 then lo &&& mask else (lo ||| (w (j+1) <<< (256-s))) &&& mask

def readField (w : Nat → Nat) (p n b : Nat) : List Nat :=
  (List.range n).map (fun j => packedEntry w (p+j*b) b)

def cutPrefix {raw T d n} (s : Slice true raw T d n) (cs : List Choice)
    (ok : makePool true d raw cs = some (cs.reverse.map choiceVal ++ raw) := by decide +kernel) :=
  prefixPool s cs ok

end PEqualNP.Outside.L_meta_40646.Model
namespace PEqualNP.Outside.L_meta_40646
open PEqualNP.Outside.L_meta_40646.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
def T : Sig := 0xe8a8e8a8e8a8e8a8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 6, 14)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 6, 14)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B1

namespace B2
def R : List Sig := vars 23
def T : Sig := 0xe8e8a8a8e8e8a8a8
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B2

namespace B3
def R : List Sig := vars 39
def T : Sig := 0xe8e8e8e8a8a8a8a8
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 83]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B3

namespace B4
def R : List Sig := vars 31
def T : Sig := 0xe8e8e8a8e8e8e8a8
theorem low : Lower true R T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 8 16) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 6, 14), (0xffff0000ffff0000, 6, 22)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 6, 14), (0xffff0000ffff0000, 6, 22)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide
  rw [he] at h
  exact h
end B4

namespace B5
def R : List Sig := vars 55
def T : Sig := 0xe8e8e8e8e8e8a8a8
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 83]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B4.low
end B5

namespace B6
def R : List Sig := vars 27
def T : Sig := 0xee88aa88ee88aa88
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67, swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B6

namespace B7
def R : List Sig := vars 43
def T : Sig := 0xee88ee88aa88aa88
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 83, swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B7

namespace B8
def R : List Sig := vars 59
def T : Sig := 0xee88ee88ee88aa88
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 83, swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B4.low
end B8

namespace B9
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
def v0 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
theorem low : Lower true R T 5 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B9

namespace B10
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
end B10

namespace B11
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B11

namespace B12
def R : List Sig := vars 23
def T : Sig := 0xeeeeeaeaeeeeeaea
theorem low : Lower true R T 3 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 4, 6), (0xf0f0f0f0f0f0f0f0, 2, 6), (0xffff0000ffff0000, 2, 18)] (by decide +kernel)
end B12

namespace B13
def R : List Sig := vars 28
def T : Sig := 0xfff0f000fff0f000
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B13

namespace B14
def R : List Sig := vars 31
def T : Sig := 0xeee8eaa8eee8eaa8
def P : Nat → Bits
  | 0 => ((0xffffff8381fe3fc7 : BitVec 64) ++ (0xfe3fffe3fd6f7fc0 : BitVec 64))
  | 1 => ((0xfc7e3fcfe1fc3f8 : BitVec 64) ++ (0x7fc38e3c3e93a4ff : BitVec 64))
  | 2 => ((0xf007fc1dffe003ff : BitVec 64) ++ (0x8ffc0fccc31cc70f : BitVec 64))
  | 3 => ((0xfff80066fffffc00 : BitVec 64) ++ (0xffff01703e0f833 : BitVec 64))
  | 4 => ((0x78ffffffff : BitVec 64) ++ (0xf000001803ff003c : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x8201005000440480 : BitVec 64) ++ (0x9004820290250940 : BitVec 64))
  | 1 => ((0x648a442c160a4148 : BitVec 64) ++ (0x264104016c0224bf : BitVec 64))
  | 2 => ((0x219480a3aaa02255 : BitVec 64) ++ (0xaa8299c4718c605 : BitVec 64))
  | 3 => ((0x4900c90bcd32a804 : BitVec 64) ++ (0xd32609d0bc0f012 : BitVec 64))
  | 4 => ((0x8e271257f1dd33a6 : BitVec 64) ++ (0x4020411eb3ff0028 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
theorem s0 : Slice true R T 0xff00ff00ff00ff 5 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B2.low
def p0 : Pool R T := prefixPool s0 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (0, 0xcccccccccccccccc, 0xfffafffafffafffa)] (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff00 3 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B12.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0x4444444444444444 4 :=
  slice_correct (ms := fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xffff0000ffff 5 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B9.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0xff000000ff0000 4 :=
  slice_correct (ms := fixRows 8 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
def w5 := combineObserved 1 w0 w2
def w6 := combineObserved 1 w5 w3
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3, w6, w4]
  (fun h => chooseRoute #[(joinPools p0 p1), (usePool p2), (usePool p3), (usePool p4)] #[] ((((0x48c : Nat) >>> ((h % 7) * 2)) &&& 3))) (by decide +kernel)
def w7 := combineObserved 2 w5 w3
def v1 : Closed T 5 := closeState (raw := R) properPN 5 [w7, w0, w1, w2, w3, w4]
  (fun _ => ([], [])) (by decide +kernel)
def w8 := combineObserved 2 w1 w3
def w9 := combineObserved 1 w8 w2
def v2 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w9, w3, w4]
  (fun _ => ([], [])) (by decide +kernel)
def w10 := combineObserved 2 w8 w2
def v3 : Closed T 5 := closeState (raw := R) properPN 5 [w10, w0, w1, w2, w3, w4]
  (fun _ => ([(usePool p4), (usePool p3)], [])) (by decide +kernel)
def w11 := combineObserved 1 w2 w3
def w12 := combineObserved 3 w0 w11
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w12, w0, w1, w2, w3, w4]
  (fun _ => ([(usePool p3), (usePool p4)], [])) (by decide +kernel)
def w13 := combineObserved 0 w1 w11
def v5 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w13, w1, w2, w3, w4]
  (fun _ => ([(usePool p3), (usePool p4)], [])) (by decide +kernel)
theorem s5 : Slice true R T 0xf0f00000f0f0000 4 :=
  slice_correct (ms := fixRows 4 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B11.low
def p5 : Pool R T := prefixPool s5 [] (by decide +kernel)
theorem s6 : Slice true R T 0xffff0000ffff 6 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
def p6 : Pool R T := prefixPool s6 [(1, 0xaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0), (1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def v6 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w5, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p5), (joinPools p6 p5), (usePool p4), (usePool p3)] #[v1, v0] ((((((0x8500 : Nat) <<< 64) ||| 0x3004003c0c600003) >>> (((h / 9 + (((0x800002100 : Nat) >>> ((h % 9) * 4)) &&& 15)) % 31) * 3)) &&& 7))) (by decide +kernel)
def w14 := combineObserved 1 w0 w4
def v7 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w14]
  (fun h => chooseRoute #[(usePool p2), (usePool p4), (usePool p3)] #[] ((((((0x10580 : Nat) <<< 64) ||| 0x500544041104a444) >>> (((h / 14 + (((0x3101009600 : Nat) >>> ((h % 14) * 3)) &&& 7)) % 42) * 2)) &&& 3))) (by decide +kernel)
def p7 : Pool R T := prefixPool s6 [(2, 0xcccccccccccccccc, 0xff00ff00ff00ff00), (1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def v8 : Closed T 6 := closeState (raw := R) properPN 6 [w8, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p4), (usePool p5), (usePool p3), (joinPools p7 p4)] #[v3, v2] ((((((0x1e002ac : Nat) <<< 64) ||| 0x2008040208109200) >>> (((h / 10 + (((0x5200258 : Nat) >>> ((h % 10) * 3)) &&& 7)) % 30) * 3)) &&& 7))) (by decide +kernel)
def w15 := combineObserved 2 w1 w4
def v9 : Closed T 6 := closeState (raw := R) properPN 6 [w15, w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p4), (usePool p2), (usePool p3)] #[] ((((((0x10044 : Nat) <<< 64) ||| 0x802400110008054) >>> (((h / 14 + (((0x6005018880 : Nat) >>> ((h % 14) * 3)) &&& 7)) % 41) * 2)) &&& 3))) (by decide +kernel)
def p8 : Pool R T := prefixPool s6 [(1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (1, 0xaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00)] (by decide +kernel)
def p9 : Pool R T := prefixPool s6 [(1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def p10 : Pool R T := prefixPool s6 [(1, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (2, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def v10 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w11, w4]
  (fun h => chooseRoute #[(joinPools p6 p5), (usePool p5), (joinPools p8 p4), (usePool p4), (usePool p2), (usePool p9), (joinPools p10 p5), (joinPools p7 p4), (usePool p3)] #[v3, v4, v5, v0] ((((((((0x3245333056310 : Nat) <<< 64) ||| 0x30338080913430a) <<< 64) ||| 0x4703b308305c3413) >>> (((h / 13 + (((0x51a6b6410000 : Nat) >>> ((h % 13) * 4)) &&& 15)) % 46) * 4)) &&& 15))) (by decide +kernel)
def p11 : Pool R T := prefixPool s6 [] (by decide +kernel)
def a0 : List Move := [swapRows 50]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 6 := rotateClosed v8 a0 a0ok
def r1 : Closed T 6 := rotateClosed v6 a0 a0ok
def v11 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p5), (usePool p4), (usePool p3), (usePool p11)] #[v9, v8, r0, v6, r1, v10, v7] ((((((((0x3036000331240 : Nat) <<< 64) ||| 0x5023920420b20071) <<< 64) ||| 0x2023280022a1303) >>> (((h / 15 + (((0x2155238300313c0 : Nat) >>> ((h % 15) * 4)) &&& 15)) % 45) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 8 :=
  fromClosed v11 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9), (0xffff0000ffff0000, 6, 22)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B14

namespace B15
def R : List Sig := vars 47
def T : Sig := 0xeee8eee8eaa8eaa8
theorem low : Lower true R T 8 := by
  exact lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B14.low
end B15

namespace B16
def R : List Sig := vars 31
def T : Sig := 0xe8a8a8a8e8a8a8a8
theorem low : Lower true R T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 0 24) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 22, 30), (0xffff0000ffff0000, 14, 30)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 22, 30), (0xffff0000ffff0000, 14, 30)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide
  rw [he] at h
  exact h
end B16

namespace B17
def R : List Sig := vars 61
def T : Sig := 0xfaa0aaa0aaa0aaa0
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 83, swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B16.low
end B17

namespace B18
def R : List Sig := vars 29
def T : Sig := 0xfaa0aaa0faa0aaa0
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67, swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B18

namespace B19
def R : List Sig := vars 45
def T : Sig := 0xfaa0faa0aaa0aaa0
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 83, swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B19

namespace B20
def R : List Sig := vars 27
def T : Sig := 0xeeaaaa88eeaaaa88
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B9.low
end B20

namespace B21
def R : List Sig := vars 27
def T : Sig := 0xeeaaaa88eeaaaa88
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B10.low
end B21

namespace B22
def R : List Sig := vars 29
def T : Sig := 0xfaaaaaa0faaaaaa0
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B9.low
end B22

namespace B23
def R : List Sig := vars 29
def T : Sig := 0xfaaaaaa0faaaaaa0
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B10.low
end B23

namespace B24
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B24

namespace B25
def R : List Sig := vars 22
def T : Sig := 0xfcfcc0c0fcfcc0c0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B25

namespace B26
def R : List Sig := vars 31
def T : Sig := 0xe8a8a880e8a8a880
def P : Nat → Bits
  | 0 => ((0xffffffffdff03fff : BitVec 64) ++ (0xfffffffffffffc3f : BitVec 64))
  | 1 => ((0x7ffe07ffebffc0ff : BitVec 64) ++ (0xf1ff1f8e3e739fd7 : BitVec 64))
  | 2 => ((0x81fff81ff5ffff03 : BitVec 64) ++ (0xfe3fe3f1c79ce7eb : BitVec 64))
  | 3 => ((0x1ffffe027fffffc : BitVec 64) ++ (0x3ffc01f9e0fbcc : BitVec 64))
  | 4 => ((0xfe00000039ffffff : BitVec 64) ++ (0xffc0007e01ff03f0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x8424104be400b2c : BitVec 64) ++ (0xb24b24a490a5283f : BitVec 64))
  | 1 => ((0x14a4324914b2c055 : BitVec 64) ++ (0x5095091a6e5295d5 : BitVec 64))
  | 2 => ((0x252890d20b355502 : BitVec 64) ++ (0x642642534f18c6ea : BitVec 64))
  | 3 => ((0x59d12483a1d9a698 : BitVec 64) ++ (0x38906dfbe0fb40 : BitVec 64))
  | 4 => ((0x61e1c71c21ee38e3 : BitVec 64) ++ (0x8900007fb5ff0380 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
theorem s0 : Slice true R T 0xcccccccccccccccc 6 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B23.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xcccccccccccccccc 5 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B22.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0xaa00aa00aa00aa 4 :=
  slice_correct (ms := fixRows 8 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f0 6 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B21.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 5 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B20.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
theorem s5 : Slice true R T 0xff000000ff000000 4 :=
  slice_correct (ms := fixRows 0 24) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p5 : Pool R T := prefixPool s5 [] (by decide +kernel)
theorem s6 : Slice true R T 0xaaaa0000aaaa 4 :=
  slice_correct (ms := fixRows 16 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
def p6 : Pool R T := prefixPool s6 [] (by decide +kernel)
def v0 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2), (usePool p3), (usePool p4), (usePool p5), (usePool p6)] #[] ((((((0x30580aa95cc180 : Nat) <<< 64) ||| 0xa0054d855a7456d) >>> (((h / 14 + (((0x30606456110c02 : Nat) >>> ((h % 14) * 4)) &&& 15)) % 41) * 3)) &&& 7))) (by decide +kernel)
theorem low : Lower true R T 8 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 3, 11), (0xffff0000ffff0000, 3, 19)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B26

namespace B27
def R : List Sig := vars 62
def T : Sig := 0xfcc0ccc0ccc0c000
theorem low : Lower true R T 8 := by
  exact lower_map (ms := [swapRows 83, swapRows 49, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B26.low
end B27

namespace B28
def R : List Sig := vars 54
def T : Sig := 0xfcfcccccccccc0c0
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 67, swapRows 81, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B10.low
end B28

namespace B29
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B29

namespace B30
def R : List Sig := vars 11
def T : Sig := 0xffeeffeeffeeffee
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
end B30

namespace B31
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
    (by decide +kernel) (proper_of _ (by decide)) B29.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 1 w2 w1
def w5 := combineObserved 1 w3 w1
def w6 := combineObserved 1 w3 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w4, w5, w6]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def w7 := combineObserved 1 w3 w0
def a0 : List Move := [swapRows 32]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v0 a0 a0ok
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w7, w5]
  (fun h => chooseRoute #[(usePool p2), (usePool p1)] #[r0] ((((0x408 : Nat) >>> ((h % 6) * 2)) &&& 3))) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B11.low
def p3 : Pool R T := prefixPool s3 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xfefefefefefefefe, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 2 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B30.low
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
end B31

namespace B32
def R : List Sig := vars 31
def T : Sig := 0xfee8eee8fee8eee8
theorem low : Lower true R T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 0 16) (raw := R)
    (T := T) (xs := [(0xffff0000ffff0000, 12, 28)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B31.low
  have he : (([(0xffff0000ffff0000, 12, 28)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B32

namespace B33
def R : List Sig := vars 47
def T : Sig := 0xfee8fee8eee8eee8
theorem low : Lower true R T 8 := by
  exact lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B32.low
end B33

namespace B34
def R : List Sig := vars 30
def T : Sig := 0xfcccccc0fcccccc0
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 65, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B10.low
end B34

namespace B35
def R : List Sig := vars 31
def T : Sig := 0xfeeeeeeafeeeeeea
theorem low : Lower true R T 7 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B34.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B35

namespace B36
def R : List Sig := vars 55
def T : Sig := 0xfefeeeeeeeeeeaea
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 83]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B35.low
end B36

namespace B37
def R : List Sig := vars 58
def T : Sig := 0xffcccccccccccc00
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 66, swapRows 81, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B10.low
end B37

namespace B38
def R : List Sig := vars 59
def T : Sig := 0xffeeeeeeeeeeeeaa
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 82]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B35.low
end B38

namespace B39
def R : List Sig := vars 15
def T : Sig := 0xeee8eee8eee8eee8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B39

namespace B40
def R : List Sig := vars 60
def T : Sig := 0xfff0fff0fff0f000
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67, swapRows 82, swapRows 33, swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B39.low
end B40

namespace B41
def R : List Sig := vars 31
def T : Sig := 0xfefefeeafefefeea
theorem low : Lower true R T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 9 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xff00ff00ff00ff00, 2, 10)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B25.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1), (0xff00ff00ff00ff00, 2, 10)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide
  rw [he] at h
  exact h
end B41

namespace B42
def R : List Sig := vars 61
def T : Sig := 0xfffafffafffafaaa
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 83, swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B41.low
end B42

namespace B43
def R : List Sig := vars 63
def T : Sig := 0xfee8eee8eee8eaa8
def P : Nat → Bits
  | 0 => ((0xff1fff8fffffff00 : BitVec 64) ++ (0x3ccf4cf4cf7fc00 : BitVec 64))
  | 1 => ((0xfe07ff070381fff : BitVec 64) ++ (0xfcf33b33b33a4c3f : BitVec 64))
  | 2 => ((0xfff83ff803fe01c : BitVec 64) ++ (0x7d03cc3cc3cc73d7 : BitVec 64))
  | 3 => ((0xf00003ffffc000e3 : BitVec 64) ++ (0x8e3c0fc0fc0f83eb : BitVec 64))
  | 4 => ((0xfffffc0000000003 : BitVec 64) ++ (0xf03ff000fff003cc : BitVec 64))
  | 5 => ((0xfc : BitVec 64) ++ (0x3fffff000003f0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x1208a400950a8a00 : BitVec 64) ++ (0x4504504509400 : BitVec 64))
  | 1 => ((0x520499020101449 : BitVec 64) ++ (0x23d121121122483f : BitVec 64))
  | 2 => ((0x895502ad00a54034 : BitVec 64) ++ (0xdd428c28c28c61d5 : BitVec 64))
  | 3 => ((0xa004034e4a8040a6 : BitVec 64) ++ (0x9ea80e80e80f02ea : BitVec 64))
  | 4 => ((0xce9e7004030186db : BitVec 64) ++ (0xf43ff000fff00340 : BitVec 64))
  | 5 => ((0x1860080c0618ff : BitVec 64) ++ (0x683fffff00000380 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 63 P N 0
def w1 := inputObserved 63 P N 1
def w2 := inputObserved 63 P N 2
def w3 := inputObserved 63 P N 3
def w4 := inputObserved 63 P N 4
def w5 := inputObserved 63 P N 5
def a0 : List Move := []
theorem a0ok : autoOK T a0 = true := by decide +kernel
theorem s0 : Slice true R T 0xf0f0f0f0f0f0f0f0 7 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
def g0 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc)
def g1 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xf000f000f000f000)
def p0 := cutPrefix s0 [g0, g1]
def w6 := combineObserved 1 w0 w1
def w7 := combineObserved 0 w6 w2
def w8 := combineObserved 0 w6 w3
def w9 := combineObserved 0 w2 w3
def w10 := combineObserved 1 w0 w9
def w11 := combineObserved 0 w1 w10
def w12 := combineObserved 1 w6 w9
def w13 := combineObserved 3 w11 w12
theorem s1 : Slice true R T 0xffff0000ffff0000 8 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B33.low
def g2 : Choice := (0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00)
def g3 : Choice := (1,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00)
def g4 : Choice := (3,0xf000f000f000f000,0xfff0fff0fff0fff0)
def p1 := cutPrefix s1 [g2, g3, g4]
theorem s2 : Slice true R T 0xffffffff00000000 8 :=
  slice_correct (ms := fixRows 0 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B32.low
def p2 := cutPrefix s2 [g2, g3, g4]
def w14 := combineObserved 1 w2 w3
def w15 := combineObserved 3 w9 w14
def w16 := combineObserved 0 w15 w1
def w17 := combineObserved 1 w16 w9
def w18 := combineObserved 1 w15 w1
def w19 := combineObserved 2 w15 w1
def w20 := combineObserved 1 w19 w9
def w21 := combineObserved 2 w6 w9
theorem s3 : Slice true R T 0xcccccccccccccccc 6 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B42.low
def p3 := cutPrefix s3 []
def p4 := cutPrefix s0 [g0]
theorem s4 : Slice true R T 0xff00ff00ff00ff00 7 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B36.low
def p5 := cutPrefix s4 [g0]
def p6 := cutPrefix s4 [g0, g1]
theorem s5 : Slice true R T 0x5555555555555555 8 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
def p7 := cutPrefix s5 [g2]
theorem s6 : Slice true R T 0x5050505050505050 6 :=
  slice_correct (ms := fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B37.low
def g5 : Choice := (0,0xcccccccccccccccc,0xfaaafaaafaaafaaa)
def p8 := cutPrefix s6 [g5]
def g6 : Choice := (3,0xcccccccccccccccc,0xfaaafaaafaaafaaa)
def p9 := cutPrefix s6 [g6]
def w22 := combineObserved 3 w1 w10
def w23 := combineObserved 2 w1 w9
def w24 := combineObserved 3 w23 w6
def w25 := combineObserved 0 w1 w2
def w26 := combineObserved 1 w0 w3
def w27 := combineObserved 3 w1 w26
def w28 := combineObserved 1 w27 w25
def g7 : Choice := (0,0xcccccccccccccccc,0xff00ff00ff00ff00)
def p10 := cutPrefix s5 [g7]
def w29 := combineObserved 0 w1 w3
def w30 := combineObserved 1 w0 w29
def w31 := combineObserved 0 w30 w2
def w32 := combineObserved 1 w0 w2
theorem s7 : Slice true R T 0x3333333333333333 6 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B17.low
def g8 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)
def p11 := cutPrefix s7 [g8]
theorem s8 : Slice true R T 0xff00ff00ff00ff 6 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
def p12 := cutPrefix s8 [g8]
def g9 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00)
def p13 := cutPrefix s1 [g8, g7, g9]
theorem s9 : Slice true R T 0xffff0000ffff 8 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B15.low
def p14 := cutPrefix s9 [g8, g7, g9]
def p15 := cutPrefix s2 [g7, g9]
theorem s10 : Slice true R T 0x44444444 4 :=
  slice_correct (ms := fixRows 33 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
def p16 := cutPrefix s10 []
def p17 := cutPrefix s6 [g7]
def w33 := combineObserved 1 w0 w5
def w34 := combineObserved 3 w0 w2
def w35 := combineObserved 2 w34 w29
def p18 := cutPrefix s2 []
def w36 := combineObserved 3 w29 w2
def w37 := combineObserved 1 w36 w0
def g10 : Choice := (1,0xcccccccccccccccc,0xfaaafaaafaaafaaa)
def p19 := cutPrefix s6 [g10]
def w38 := combineObserved 1 w1 w9
def w39 := combineObserved 3 w0 w38
def g11 : Choice := (2,0xcccccccccccccccc,0xfaaafaaafaaafaaa)
def p20 := cutPrefix s6 [g11]
def w40 := combineObserved 1 w23 w0
def w41 := combineObserved 3 w0 w1
def w42 := combineObserved 2 w41 w9
theorem s11 : Slice true R T 0xf0f0f0f0f0f0f0f 6 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B8.low
def p21 := cutPrefix s11 []
def p22 := cutPrefix s0 []
def g12 : Choice := (2,0xcccccccccccccccc,0xf000f000f000f000)
def p23 := cutPrefix s9 [g2, g12, g3]
theorem s12 : Slice true R T 0xffffffff 8 :=
  slice_correct (ms := fixRows 32 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B14.low
def p24 := cutPrefix s12 [g2, g12, g3]
def p25 := cutPrefix s12 [g2, g3]
theorem s13 : Slice true R T 0xf0f00000f0f 5 :=
  slice_correct (ms := fixRows 20 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def g13 : Choice := (2,0xfcccfcccfcccfccc,0xffffffff00000000)
def p26 := cutPrefix s13 [g13]
theorem s14 : Slice true R T 0xffff000000000000 7 :=
  slice_correct (ms := fixRows 0 48) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B31.low
def p27 := cutPrefix s14 [g2, g3]
def w43 := combineObserved 2 w38 w5
def p28 := cutPrefix s9 [g2, g3, g4]
def p29 := cutPrefix s12 [g2, g3, g4]
def w44 := combineObserved 3 w15 w1
def p30 := cutPrefix s2 [g2]
theorem s15 : Slice true R T 0x4444444444444444 5 :=
  slice_correct (ms := fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B40.low
def p31 := cutPrefix s15 []
def p32 := cutPrefix s7 []
def p33 := cutPrefix s6 []
def p34 := cutPrefix s0 [g7]
def g14 : Choice := (0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)
def p35 := cutPrefix s4 [g14]
def p36 := cutPrefix s4 []
def p37 := cutPrefix s8 []
def p38 := cutPrefix s5 [g14]
def p39 := cutPrefix s5 []
def p40 := cutPrefix s1 [g0]
def p41 := cutPrefix s9 [g0]
def p42 := cutPrefix s2 [g0]
def p43 := cutPrefix s12 [g0]
def w45 := combineObserved 0 w7 w3
def g15 : Choice := (0,0xeeeeeeeeeeeeeeee,0xff00ff00ff00ff00)
def p44 := cutPrefix s6 [g15]
def w46 := combineObserved 3 w8 w2
def p45 := cutPrefix s5 [g15]
def g16 : Choice := (0,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0)
def p46 := cutPrefix s5 [g16]
theorem s16 : Slice true R T 0x5500550055005500 6 :=
  slice_correct (ms := fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B28.low
def p47 := cutPrefix s16 [g16]
def p48 := cutPrefix s16 []
def a1 : List Move := [swapRows 50]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def p49 := cutPrefix s11 [g0]
def g17 : Choice := (1,0xcccccccccccccccc,0xf000f000f000f000)
def p50 := cutPrefix s6 [g17]
def p51 := cutPrefix s6 [g12]
def p52 := cutPrefix s5 [g2, g17]
def p53 := cutPrefix s5 [g2, g12]
def g18 : Choice := (1,0xeeeeeeeeeeeeeeee,0xf000f000f000f000)
def p54 := cutPrefix s6 [g18]
def p55 := cutPrefix s9 [g2]
def p56 := cutPrefix s1 [g2]
def p57 := cutPrefix s12 [g2]
def g19 : Choice := (2,0xeeeeeeeeeeeeeeee,0xf000f000f000f000)
def p58 := cutPrefix s5 [g2, g19]
def p59 := cutPrefix s9 []
def p60 := cutPrefix s1 []
def p61 := cutPrefix s12 []
def p62 := cutPrefix s6 [g19]
def g20 : Choice := (1,0x4444444444444444,0xf000f000f000f000)
def p63 := cutPrefix s6 [g20]
def w47 := combineObserved 1 w41 w9
def g21 : Choice := (2,0x4444444444444444,0xf000f000f000f000)
def p64 := cutPrefix s6 [g21]
def g22 : Choice := (0,0xcccccccccccccccc,0xffaaffaaffaaffaa)
def g23 : Choice := (3,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)
def p65 := cutPrefix s5 [g22, g23]
def w48 := combineObserved 3 w1 w2
def w49 := combineObserved 0 w1 w26
def g24 : Choice := (3,0xcccccccccccccccc,0xfafafafafafafafa)
def p66 := cutPrefix s5 [g24, g7]
def w50 := combineObserved 3 w1 w32
def g25 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00)
def g26 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xc0c0c0c0c0c0c0c0)
def p67 := cutPrefix s0 [g25, g26]
def p68 := cutPrefix s4 [g14, g26]
def p69 := cutPrefix s1 [g14, g26]
def p70 := cutPrefix s2 [g14, g26]
def w51 := combineObserved 1 w0 w25
def p71 := cutPrefix s11 [g25]
def g27 : Choice := (3,0xc0c0c0c0c0c0c0c0,0xff00ff00ff00ff00)
def p72 := cutPrefix s6 [g27]
def g28 : Choice := (3,0xcc00cc00cc00cc00,0xf0f0f0f0f0f0f0f0)
def p73 := cutPrefix s5 [g7, g28]
def p74 := cutPrefix s1 [g7, g28]
def p75 := cutPrefix s2 [g7, g28]
def g29 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0)
def p76 := cutPrefix s8 [g29]
def p77 := cutPrefix s16 [g28]
def g30 : Choice := (3,0xcc00cc00cc00cc00,0xfafafafafafafafa)
def p78 := cutPrefix s5 [g7, g30]
def w52 := combineObserved 3 w29 w32
def g31 : Choice := (3,0xcccccccccccccccc,0xff00ff00ff00ff00)
def g32 : Choice := (3,0x3300330033003300,0xf0f0f0f0f0f0f0f0)
def p79 := cutPrefix s5 [g31, g32]
def p80 := cutPrefix s0 [g31]
def p81 := cutPrefix s4 [g29]
def p82 := cutPrefix s9 [g31, g32]
def p83 := cutPrefix s12 [g31, g32]
def w53 := combineObserved 3 w1 w3
def w54 := combineObserved 3 w53 w2
def g33 : Choice := (3,0x3300330033003300,0xfafafafafafafafa)
def p84 := cutPrefix s5 [g31, g33]
def p85 := cutPrefix s3 [g29]
def p86 := cutPrefix s16 [g33]
def w55 := combineObserved 3 w53 w32
def p87 := cutPrefix s0 [g8, g26]
def p88 := cutPrefix s11 [g8]
def p89 := cutPrefix s16 [g14]
def p90 := cutPrefix s9 [g8, g14, g26]
def p91 := cutPrefix s1 [g8, g14, g26]
def p92 := cutPrefix s9 [g2, g12]
def g34 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000)
def p93 := cutPrefix s7 [g34]
def p94 := cutPrefix s4 [g34]
def p95 := cutPrefix s0 [g34]
def p96 := cutPrefix s12 [g34]
def p97 := cutPrefix s2 [g34]
def p98 := cutPrefix s1 [g2, g12]
def p99 := cutPrefix s11 [g34]
def p100 := cutPrefix s8 [g34]
def w56 := combineObserved 3 w0 w4
def p101 := cutPrefix s1 [g7, g9]
def p102 := cutPrefix s9 [g7, g9]
def p103 := cutPrefix s12 [g7, g9]
def a2 : List Move := [swapRows 84]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def g35 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000)
def p104 := cutPrefix s8 [g35]
def p105 := cutPrefix s1 [g14]
def p106 := cutPrefix s9 [g14]
def p107 := cutPrefix s2 [g14]
def p108 := cutPrefix s12 [g14]
def w57 := combineObserved 0 w51 w3
def g36 : Choice := (0,0xc0c0c0c0c0c0c0c0,0xff00ff00ff00ff00)
def p109 := cutPrefix s5 [g14, g36]
def g37 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xc000c000c000c000)
def p110 := cutPrefix s0 [g36, g37]
def p111 := cutPrefix s4 [g14, g37]
def p112 := cutPrefix s9 [g14, g36, g37]
def p113 := cutPrefix s1 [g14, g36, g37]
def p114 := cutPrefix s12 [g14, g36, g37]
def p115 := cutPrefix s2 [g14, g36, g37]
theorem s17 : Slice true R T 0x3333000033330000 5 :=
  slice_correct (ms := fixRows 2 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B19.low
def p116 := cutPrefix s17 []
def p117 := cutPrefix s13 []
theorem s18 : Slice true R T 0x3333333300000000 5 :=
  slice_correct (ms := fixRows 2 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B18.low
def p118 := cutPrefix s18 []
theorem s19 : Slice true R T 0xf0f0f0f 5 :=
  slice_correct (ms := fixRows 36 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p119 := cutPrefix s19 []
def w58 := combineObserved 0 w25 w3
def w59 := combineObserved 1 w0 w58
def p120 := cutPrefix s11 [g35]
def p121 := cutPrefix s6 [g36]
def g38 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xffffffff00000000)
def p122 := cutPrefix s11 [g38]
def g39 : Choice := (3,0xbafabafabafabafa,0xff00ff00ff00ff00)
def p123 := cutPrefix s11 [g39]
def g40 : Choice := (1,0x30f030f030f030f0,0xaaaaaaaaaaaaaaaa)
def p124 := cutPrefix s0 [g7, g40]
def p125 := cutPrefix s4 [g8]
def p126 := cutPrefix s0 [g8]
def p127 := cutPrefix s0 [g7, g8]
def p128 := cutPrefix s9 [g8]
def p129 := cutPrefix s1 [g8]
def p130 := cutPrefix s1 [g7, g28, g8]
def g41 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xc0f0c0f0c0f0c0f0)
def p131 := cutPrefix s4 [g32, g41]
def g42 : Choice := (1,0xcccccccccccccccc,0xeafaeafaeafaeafa)
def p132 := cutPrefix s11 [g42]
def p133 := cutPrefix s0 [g31, g41]
def p134 := cutPrefix s3 [g41]
def w60 := combineObserved 1 w0 w54
def p135 := cutPrefix s2 [g31, g32]
def p136 := cutPrefix s0 [g31, g8]
def p137 := cutPrefix s3 [g8]
def p138 := cutPrefix s9 [g31, g32, g8]
def p139 := cutPrefix s1 [g2, g1]
def p140 := cutPrefix s9 [g2, g1]
def p141 := cutPrefix s2 [g2, g1]
def p142 := cutPrefix s12 [g2, g1]
def p143 := cutPrefix s4 [g1]
def p144 := cutPrefix s0 [g1]
def p145 := cutPrefix s9 [g2, g8]
def p146 := cutPrefix s1 [g2, g8]
theorem s20 : Slice true R T 0xff00000000 4 :=
  slice_correct (ms := fixRows 24 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p147 := cutPrefix s20 []
def p148 := cutPrefix s12 [g2, g12]
def p149 := cutPrefix s2 [g2, g12]
def p150 := cutPrefix s5 [g2, g3]
def p151 := cutPrefix s0 [g17]
def p152 := cutPrefix s1 [g2, g17, g3]
def p153 := cutPrefix s2 [g2, g17, g3]
def p154 := cutPrefix s9 [g2, g3]
def p155 := cutPrefix s1 [g2, g3]
def p156 := cutPrefix s2 [g2, g3]
def p157 := cutPrefix s11 [g13]
def p158 := cutPrefix s14 [g2]
def p159 := cutPrefix s0 [g12]
def p160 := cutPrefix s5 [g2, g3, g4]
def g43 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc)
def p161 := cutPrefix s2 [g43]
def p162 := cutPrefix s9 [g0, g43]
def p163 := cutPrefix s1 [g0, g43]
def p164 := cutPrefix s12 [g0, g43]
def p165 := cutPrefix s2 [g0, g43]
def p166 := cutPrefix s1 [g0, g16]
def p167 := cutPrefix s2 [g0, g16]
def p168 := cutPrefix s9 [g0, g16]
def p169 := cutPrefix s12 [g0, g16]
def g44 : Choice := (3,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0)
def p170 := cutPrefix s5 [g44]
def p171 := cutPrefix s9 [g0, g44]
def p172 := cutPrefix s1 [g0, g44]
def p173 := cutPrefix s12 [g0, g44]
def p174 := cutPrefix s2 [g0, g44]
def p175 := cutPrefix s5 [g23]
def w61 := combineObserved 3 w6 w2
def g45 : Choice := (0,0x4444444444444444,0xf0f0f0f0f0f0f0f0)
def p176 := cutPrefix s5 [g45]
def p177 := cutPrefix s9 [g43, g45]
def p178 := cutPrefix s1 [g43, g45]
def p179 := cutPrefix s12 [g43, g45]
def p180 := cutPrefix s2 [g43, g45]
def p181 := cutPrefix s0 [g43]
def w62 := combineObserved 0 w41 w2
def g46 : Choice := (3,0x4444444444444444,0xf0f0f0f0f0f0f0f0)
def p182 := cutPrefix s5 [g46]
def p183 := cutPrefix s1 [g43, g46]
def p184 := cutPrefix s2 [g43, g46]
def p185 := cutPrefix s9 [g43, g46]
def p186 := cutPrefix s12 [g43, g46]
def p187 := cutPrefix s16 [g46]
def w63 := combineObserved 3 w41 w2
def p188 := cutPrefix s4 [g43]
def p189 := cutPrefix s9 [g43]
def p190 := cutPrefix s1 [g43]
def p191 := cutPrefix s12 [g43]
def p192 := cutPrefix s16 [g23]
def p193 := cutPrefix s9 [g29, g23]
def p194 := cutPrefix s1 [g29, g23]
def p195 := cutPrefix s12 [g29, g23]
def p196 := cutPrefix s2 [g29, g23]
def p197 := cutPrefix s5 [g24]
def g47 : Choice := (0,0xcccccccccccccccc,0xfafafafafafafafa)
def p198 := cutPrefix s5 [g47]
def p199 := cutPrefix s1 [g29, g47]
def p200 := cutPrefix s2 [g29, g47]
def p201 := cutPrefix s9 [g29, g47]
def p202 := cutPrefix s12 [g29, g47]
def w64 := combineObserved 0 w1 w32
def p203 := cutPrefix s9 [g29, g24]
def p204 := cutPrefix s1 [g29, g24]
def p205 := cutPrefix s12 [g29, g24]
def p206 := cutPrefix s2 [g29, g24]
def p207 := cutPrefix s0 [g25]
def p208 := cutPrefix s9 [g25]
def p209 := cutPrefix s1 [g25]
def p210 := cutPrefix s12 [g25]
def p211 := cutPrefix s2 [g25]
def p212 := cutPrefix s4 [g23]
def p213 := cutPrefix s3 [g25]
def p214 := cutPrefix s9 [g23]
def p215 := cutPrefix s1 [g23]
def p216 := cutPrefix s12 [g23]
def p217 := cutPrefix s2 [g23]
def g48 : Choice := (0,0xffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0)
def p218 := cutPrefix s5 [g48]
def p219 := cutPrefix s1 [g25, g48]
def p220 := cutPrefix s2 [g25, g48]
def p221 := cutPrefix s9 [g25, g48]
def p222 := cutPrefix s12 [g25, g48]
def w65 := combineObserved 0 w26 w2
def g49 : Choice := (0,0x5050505050505050,0xff00ff00ff00ff00)
def p223 := cutPrefix s5 [g49]
def g50 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0)
def p224 := cutPrefix s9 [g50, g49]
def p225 := cutPrefix s1 [g50, g49]
def p226 := cutPrefix s12 [g50, g49]
def p227 := cutPrefix s2 [g50, g49]
def p228 := cutPrefix s0 [g49]
def p229 := cutPrefix s4 [g50]
def w66 := combineObserved 0 w34 w3
def p230 := cutPrefix s9 [g50, g23]
def p231 := cutPrefix s1 [g50, g23]
def p232 := cutPrefix s12 [g50, g23]
def p233 := cutPrefix s2 [g50, g23]
def p234 := cutPrefix s3 [g50]
def p235 := cutPrefix s9 [g7]
def p236 := cutPrefix s1 [g7]
def p237 := cutPrefix s12 [g7]
def p238 := cutPrefix s2 [g7]
def p239 := cutPrefix s9 [g50]
def p240 := cutPrefix s1 [g50]
def p241 := cutPrefix s12 [g50]
def p242 := cutPrefix s2 [g50]
def g51 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00)
def p243 := cutPrefix s0 [g51]
def p244 := cutPrefix s9 [g51]
def p245 := cutPrefix s1 [g51]
def p246 := cutPrefix s12 [g51]
def p247 := cutPrefix s2 [g51]
def p248 := cutPrefix s3 [g51]
def w67 := combineObserved 3 w0 w3
def p249 := cutPrefix s1 [g8, g14]
def p250 := cutPrefix s9 [g8, g14]
def p251 := cutPrefix s9 [g8, g23]
def p252 := cutPrefix s1 [g8, g23]
def p253 := cutPrefix s1 [g8, g2]
def p254 := cutPrefix s9 [g8, g2]
def p255 := cutPrefix s12 [g34, g14]
def p256 := cutPrefix s2 [g34, g14]
theorem s21 : Slice true R T 0xff000000ff 5 :=
  slice_correct (ms := fixRows 24 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B3.low
def p257 := cutPrefix s21 []
def p258 := cutPrefix s12 [g34, g23]
def p259 := cutPrefix s2 [g34, g23]
def p260 := cutPrefix s3 [g34]
def p261 := cutPrefix s12 [g34, g2]
def p262 := cutPrefix s2 [g34, g2]
def p263 := cutPrefix s0 [g26]
def p264 := cutPrefix s9 [g14, g26]
def p265 := cutPrefix s12 [g14, g26]
def g52 : Choice := (3,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0)
def p266 := cutPrefix s5 [g14, g52]
def p267 := cutPrefix s12 [g14, g52]
def p268 := cutPrefix s2 [g14, g52]
def p269 := cutPrefix s9 [g14, g52]
def p270 := cutPrefix s1 [g14, g52]
def g53 : Choice := (3,0x3030303030303030,0xff00ff00ff00ff00)
def p271 := cutPrefix s0 [g53]
def p272 := cutPrefix s0 [g36]
def p273 := cutPrefix s1 [g14, g36]
def p274 := cutPrefix s9 [g14, g36]
def p275 := cutPrefix s2 [g14, g36]
def p276 := cutPrefix s12 [g14, g36]
def g54 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xff00ff00ff00ff00)
def p277 := cutPrefix s5 [g14, g54]
def p278 := cutPrefix s0 [g54]
def p279 := cutPrefix s9 [g14, g54]
def p280 := cutPrefix s1 [g14, g54]
def p281 := cutPrefix s12 [g14, g54]
def p282 := cutPrefix s2 [g14, g54]
def w68 := combineObserved 1 w25 w3
def p283 := cutPrefix s4 [g28]
def p284 := cutPrefix s9 [g7, g28]
def p285 := cutPrefix s12 [g7, g28]
theorem s22 : Slice true R T 0xff00ff 5 :=
  slice_correct (ms := fixRows 40 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B2.low
def p286 := cutPrefix s22 []
def g55 : Choice := (1,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)
def p287 := cutPrefix s5 [g14, g55]
def p288 := cutPrefix s1 [g14, g55]
def p289 := cutPrefix s9 [g14, g55]
def p290 := cutPrefix s2 [g14, g55]
def p291 := cutPrefix s12 [g14, g55]
def w69 := combineObserved 1 w1 w2
def g56 : Choice := (1,0xcccccccccccccccc,0xff00ff00ff00ff00)
def p292 := cutPrefix s5 [g56]
def p293 := cutPrefix s0 [g56]
def p294 := cutPrefix s9 [g56]
def p295 := cutPrefix s1 [g56]
def p296 := cutPrefix s12 [g56]
def p297 := cutPrefix s2 [g56]
def w70 := combineObserved 1 w1 w3
def p298 := cutPrefix s5 [g7, g23]
def p299 := cutPrefix s5 [g55]
def g57 : Choice := (2,0xcccccccccccccccc,0xff00ff00ff00ff00)
def p300 := cutPrefix s6 [g57]
def p301 := cutPrefix s4 [g55]
def p302 := cutPrefix s0 [g57]
def p303 := cutPrefix s9 [g55]
def p304 := cutPrefix s1 [g55]
def p305 := cutPrefix s12 [g55]
def p306 := cutPrefix s2 [g55]
def p307 := cutPrefix s5 [g57]
def p308 := cutPrefix s9 [g57]
def p309 := cutPrefix s1 [g57]
def p310 := cutPrefix s12 [g57]
def p311 := cutPrefix s2 [g57]
def w71 := combineObserved 2 w1 w3
def g58 : Choice := (0,0xffccffccffccffcc,0xf0f0f0f0f0f0f0f0)
def p312 := cutPrefix s5 [g56, g58]
def p313 := cutPrefix s1 [g56, g58]
def p314 := cutPrefix s9 [g56, g58]
def p315 := cutPrefix s2 [g56, g58]
def p316 := cutPrefix s12 [g56, g58]
def w72 := combineObserved 0 w70 w2
def g59 : Choice := (2,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)
def g60 : Choice := (3,0xc0c0c0c0c0c0c0c,0xcccccccccccccccc)
def p317 := cutPrefix s5 [g59, g60]
def p318 := cutPrefix s1 [g59, g60]
def p319 := cutPrefix s9 [g59, g60]
def p320 := cutPrefix s2 [g59, g60]
def p321 := cutPrefix s12 [g59, g60]
def g61 : Choice := (3,0xcc00cc00cc00cc,0xf0f0f0f0f0f0f0f0)
def p322 := cutPrefix s5 [g57, g61]
def p323 := cutPrefix s1 [g57, g61]
def p324 := cutPrefix s9 [g57, g61]
def p325 := cutPrefix s2 [g57, g61]
def p326 := cutPrefix s12 [g57, g61]
def w73 := combineObserved 3 w71 w2
def p327 := cutPrefix s5 [g57, g31]
def p328 := cutPrefix s9 [g57, g31]
def p329 := cutPrefix s1 [g57, g31]
def p330 := cutPrefix s12 [g57, g31]
def p331 := cutPrefix s2 [g57, g31]
def g62 : Choice := (1,0x3030303030303030,0xaaaaaaaaaaaaaaaa)
def p332 := cutPrefix s1 [g23, g62]
def p333 := cutPrefix s2 [g23, g62]
def p334 := cutPrefix s0 [g62]
def p335 := cutPrefix s9 [g23, g62]
def p336 := cutPrefix s12 [g23, g62]
def w74 := combineObserved 1 w48 w0
def g63 : Choice := (0,0x3030303030303030,0xff00ff00ff00ff00)
def p337 := cutPrefix s5 [g23, g63]
def p338 := cutPrefix s9 [g23, g63]
def p339 := cutPrefix s1 [g23, g63]
def p340 := cutPrefix s12 [g23, g63]
def p341 := cutPrefix s2 [g23, g63]
def p342 := cutPrefix s0 [g63]
def w75 := combineObserved 0 w48 w3
def g64 : Choice := (1,0x3030303030303030,0xff00ff00ff00ff00)
def p343 := cutPrefix s5 [g23, g64]
def p344 := cutPrefix s0 [g64]
def p345 := cutPrefix s9 [g23, g64]
def p346 := cutPrefix s1 [g23, g64]
def p347 := cutPrefix s12 [g23, g64]
def p348 := cutPrefix s2 [g23, g64]
def w76 := combineObserved 1 w48 w3
def p349 := cutPrefix s4 [g32]
def p350 := cutPrefix s1 [g31, g32]
def p351 := cutPrefix s5 [g23, g53]
def p352 := cutPrefix s9 [g23, g53]
def p353 := cutPrefix s1 [g23, g53]
def p354 := cutPrefix s12 [g23, g53]
def p355 := cutPrefix s2 [g23, g53]
def w77 := combineObserved 3 w48 w3
def p356 := cutPrefix s4 [g17]
def p357 := cutPrefix s1 [g2, g17]
def p358 := cutPrefix s9 [g2, g17]
def p359 := cutPrefix s2 [g2, g17]
def p360 := cutPrefix s12 [g2, g17]
def p361 := cutPrefix s4 [g12]
def g65 : Choice := (0,0xcccccccccccccccc,0xfff0fff0fff0fff0)
def p362 := cutPrefix s5 [g3, g65]
def p363 := cutPrefix s1 [g3, g65]
def p364 := cutPrefix s9 [g3, g65]
def p365 := cutPrefix s2 [g3, g65]
def p366 := cutPrefix s12 [g3, g65]
def w78 := combineObserved 0 w1 w14
def g66 : Choice := (3,0xcccccccccccccccc,0xfff0fff0fff0fff0)
def p367 := cutPrefix s5 [g3, g66]
def p368 := cutPrefix s9 [g3, g66]
def p369 := cutPrefix s1 [g3, g66]
def p370 := cutPrefix s12 [g3, g66]
def p371 := cutPrefix s2 [g3, g66]
def w79 := combineObserved 3 w1 w14
def g67 : Choice := (2,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00)
def g68 : Choice := (1,0xf000f000f000f0,0xcccccccccccccccc)
def p372 := cutPrefix s5 [g67, g68]
def p373 := cutPrefix s0 [g68]
def p374 := cutPrefix s1 [g67, g68]
def p375 := cutPrefix s9 [g67, g68]
def p376 := cutPrefix s2 [g67, g68]
def p377 := cutPrefix s12 [g67, g68]
def w80 := combineObserved 2 w2 w3
def w81 := combineObserved 1 w80 w1
def g69 : Choice := (2,0xff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0)
def g70 : Choice := (3,0xf000f000f000f00,0xcccccccccccccccc)
def p378 := cutPrefix s5 [g69, g70]
def p379 := cutPrefix s4 [g70]
def p380 := cutPrefix s1 [g69, g70]
def p381 := cutPrefix s9 [g69, g70]
def p382 := cutPrefix s2 [g69, g70]
def p383 := cutPrefix s12 [g69, g70]
def w82 := combineObserved 2 w3 w2
def w83 := combineObserved 3 w82 w1
def g71 : Choice := (3,0xf000f000f000f0,0xf0f0f0f0f0f0f0f0)
def p384 := cutPrefix s5 [g67, g71]
def p385 := cutPrefix s1 [g67, g71]
def p386 := cutPrefix s9 [g67, g71]
def p387 := cutPrefix s2 [g67, g71]
def p388 := cutPrefix s12 [g67, g71]
def p389 := cutPrefix s1 [g29]
def p390 := cutPrefix s2 [g29]
def p391 := cutPrefix s9 [g29]
def p392 := cutPrefix s12 [g29]
def p393 := cutPrefix s5 [g3]
def p394 := cutPrefix s1 [g3]
def p395 := cutPrefix s9 [g3]
def p396 := cutPrefix s2 [g3]
def p397 := cutPrefix s12 [g3]
def p398 := cutPrefix s5 [g67]
def p399 := cutPrefix s9 [g67]
def p400 := cutPrefix s1 [g67]
def p401 := cutPrefix s12 [g67]
def p402 := cutPrefix s2 [g67]
def data0 : Array Nat := #[fourWords 0x5a57888590001250 0x10b12a613640056 0x57962608b50f07c2 0x71e848305080c101, fourWords 0x10c142030405506 0xa101870405d97ec 0x112c5323c6517094 0x90008c0007c2a5a9, fourWords 0x18202182840608d0 0x100182030405c804 0x4142030404305080 0xc1014618284420c1, fourWords 0x18203443051e101 0x8202182840628101 0xc1420304058860a 0x1018203203050918, fourWords 0x8240b0483e3010af 0x440bf5f2804e3e1e 0x8f04816090c04229 0x18ac502a13860a1, fourWords 0x7c3d1e09024300b3 0xbc2af110bc1e4271 0x20f87a3c090c3158 0xbc46242c271f0f47, fourWords 0xc2c3e1e8f04e2409 0x544016351b04c69 0x358f460212f98078 0x2718085008113848, fourWords 0x5db23e1e8f04e160 0x90826b379a0c26d3 0x8120904e3e1e8f02 0x403984ca593110cc, fourWords 0x8587c3d1e09c2425 0xa8902c381d01c72 0x1e1f0f478271207c 0x24030a859acd857b, fourWords 0x23c8263e1e8f04e1 0x20a85b2430ca6472 0x7951209c7c3d1e04 0xb1c2410e43198dc7, fourWords 0xed0227e878ad190 0xfd2d7b1edd0f1ef 0xe3cee7cdebcceeec 0x70cc05cb098a31e9, fourWords 0x69800112c7780000 0xa95a93446f400 0x90a8cd3628446a8 0xcc90cc028c76698c, fourWords 0x60007d89f0000ff0 0x3e00000 0x158faf288c4 0x22640000006b50a6, fourWords 0x361089032f2d6a80 0x239497546cb6ac8e 0x8ced191c40009261 0x791640013af4c940, fourWords 0x5102ec84ced60000 0x94324f96a401cf22 0xf52420c8a25ca458 0xe655f6d4a62e86ee, fourWords 0xe99858904a7942cc 0x524000ce81b0e928 0xe24b0da67f4280be 0xa000000000aa4000, fourWords 0xc4020218284061c 0x11a0200305080c38 0x2544c47aaf320e80 0x74a882b1471802, fourWords 0x200305080c1017e1 0x8284062838202003 0x5080c1017c18284 0x61c402020030508, fourWords 0x80c101660030508 0xc14102003050884 0x1016218284062810 0x15400305080c1400, fourWords 0x36200305080c1018 0x600305080e102021 0x829b080c10162182 0x9b080c11a0200305, fourWords 0x5080c1016201105 0x80c11a021828406 0x80c462182840608 0xf01460030508080a, fourWords 0xa020200304062810 0x1720030406080b96 0x2003040608d01720 0x1105080c50202011, fourWords 0x305080c13b02003 0x5080c1016200305 0x808d01621828406 0xd011a0200305080d, fourWords 0xc11a02003050918 0x11a02182840608f0 0x14a00305080c1014 0xa182c5080c11a020, fourWords 0x200305080c11a020 0x305080e48202182 0x848c0c1019018284 0x608f0162182c708, fourWords 0x80c101980030508 0xc14b02003050608 0xb6901828406080b 0x19000305080e5020, fourWords 0x20200305082c1820 0x2182840738101620 0x305080c13702182 0xcd080c1016200305, fourWords 0x8406281013000305 0x80c10130182844e 0xc5020200305089c 0x1820218284160c50, fourWords 0x1540200305080e90 0x20200305080c101a 0x305080c14f020 0x60a3c50202182, fourWords 0x8580a04018804ca0 0x180a8242113a8406 0xa351290400030508 0xc5020200305080c, fourWords 0x8587c3d1e090240 0x31381150a95329c2 0xa2e528b82a6c359a 0x8d22b150a4502711, fourWords 0x200d56ad562b82a 0xaa108594ea6178ac 0x5429140982a0554a 0xa04e04018b85e251]
def data1 : Array Nat := #[fourWords 0x580c074391c0ac5 0x42914084401e1389 0x4481602810061503 0xabc4a3e1e8f04812, fourWords 0x3e1e8f0481213ad4 0x40b90aae96eb85b0 0xb84a3e1e8f04c240 0x90556ab159ac9682, fourWords 0x816578857ebe5ea8 0x74391c09c4a240f 0x58061f5e2d42a20 0x3aed542e1287c2c, fourWords 0x8ab6128f87a3c120 0x485c2764b298e206 0x40598cc510300a85 0x138543ec161b098, fourWords 0x8d2210f8544e1610 0x33c482611ad9542e 0xa8f87a3c1289024 0x2765b3406cc67059, fourWords 0xa840d96c35dacd36 0x9345a02710858061 0xf0ab3c48af6a2c00 0x6d369345a06c359a, fourWords 0x940ee572381c4e1 0x71855be210b00c7c 0x3d1e080242767b74 0x2ade6d891b8da6aa, fourWords 0x18842c11728802a0 0xa6007dd4e51009c2 0xce67439dd21557b6 0x842031f0f4782009, fourWords 0x6b3004e211005806 0x301207de6250aabc 0x44f278bc1deee76b 0xb1d63013894481f0, fourWords 0x49205007d2c0843 0xe123b15c4e0b3f3e 0x9f22635b5154267c 0x3ddecf57a365b0d7, fourWords 0x270f84818573e9f9 0xfcfd038795492602 0x2102803e89c42120 0xf95cfcfb7e3655eb, fourWords 0x5036b2be02b03a98 0xbe5d2c0f04e210f 0x9a4c45c2f3fe006a 0x1337c429240a00ec, fourWords 0xc05f1e09c3e751c9 0x88ba5e82c1870078 0xaaa08c03017cba3 0xc13885ae1f3117a0, fourWords 0x84026632c054210b 0xf87a3c17094481f 0x91604e208385611 0x92311c4cdf1098c, fourWords 0x582a1f8643a150d8 0x78818cb03b1d0b02 0x70f85a1308361acd 0x4691708c2b072391, fourWords 0x450411085b5d542e 0x1f0f478271204842 0x3102bc2b0a8643a 0x1b0f0b42d6c2e090, fourWords 0xb9b0d66a34856371 0x90b16040233b9d8e 0xa74128f87a3c1385 0x4242388c4e2a6d89, fourWords 0x104416c773a8f87a 0x3c1389024250b470 0x451d104789215251 0x2c4b1a8c4584c248, fourWords 0x5018864524904864 0x6200b47e02763a05 0xa3d1d773b5d8eb24 0x82a3824259284a22, fourWords 0xaf128902c0a1100c 0x3e20528565529944 0x9e4a261205807263 0x61acd4692c08046a, fourWords 0x4039a4ce6531984b 0x2d389bcda6a2097 0x4b65ea50acaddced 0x763adb2d86bb59a8, fourWords 0x4141a189a8016a14 0xf9b42e1f0f478270 0xb0480726184ee7a1 0x59d4f27224528904, fourWords 0x478270b04a5e1518 0x828d48a25168e24 0x85ad8d2251f0f478 0x27120485c2310cfc, fourWords 0x32934ba68914a230 0xace26f369acd1b2d 0x86bb595e240b4bc0 0x6206a301b4b61f0f, fourWords 0xad954a0170587c3d 0x1e09448126009c3e 0x3a8546a415a753d 0x5ea51280c6020a55, fourWords 0x2080075aaed6c2cd 0x4600567d101f0f47 0x8270900c4ad4ac07 0xea956a9d56ae1562, fourWords 0x1007c7c3d1e09c48 0x120185abe4f1293a 0xc051431482b10af5 0x72b2d96c35dacaf1, fourWords 0x54723d168d452300 0xe24b3592c2d96c35 0xdacd457d884003b2 0xd8c2c1f0a9dcea2e, fourWords 0x24108591a8c45a28 0x74391c0791e8e0a8 0x1dbe2410859b43e1 0xe8f04012018944e1, fourWords 0x4391c07848160a89 0xc7c3d1e0484816b3 0xa584a1fb4dac6615 0x1da2d4df6d09c4a, fourWords 0x7a3c138942415120 0x5ad89e2da4c6a614 0xa080416bb55a6d07 0x73a8cc4a07b3a587, fourWords 0x4329a10a6c2d3e3b 0x9d528933096c7439 0x1c0d44a200f01ed8 0x9e120582a763a0f8]
def data2 : Array Nat := #[fourWords 0x480621b9dd6e976b 0x90902cb6170f87a3 0xc138484220b7dc6d 0xd70b68902c154ca5, fourWords 0x60afb7fc08802c3e 0x1e8f04e120b5e006 0x30bd056f977bcdec 0x48b6170f87a3c138, fourWords 0xd0f87a3c13884401 0x2c18544985c3e130 0xc070b2d85c3e1e8f 0x4e24095f84a21c0, fourWords 0x8fe608da5c8bae88 0x8de8860e083ce880 0xfde7ee247c5a479d 0x267725875767c396, fourWords 0x2124af8a6acde2aa 0x7a2a8164a58f2a20 0xac9ef1a9d1e49a96 0x29832a953e8926e4, fourWords 0x626d1b6acec26cc1 0x54caae8c7deac4ea 0x4c2626bfb6cbc9da 0xbacacb7b2eb4762b, fourWords 0xe4f4966f1eaaeef6 0x4ec6ece9566e6aa4 0xe422ee0e56df5a8d 0xc8a4da02ad70e6d4, fourWords 0x9f26156da90fd81a 0x1c4a709ae5072610 0x4e6102a6100650ff 0x468fc766f9ca6f71, fourWords 0x730000003cd1a23 0x9e2e2af0000572a8 0x800502c2718e8ee 0x9ca43c2035692e1a, fourWords 0x588134089b3f8000 0xe00200380005dab 0xf038200014600000 0x2a88ca51e594828, fourWords 0x5c12db94462dcc7 0x400026180000012c 0x57a3e42cc2318b65 0x2a00035918924811, fourWords 0x48c1bcd302099f60 0xa65c61d3dad323d4 0x8cbdb69cd421b800 0x45e0fb00e5651eb2, fourWords 0x30a15bc2c800 0x43800051ab3cea0 0x375972000330a9 0xd501438b1ca694a0, fourWords 0xa101875c080860a1 0x18904680860a101 0x8704052860a1018a 0xe0950003b525300, fourWords 0x141c1000c1420b06 0x1c1060a105071008 0x860a10189100808 0x60a1018704057860, fourWords 0x60a1068314080860 0xa1018a0e04c000c1 0x42030e04c060a113 0x83141c0860a10583, fourWords 0x8a04055860a11803 0x14080860a1018a04 0x4b060a101870404 0xb000c142030404b0, fourWords 0x1000c142033c0598 0xc1420364058860 0xa1018a02a8c060a1 0x138314055060a101, fourWords 0x42030405a860a110 0x823c052800c14221 0x4052860a6c20368 0x8d000c14d8406d0, fourWords 0x8d2860a101823c05 0x2000c1420304e008 0xc1422104dc0860 0xa101823c05a800c1, fourWords 0xa1019f04052060a1 0x19f40080800c101 0x8202e4c000088284 0x6d01060a1011e02, fourWords 0x4980800c1420378 0x8080001828406f0 0x1060a101ba046808 0x60a1019f04052860, fourWords 0x441420304dc0800 0xc142037a080860a1 0x1823c9808044142 0x304052800c14203, fourWords 0x8b06080860a10583 0x404b860a1058304 0x55860a1068b0608 0x860a10583043008, fourWords 0x860a1018a040540 0x60a1018a0404b860 0xa1018a04300860a1 0x5830404c060a113, fourWords 0x420304a4085089c1 0x8a04056000c147a7 0x14080860a1138304 0x4c220a113831408, fourWords 0x31000001828a0404 0x8000c1478a0404c2 0x20a1018a0404c060 0xa1018a04a40800c1, fourWords 0x150200c5805158a8 0x5228138804c24118 0x582a250280c40160 0x28882a041087c3c0, fourWords 0xa21030002a301288 0x40e200a818002f0b 0x540a03170b44a24 0xb0142a04018902c, fourWords 0x70370f0902c361a8 0xc84a030a89c4a150 0x281040351a0cc622 0x51001c2a321889c4, fourWords 0x468152087c803b1d 0xe4701e1f80c4816 0xa89c40231f0f478 0x12138902c3b1d0e4, fourWords 0x9c3e152288042152 0x39184c1f101108a2 0x40b00c861f120584 0x421b0802a07018d]
def data3 : Array Nat := #[fourWords 0x9448231f0f47822 0x909c2c4d261244a 0x220b0804a2025928 0x4e15110589248220, fourWords 0x84aa54120803e3 0xe1e8f0244f13858a 0x6501285406522889 0xc2c4f27094481611, fourWords 0x883c400a31988c2 0x602f96c78272f174 0xb8351087c16582b9 0x584c5a2c91c2c0a1, fourWords 0xb351a4b027128904 0x61510098d0672693 0x4e220b05414160a 0x844cc65320942c15, fourWords 0x3b0a9cce2251f0f4 0x78200909cda773b1 0xd4e845129bcda153 0x7080e072389ccd86, fourWords 0x64b249f0da4d128f 0x87a3c138802a120b 0x124f67a3c9e0ee76 0x3a9d0e470371348a, fourWords 0xa625018f87a3c138 0x482c152709c4a200 0xb02892223f831048 0x1401f4ae27091f81, fourWords 0x91a8c45a284a2004 0xc2a074421c180b 0x44a05007d13848fc 0x57431390a84419b4, fourWords 0xc0e8d4622d143b1 0xa0c44e07019b42a0 0x90380c401401a351 0x88b450ec260347a3, fourWords 0xcc4e1f0f01c9e27 0x118240e03278e872 0x381389446200f020 0x2a071d8d86427100, fourWords 0xc25d2a164da69321 0x90a8d12c9449984b 0x61e0aa4922901a07 0x816571d8e872381a, fourWords 0x1389448160a81c06 0x6d1d8f87a3c13894 0x48200b05424354ea 0x50741a4e1dcea374, fourWords 0xb6bcc2c150e27c4 0x21d00808829b4d26 0x52a190c05c2c151b 0x27910571b02c6c35, fourWords 0x37850f7754d767cf 0x7580f74851736517 0x244b71913704cf6f 0x50d6e7916d58d6c8, fourWords 0x8270d819938054f7 0xf5937e1497d84b7c 0xd0b7c1c77bb057b6 0x8d7a9097a0077995, fourWords 0x255f903998e8938d 0x4478cd958b71989c 0x158858787ec387c9 0xb85f55848c983fd7, fourWords 0x719a4c0fa3c55a25 0xcba1a87a13d39ff9 0x59e91d9c99f9a7cf 0x9981b97adb95db39, fourWords 0xa238c6910d1b289 0x9b0d89b0493af05b 0xad30bac7ddaa84da 0x9acfa8b15a748da6, fourWords 0x520015880068ac51 0xcd2580f811000085 0x34d0cc529d700052 0x8cd8007a65d0471f, fourWords 0x2440202182840608 0x961a2000853a400 0x2039b3504070f 0x9c92c67e9753724, fourWords 0xa10e833404305080 0xc3990218284160c3 0x970c1420b061c606 0xa10587100830514, fourWords 0xc1420d06300860a 0x1019f0499105080c 0xf824888284067d00 0x20c142213e801060, fourWords 0x130182840604b980 0xc1422706300860a1 0x1812eac305082c1 0x825218284160c128, fourWords 0x2d02403051408090 0x281828a26080900c 0x1450202408851e9c 0x50202b03051e9c10, fourWords 0x80b8582a140904c2 0x41208844200f0703 0x4180b05028120803 0x8180a0302060a281, fourWords 0x7c55c78631f0b41e 0x6c3c0d8f8512f07 0xe3e0d8fc0d8781b0 0xe87004010d868321, fourWords 0xd09e4813c900781b 0xf0367e414fc7507 0x81b1f1c21e06cbc6 0x7978bd0f0363e2d0, fourWords 0x504048060a289812 0x21829204048060a1 0x1811c1828b12201 0x508000006b0d25bc, fourWords 0x0 0x0 0x781b3c0ddf068f03 0x6fc1101004001829]
def wordAt (i : Nat) : Nat := (if i < 64 then (if i < 32 then data0[i % 32]?.getD 0 else data1[i % 32]?.getD 0) else (if i < 96 then data2[i % 32]?.getD 0 else data3[i % 32]?.getD 0))
def countAt : Nat → Nat
  | 5 => 5
  | 6 => 23
  | 7 => 63
  | 8 => 59
  | 9 => 13
  | 10 => 1
  | _ => 0
def rowAt : Nat → Nat → Nat
  | 5, i => packedEntry wordAt (31551+i*42) 42
  | 6, i => packedEntry wordAt (29620+i*49) 49
  | 7, i => packedEntry wordAt (19755+i*56) 56
  | 8, i => packedEntry wordAt (4213+i*56) 56
  | 9, i => packedEntry wordAt (406+i*49) 49
  | 10, i => packedEntry wordAt (0+i*42) 42
  | _, _ => 0
def indexAt : Nat → Nat → Nat
  | 5, tag => let j := (tag / 2 + packedEntry wordAt (31481 + (tag % 2)*3) 3) % 8; packedEntry wordAt (31487 + j*8) 8
  | 6, tag => let j := (tag / 10 + packedEntry wordAt (29142 + (tag % 10)*6) 6) % 38; packedEntry wordAt (29202 + j*11) 11
  | 7, tag => let j := (tag / 27 + packedEntry wordAt (18354 + (tag % 27)*7) 7) % 101; packedEntry wordAt (18543 + j*12) 12
  | 8, tag => let j := (tag / 28 + packedEntry wordAt (2745 + (tag % 28)*7) 7) % 106; packedEntry wordAt (2941 + j*12) 12
  | 9, tag => let j := (tag / 8 + packedEntry wordAt (96 + (tag % 8)*5) 5) % 27; packedEntry wordAt (136 + j*10) 10
  | _, _ => 0
def candidatesAt : Nat → Nat → Nat → List Nat
  | 5,i,_ => let r := packedEntry wordAt (31788+i*17) 17; readField wordAt (r % 32768) (r / 32768) 9
  | 6,i,_ => let r := packedEntry wordAt (31044+i*19) 19; readField wordAt (r % 32768) (r / 32768) 9
  | 7,i,_ => let r := packedEntry wordAt (27882+i*20) 20; readField wordAt (r % 32768) (r / 32768) 9
  | 8,i,_ => let r := packedEntry wordAt (17174+i*20) 20; readField wordAt (r % 32768) (r / 32768) 9
  | 9,i,_ => let r := packedEntry wordAt (2537+i*16) 16; readField wordAt (r % 4096) (r / 4096) 9
  | 10,i,_ => let r := packedEntry wordAt (87+i*9) 9; readField wordAt (r % 64) (r / 64) 9
  | _,_,_ => []
def book : Archive R T (asRow P) (asRow N) := ⟨#[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83], #[(usePool p0), (usePool p1), (usePool p2), (usePool p3), (usePool p4), (usePool p5), (usePool p6), (usePool p7), (usePool p8), (usePool p9), (usePool p10), (usePool p11), (usePool p12), (usePool p13), (usePool p14), (usePool p15), (usePool p16), (usePool p17), (usePool p18), (usePool p19), (usePool p20), (usePool p21), (usePool p22), (usePool p23), (usePool p24), (usePool p25), (usePool p26), (usePool p27), (usePool p28), (usePool p29), (usePool p30), (usePool p31), (usePool p32), (usePool p33), (usePool p34), (usePool p35), (usePool p36), (usePool p37), (usePool p38), (usePool p39), (usePool p40), (usePool p41), (usePool p42), (usePool p43), (usePool p44), (usePool p45), (usePool p46), (usePool p47), (usePool p48), (joinPools p49 p50), (joinPools p49 p51), (usePool p52), (usePool p50), (usePool p53), (usePool p51), (usePool p54), (usePool p55), (usePool p56), (usePool p57), (usePool p58), (usePool p59), (usePool p60), (usePool p61), (usePool p62), (usePool p63), (usePool p64), (usePool p65), (usePool p66), (usePool p67), (usePool p68), (usePool p69), (usePool p70), (joinPools p71 p72), (usePool p73), (usePool p74), (usePool p75), (joinPools p76 p77), (usePool p78), (usePool p79), (usePool p80), (usePool p81), (usePool p82), (usePool p83), (usePool p84), (usePool p85), (usePool p86), (usePool p87), (usePool p88), (usePool p89), (usePool p90), (usePool p91), (usePool p92), (usePool p93), (usePool p94), (usePool p95), (usePool p96), (usePool p97), (usePool p98), (usePool p99), (usePool p100), (usePool p101), (usePool p102), (usePool p103), (joinPools p104 p77), (joinPools p12 p77), (usePool p105), (usePool p106), (usePool p107), (usePool p108), (usePool p109), (usePool p110), (usePool p111), (usePool p112), (usePool p113), (usePool p114), (usePool p115), (usePool p116), (usePool p117), (usePool p118), (usePool p119), (joinPools p120 p121), (joinPools p99 p121), (joinPools p88 p121), (joinPools p122 p121), (joinPools p123 p124), (usePool p125), (usePool p126), (joinPools p88 p127), (usePool p128), (usePool p129), (usePool p130), (usePool p131), (joinPools p132 p133), (usePool p134), (usePool p135), (joinPools p88 p136), (usePool p137), (usePool p138), (usePool p139), (usePool p140), (usePool p141), (usePool p142), (usePool p143), (usePool p144), (usePool p145), (usePool p146), (usePool p147), (usePool p148), (usePool p149), (usePool p150), (usePool p151), (usePool p152), (usePool p153), (usePool p154), (usePool p155), (usePool p156), (usePool p157), (usePool p158), (usePool p159), (usePool p160), (usePool p161), (usePool p162), (usePool p163), (usePool p164), (usePool p165), (joinPools p32 p3), (usePool p166), (usePool p167), (usePool p168), (usePool p169), (usePool p170), (usePool p171), (usePool p172), (usePool p173), (usePool p174), (usePool p175), (usePool p176), (usePool p177), (usePool p178), (usePool p179), (usePool p180), (usePool p181), (usePool p182), (usePool p183), (usePool p184), (usePool p185), (usePool p186), (usePool p187), (usePool p188), (usePool p189), (usePool p190), (usePool p191), (usePool p192), (usePool p193), (usePool p194), (usePool p195), (usePool p196), (usePool p197), (usePool p198), (usePool p199), (usePool p200), (usePool p201), (usePool p202), (usePool p203), (usePool p204), (usePool p205), (usePool p206), (usePool p207), (usePool p208), (usePool p209), (usePool p210), (usePool p211), (usePool p212), (usePool p213), (usePool p214), (usePool p215), (usePool p216), (usePool p217), (usePool p218), (usePool p219), (usePool p220), (usePool p221), (usePool p222), (usePool p223), (usePool p224), (usePool p225), (usePool p226), (usePool p227), (usePool p228), (usePool p229), (usePool p230), (usePool p231), (usePool p232), (usePool p233), (usePool p234), (usePool p235), (usePool p236), (usePool p237), (usePool p238), (usePool p239), (usePool p240), (usePool p241), (usePool p242), (usePool p243), (usePool p244), (usePool p245), (usePool p246), (usePool p247), (usePool p248), (usePool p249), (usePool p250), (usePool p251), (usePool p252), (usePool p253), (usePool p254), (usePool p255), (usePool p256), (usePool p257), (usePool p258), (usePool p259), (usePool p260), (usePool p261), (usePool p262), (usePool p263), (usePool p264), (usePool p265), (usePool p266), (joinPools p267 p268), (usePool p269), (usePool p270), (usePool p267), (usePool p268), (joinPools p21 p271), (usePool p272), (usePool p273), (usePool p274), (usePool p275), (usePool p276), (usePool p277), (usePool p278), (usePool p279), (usePool p280), (usePool p281), (usePool p282), (usePool p283), (usePool p284), (usePool p285), (usePool p286), (usePool p287), (usePool p288), (usePool p289), (usePool p290), (usePool p291), (usePool p292), (usePool p293), (usePool p294), (usePool p295), (usePool p296), (usePool p297), (usePool p298), (usePool p299), (usePool p300), (usePool p301), (usePool p302), (usePool p303), (usePool p304), (usePool p305), (usePool p306), (usePool p307), (usePool p308), (usePool p309), (usePool p310), (usePool p311), (usePool p312), (usePool p313), (usePool p314), (usePool p315), (usePool p316), (joinPools p21 p293), (usePool p317), (usePool p318), (usePool p319), (usePool p320), (usePool p321), (usePool p322), (usePool p323), (usePool p324), (usePool p325), (usePool p326), (usePool p327), (usePool p328), (usePool p329), (usePool p330), (usePool p331), (usePool p332), (usePool p333), (usePool p334), (usePool p335), (usePool p336), (usePool p337), (usePool p338), (usePool p339), (usePool p340), (usePool p341), (usePool p342), (usePool p343), (usePool p344), (usePool p345), (usePool p346), (usePool p347), (usePool p348), (usePool p349), (usePool p350), (usePool p351), (usePool p271), (usePool p352), (usePool p353), (usePool p354), (usePool p355), (usePool p356), (usePool p357), (usePool p358), (usePool p359), (usePool p360), (usePool p361), (usePool p362), (usePool p363), (usePool p364), (usePool p365), (usePool p366), (usePool p367), (usePool p368), (usePool p369), (usePool p370), (usePool p371), (usePool p372), (usePool p373), (usePool p374), (usePool p375), (usePool p376), (usePool p377), (usePool p378), (usePool p379), (usePool p380), (usePool p381), (usePool p382), (usePool p383), (usePool p384), (usePool p385), (usePool p386), (usePool p387), (usePool p388), (usePool p389), (usePool p390), (usePool p391), (usePool p392), (usePool p393), (usePool p394), (usePool p395), (usePool p396), (usePool p397), (usePool p398), (usePool p399), (usePool p400), (usePool p401), (usePool p402)], #[⟨a0,a0ok⟩, ⟨a1,a1ok⟩, ⟨a2,a2ok⟩], 7, countAt, rowAt, indexAt, candidatesAt⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h5_0 : Span (book.check 5) 0 5 := scan_ok (by decide +kernel)
theorem done5 : Span (book.check 5) 0 5 := h5_0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h6_0 : Span (book.check 6) 0 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h6_8 : Span (book.check 6) 8 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h6_16 : Span (book.check 6) 16 7 := scan_ok (by decide +kernel)
theorem done6 : Span (book.check 6) 0 23 := (adjacent (adjacent h6_0 h6_8) h6_16)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_0 : Span (book.check 7) 0 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_8 : Span (book.check 7) 8 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_16 : Span (book.check 7) 16 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_24 : Span (book.check 7) 24 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_32 : Span (book.check 7) 32 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_40 : Span (book.check 7) 40 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_48 : Span (book.check 7) 48 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_56 : Span (book.check 7) 56 7 := scan_ok (by decide +kernel)
theorem done7 : Span (book.check 7) 0 63 := (adjacent (adjacent (adjacent h7_0 h7_8) (adjacent h7_16 h7_24)) (adjacent (adjacent h7_32 h7_40) (adjacent h7_48 h7_56)))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_0 : Span (book.check 8) 0 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_8 : Span (book.check 8) 8 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_16 : Span (book.check 8) 16 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_24 : Span (book.check 8) 24 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_32 : Span (book.check 8) 32 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_40 : Span (book.check 8) 40 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_48 : Span (book.check 8) 48 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_56 : Span (book.check 8) 56 3 := scan_ok (by decide +kernel)
theorem done8 : Span (book.check 8) 0 59 := (adjacent (adjacent (adjacent h8_0 h8_8) (adjacent h8_16 h8_24)) (adjacent (adjacent h8_32 h8_40) (adjacent h8_48 h8_56)))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h9_0 : Span (book.check 9) 0 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h9_8 : Span (book.check 9) 8 5 := scan_ok (by decide +kernel)
theorem done9 : Span (book.check 9) 0 13 := (adjacent h9_0 h9_8)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h10_0 : Span (book.check 10) 0 1 := scan_ok (by decide +kernel)
theorem done10 : Span (book.check 10) 0 1 := h10_0
theorem allRows : ∀ k ≤ 10, ∀ i < book.count k, book.check k i = true := by
  intro k hk i hi
  have casesK : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 := by omega
  rcases casesK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Nat.not_lt_zero _ hi).elim
  · exact (Nat.not_lt_zero _ hi).elim
  · exact (Nat.not_lt_zero _ hi).elim
  · exact (Nat.not_lt_zero _ hi).elim
  · exact (Nat.not_lt_zero _ hi).elim
  · exact done5 i (Nat.zero_le _) hi
  · exact done6 i (Nat.zero_le _) hi
  · exact done7 i (Nat.zero_le _) hi
  · exact done8 i (Nat.zero_le _) hi
  · exact done9 i (Nat.zero_le _) hi
  · exact done10 i (Nat.zero_le _) hi
theorem low : Lower true R T 11 := by
  let c : Closed T 10 := ⟨book.vals 10 0,book.sound properPN 10 allRows 0 (by decide)⟩
  exact fromClosed c (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9), (0xffff0000ffff0000, 6, 22), (0xffffffff00000000, 6, 38)] (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B43

def fullRoots : List Sig := inputs
def fullWord : Sig := 0xfee8eee8eee8eaa8
theorem fullBound : Lower true fullRoots fullWord 11 := by
  intro p bank h hit
  have hlow := B43.low p bank h hit
  omega
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276678376 * 2 ^ 32 + 4008241832)
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
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_40646.Model.Repr at out
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

def mono : List Gate := [⟨.or, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [1, 15]⟩, ⟨.or, [11, 16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 17⟩ (List.ofFn x) = posted x := by decide +kernel

theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40646

open PEqualNP.Outside.L_meta_40646 in
theorem PEqualNP.Outside.L_meta_40646 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678376 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678376 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve fullBound

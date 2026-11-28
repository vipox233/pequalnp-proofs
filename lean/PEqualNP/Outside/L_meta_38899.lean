import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38899.Model
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

end PEqualNP.Outside.L_meta_38899.Model

namespace PEqualNP.Outside.L_meta_38899
open PEqualNP.Outside.L_meta_38899.Model
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

def page0 : List Nat := [0x3b8c8720c042107, 0xe7a10f641c106e4, 0x8600847cd624043, 0x637e291020e818, 0x188617868085f20, 0x5f8a0617e0910ee, 0x87d10021f06008, 0x42085f9a021e862, 0x7c48085e92021ec, 0x42220001c8921c5, 0xf861c1290eeaa8, 0x3fc43f883e18fc1, 0x208906a8e304688, 0x4b211e0c22031a, 0x81e591c21444c2, 0x83f7910ec83a10e, 0x3108685640c421c, 0xc4214836c106c94, 0x1209c82e4818f10, 0xc042906215b35c8, 0x86210c7c5734c83, 0x43943110520e392, 0x55031c838a4a188, 0x8720ac82e4818c7]
def page1 : List Nat := [0x2ca4a18843c4310, 0x86c000801d810, 0xf34c83b08520bd4, 0xbe410cbec8120d, 0x710bc41483e4831, 0x88720bf14ccbd08, 0x2f493109f34c83b, 0xc750c421ee2148, 0x31086f41221dd40, 0xdc31c82fc9031f4, 0x20ec21c82fc9310, 0x9031bf14c8370c5, 0xdc5021df240c774, 0x11c40019bd240c7, 0x5c10000000, 0x84000f3690250, 0x1b0000005404cb0, 0xac001d0070000, 0xbc00000000000, 0x200000800002000, 0xc000050000, 0x991004408106240, 0x66440231200, 0x71649238c308102]
def page2 : List Nat := [0xe36d32c2caa689e, 0x28ca044f2c903c, 0x9213b108a10524a, 0x8321090a1080a01, 0x21f865fc82f1890, 0x10fa41f0c7f997e, 0xe61c4570c7e10ff, 0x60002000080000, 0x890000030001400, 0xf32b2681a40a101, 0x2995c409959a6c4, 0x63eb42e2059acd3, 0x4cbe187c31f842c, 0x83e197d10f821f, 0x487e907d30fa63f, 0x144d05c800081f, 0x50b592368924680, 0x220b1a230b1a23e, 0x106092421903045, 0xad2484360c2203, 0x210d83044360c12, 0x27002b51488360c, 0xa21f483f105c309, 0x1c056ff087d21f]
def page3 : List Nat := [0xe3f91221d908439, 0x3cca32b7414ca4c, 0xc2b49230b514083, 0x4082d45330b5148, 0xe34482dd05209d3, 0x9f3408270d1209, 0x432af24cc2b4933, 0x1c04af248c2d50, 0x133cf40033c15, 0x87d30fc41f8c3e9, 0x7e32f841fcc3e1, 0x7fd32fe65f0cbf9, 0x6b648d248800005, 0x63fe9e9e9e9e9e0, 0x418c69aba88420c, 0x1926a20d9537108, 0x1096010720e1884, 0xe3bbb26222843aa, 0xc0000a01902069, 0x32842a008468064, 0x33f43540429f594, 0x6c94409f55a3284, 0x20cf109351067d3, 0xc9b43d02ec468cb]
def page4 : List Nat := [0x5c83af4310b20af, 0xf66110f21bdc5b3, 0x540219f09950106, 0x29f099500c77631, 0xc745c86f516cd44, 0x8cabf4605632dd8, 0xf268c720afd1b05, 0xf20b74d8420c6e, 0xfa8ca30c82f9601, 0x842c82bf26d0c41, 0x827d6510f20bb4d, 0x32c8310eb10841c, 0x743bdc5a32843ea, 0xb10b45c827f26c5, 0x428c75c324d441e, 0x2f516116329f594, 0x111421bbd1a32c8, 0x41af4d842107753, 0x8cb35c833c42540, 0x2cc73f43c9441f3, 0x7e36c94409f5944, 0x540419f59441c82, 0x2afd1b350873f43, 0x8045086f7161163]
def page5 : List Nat := [0x1033f43944429f5, 0xd6510c219f18935, 0x96319f59443c867, 0xb74d842cc36e32c, 0x8321067c624d441, 0x42dd3610730eb10, 0x2611710fc8c720c, 0x632bd98442cc67f, 0xa58042c83771585, 0x25107b74310531f, 0x2f9600c7209f41b, 0x6944429f4db2584, 0x31fcc5b20c427d0, 0x4db25d06f726105, 0x5cc36c528c9319f, 0xef26107209fc9b1, 0x106319f59431c82, 0x9f59432107b743, 0x5a321067c624d61, 0xcaee6210f209f5, 0xd6510831db10950, 0xc840ed108418c67, 0xbdc5b3510a7d650, 0xa32c836e32c9610]
def page6 : List Nat := [0x36c42c9631fac1, 0x2610631db8cb251, 0x610af119158caf7, 0xd4c7450867e36c9, 0x41cc2ef260c720d, 0x2dd3610a319f594, 0x694443b74d821cc, 0x419f18935d067d0, 0x4db45c867e36c94, 0x51067d36c94419f, 0x7d0694432d78c93, 0x109319f59442cc2, 0x3bd580418c67f56, 0x8414c67f269444, 0xc827d568c720ed1, 0xf46cd720fa41a32, 0x7209f55a32102b, 0x9f59421cc2f9601, 0x8420cbce324d720, 0xc76e32c9630f34d, 0x62115319f41b250, 0x441eb10832d027e, 0xf41a5210f6e32c9, 0x43c86bf16d0c429]
def page7 : List Nat := [0xfe842c8310bb988, 0x34d4219f1895010, 0x40db108524c75c4, 0xd0d35086bd3610b, 0x708140c6216d7, 0x4000000701a430, 0xb0200b54a610017, 0x16655700100c00f, 0xf02320600bf002e, 0xc00100602790c0, 0x1c1c00cb9f00, 0xe50e2e10001e080, 0xc000202, 0x1000000, 0x30000000000200, 0x4000000000, 0x500000, 0x7000000000060, 0x900000000, 0xa0000, 0xd0000000000c, 0x211070000000, 0x90904000, 0xa01020000009810]
def page8 : List Nat := [0xa0106000000, 0x30000019010100, 0x190106000001901, 0x1a110700000, 0x200000211902010, 0xa919203000211a0, 0x900102010008, 0x20200099190203, 0x9a9a0a020009a82, 0x2000a2998a02000, 0x192030018a9a1a0, 0x1a0190200001901, 0x1a01a1a0000, 0x190301211a01903, 0x8000000009b021, 0xc3870e1c3870a14, 0x2850910203870e1, 0x6448901e3c78c18, 0x386cd9b325cb952, 0xf3e78f1e3c78e9d, 0x2142850a04080f9, 0x3a74c992a5488d1, 0x56ad56ad4a950a1, 0xc17af5ebd7af5cb]
def page9 : List Nat := [0xe1bb666cd9b262, 0x7af1e3b76e9cb97, 0x3870e0c080fdf3d, 0x478f1e3468b161c, 0x6cc993254993264, 0x1531e3131429f3a, 0x827610d38996020, 0x164060d41572470, 0x843cd28301a8017, 0x71840ca2001c00, 0x61c72430010de6, 0x911c63840c209b0, 0xc348b1c70c061f0, 0xf192637f45cc430, 0xafe4ba0ffcd421f, 0x319fa2e637e5110, 0x2cc7f843a05fc96, 0xc9440fa20c63fc4, 0xf4414c6fe4b985f, 0x8df11720fb18e21, 0x883fd35106faa01, 0x83985fc9630bf92, 0xf8ae87ff45c83f8, 0x6fe4ba1df11710b]
def page10 : List Nat := [0x32be9ae437d5008, 0x210ff641887fc16, 0x9710fe216617e5, 0x7f25842f88b195f, 0xdfc5632fe21e41, 0xc63fc420c6fa6a1, 0x2b197fd0e32bfa2, 0xf194637c454c7f8, 0x7fe87907f8ca30f, 0x10fe9a885ff2510, 0x3c87fa6b907f0ca, 0x1632bfa2865fc4, 0x7f25cc7fc65087f, 0xdfd1632be9ae83, 0x843ff434c7fe879, 0x6a20ff8c720fb18, 0xe9a8437f450c6fa, 0xbf865a07fc5720f, 0x41bfa2e617d500c, 0x1c83fc6420ffcd4, 0x54021de21083fc4, 0xfc32103dc65907f, 0x7fcd442dfa1883, 0xe21fc43087fe6b9]
def page11 : List Nat := [0x6390dfc9431ffa1, 0x621641f531087ec, 0xbf865887fc5632f, 0x42fea8083fd5110, 0x20cafa6a206fd0c, 0x45632bfa2843ec4, 0xff30c83f461907f, 0x8ff0c841fe21263, 0x621ff438c7ee831, 0x87887f0c740fe21, 0xe9ac21fc21cc3f8, 0x6faa020dfc5730b, 0x20bf28865ff4308, 0x2103fe8b195fd17, 0x54043bf28887fe3, 0xfc458cbfc65a0df, 0x7f85632ff19621, 0x857c45087fc63a, 0x87a07f0cb41bea8, 0xe18e41fe5110b7e, 0xbf88518df4d420f, 0x40fe82c65fd5010, 0x5c86f8a498ff8cb, 0x10b40bf8ae417f4]
def page12 : List Nat := [0x386fa6a216f, 0x387c000600285e2, 0xc001d0000000cb1, 0x60220c00000026, 0x686000550000000, 0x9166d6880162fd5, 0xc000017a020003, 0x100000007c80800, 0x1ca970000000000, 0x20800000000000, 0xcabc08000000000, 0x308006a510, 0x4b00000004d6b80, 0x408c00370000000, 0xf2001e801e6770, 0xb50000000470000, 0x8000e4e80826, 0x4004382bb452020, 0x4f0409, 0x221400d90000000, 0x80000000010000, 0x20000000, 0x1000000006, 0x60000000280]
def page13 : List Nat := [0x200000000e000, 0xa0000000480000, 0x16000000, 0x680000003, 0x1e0000000e0, 0x408080000004000, 0x202000101000000, 0x200004240c00020, 0x181000000848, 0x6240800030204, 0x191030000c48180, 0x40800040202000, 0x10001048100008, 0xc00042208000211, 0x10c8100008441, 0x110206000881010, 0x808080024040000, 0x20c000901030004, 0x100024241000120, 0x981030004c08, 0x26240c00131204, 0xa01000004c88180, 0x40800140202000, 0x20005008300028]
def page14 : List Nat := [0x800141208000a09, 0x8408080028640, 0x220200001081020, 0x848180044040400, 0x200001109040008, 0x100046040800230, 0x1189030008c48, 0x48040000232206, 0x201020009008080, 0x241000241204001, 0x100090c8100048, 0xc00310204001881, 0xc808000062040, 0x320206001901010, 0x848180064041800, 0x20000190904000c, 0x100066040800330, 0x198903000cc48, 0x68040400340200, 0xa0106000d008100, 0x64080034220e001, 0x1108c810080068, 0x535020406901902, 0xd41010126a04280]
def page15 : List Nat := [0x424029a820a014, 0x50126a64280d35, 0x402a8018a034d4d, 0x2a008680150041, 0x288212009440c90, 0xa46480e51043401, 0x10201c54d0d0162, 0x480f20232401900, 0xc940c501e4046, 0x400a01001a01902, 0x20420f82c090160, 0x20781d06a168501, 0x8bc2c8aa270942, 0x20fe3d8ea378d03, 0x39444c926481104, 0x31886117a5a95c5, 0xd9b2691a0671926, 0x61d2739c8701bc6, 0x19fe7e9ea791dc7, 0xf2368ba2886a0e8, 0xba5e95a50932408, 0x7296a3a8a9f2769, 0x62d0b2abaacaa8a, 0x12fabc2ecba2e4b]
def page16 : List Nat := [0xc328c7314c430ac, 0x6354d3346d0b38c, 0x1b82dcb68d8b5cd, 0xbb4ea3a2e7390e, 0xb3def5bd2f3bc6f, 0x841902c04ffbfaf, 0x44490fc3b0cc2d0, 0x4563084771945d1, 0x8b0e34794562c30, 0x6071b9a18708ddc, 0x92926e301897a40, 0xf8583181870c572, 0x1ce4a4b2c6c41a, 0x5834937182c403a, 0x7020060b1afa907, 0x2c41c6cbaac058, 0x3cd3a3290616206, 0xc0bc1c349371024, 0x64405963018d161, 0x8345c6442406908, 0x14182900e080c81, 0xd1820383023528b, 0xbf26141381981e8, 0xf8b0c1d0cb951c6]
def page17 : List Nat := [0x468b06310137021, 0xfc304b030607060, 0xd292861c81a0502, 0x172aa0c100c1076, 0x108ad10c01a0218, 0x3181ee16763018, 0xfa8562880c1e2c3, 0x1c2856b82825831, 0x325ca361410c20f, 0xa0a54a6b1418c3a, 0xa4c6100e083250, 0xd1e301871a08329, 0xaf16182a17e3308, 0x58f141822c2032b, 0x887052868b7419, 0x307de2cec10108b, 0x82010da2ac4950e, 0x2030583001d48e1, 0xb0e0c10c18b058c, 0xcdd2698c100a58, 0x2820e9c4240c747, 0x870c946f56bd930, 0x1c15a9481a0c0e1, 0x630606062c3cb1a]
def page18 : List Nat := [0x10304ed0e6230d0, 0xda21c6ce7a34937, 0xd109665a0980873, 0x88c074c5c318345, 0x2eaa1a781a0b031, 0xa1f980c30782348, 0x4212974af250e1a, 0x62c383043034a0, 0xd16299ac1e34606, 0x8b0e3458e183018, 0x603042c6820c386, 0x318b101c1014634, 0x2c665001de8f184, 0x432b8a7f0600b0f, 0x1d9c1007c1c5830, 0x1e332081608007, 0xb0cf630d7ed051, 0xe87080060b1c346, 0x980b0e040084c50, 0x1d943195870c1e1, 0x6a46c6933c58804, 0x18305870c08f8cb, 0xd1c3098704e2103, 0x879a306bd180d58]
def page19 : List Nat := [0xa8c1cd4607062c6, 0x5060a100b45b5a, 0xfc43fc41fc40be8, 0xe31ff30ff20fe10, 0x10fd31fc20ff31f, 0x2ff21fc42ff43ff, 0xfc31fc32fe30fe3, 0xa2ff40ff41fc21, 0x100000556005a6, 0x140000800003000, 0x7000030000, 0x58000280001, 0x380001a0000c, 0x20200010000078, 0x902084808404041, 0x818644003120618, 0x440204201010c8, 0x221100104810824, 0x10c810864004220, 0x6240d3120498100, 0x120518102840812, 0x1038c88046240e3, 0x8062040f1020519, 0xf2020790101c80]
def page20 : List Nat := [0x798902cc0816424, 0xd048168040b3120, 0x100343205a1900, 0xdcc8b4907c58483, 0x1998561513104f0, 0x5c22e09f5e5c9b, 0x21980cc1992422c, 0x12c084531c15d30, 0xc2c6a4c006a87ac, 0xe0091a48cb0c0b4, 0x4c2ef0ae18b3d, 0xa272c381f18b40, 0x3185008ccc38218, 0xb68614a301096c8, 0x51101a6046b012d, 0x118088630b0c094, 0x325348b18501454, 0x108b44318204d2c, 0xd0727c60302cc1b, 0x83904faad21c409, 0x6d8829286177930, 0xa1e41779348790, 0x837cb0065885f6c, 0x1964b20eda6592c]
def page21 : List Nat := [0x7905de4c18e41b7, 0xfaad19621773108, 0x208613eb2883104, 0x13fab084984faca, 0x2885984faca20e6, 0x21cfacb194833eb, 0xaad20c613e834a4, 0xa613fab484984f, 0x9fa9882a05ba6c2, 0x46420ed86592e21, 0x1ede65928833eab, 0xcaa1c413eb064ba, 0x833e1320b20cfe, 0xeb2865a04faca19, 0x6520ed865928833, 0xcf8caa1e413fb2a, 0x21c413e132a018, 0x613f936a0a1df2c, 0xab483905f2c0212, 0x2a04faad20c413f, 0xd8c4a1c419e2908, 0x21e419ea1e4a20d, 0x33e1320b21decc2, 0xa4a1cfac192c6]
def page22 : List Nat := [0x984fcca21e413eb, 0x8c2a1e41b6210a4, 0x92817b30887105e, 0x3eab4631067e862, 0x28620cfac192c83, 0x5ba6c20e615e31, 0xca18c41afa9c64a, 0xa613eb2843984fa, 0xea1aa020cfeac20, 0xa020dde4d20c419, 0xd7a6c20a813e132, 0xd18e415e8348420, 0x419ea1aa0214fea, 0xab464a04fcca18e, 0x2984f84c82c633f, 0xfaca21c413fab04, 0x196213fb2a6420c, 0x39fa1a0b214faca, 0x2883184faad9908, 0x994fa0d928633eb, 0x84c82e877a30a86, 0x80876e9b085984f, 0x7a30a87194f8c4a, 0x26a20dba6d21261]
def page23 : List Nat := [0x857ec0a18839f21, 0xc192c87ae1926b8, 0xe41af1926a20cfa, 0xeab465a04fcca20, 0x4ba04fead21e413, 0x6bc649ae219ea1e, 0xd18c416e9b08498, 0x616e9b042985de4, 0x8364a20de8c2a1c, 0x7106ba649ac833e, 0xbc649ae817a30a8, 0xa1a61ae1926a20e, 0x15e9b48420de8c2, 0x926ba05ba6d20c6, 0x984fead20a61ae1, 0x1e0000016e9b043, 0x17a9e0000000032, 0x13a000000000, 0x2000000d64a0400, 0x401660000009, 0x400000000, 0xfe000000b6000, 0x136000086000000, 0x5e0000000000080]
def page24 : List Nat := [0x11ae600000001, 0xba6e000000000, 0x12a0000000056, 0x261a00ea7e000, 0x40000620000, 0xee00005ebe00000, 0x7a01a34e0000, 0x4e0600000, 0xe00000005560000, 0x9b06017600e2c, 0x72de003600, 0x1316f6000000000, 0xca0000008247, 0x620016426a00000, 0xe00018a000a01, 0x4600ab0ec200000, 0x600000000000023, 0x126017e5a0001a, 0xa6096e, 0x6b8f834a0000000, 0x4000000001201, 0x300000001000000, 0x80000000, 0x3000000014]
def page25 : List Nat := [0x120000000700, 0x5800000028000, 0x140000000d00000, 0x800264414000312, 0xa010800050083, 0x44040c002202040, 0x110700090883000, 0x804511304060012, 0x14d4909008a4280, 0x45332402a281820, 0x1020006a6280805, 0x870e18284080c10, 0x68d1a2848910203, 0xb94284c8901e38, 0x78e9a3464c99306, 0x499121428101e3c, 0x66c972e5ab55aa5, 0x86ed9b3568d1a33, 0xbf7efde3c78e5cb, 0x2c5890a0c180fdf, 0xa74d99325ca9326, 0x5aa53a74a8ce9d3, 0xb76e5bb76ed58af, 0xee001c20002f5eb]
def page26 : List Nat := [0xd3845931c2009, 0x2af19c20010f040, 0x1423882050c4002, 0x9c04040141c407d, 0x18a06251501681c, 0xd053803301c6100, 0xac9628806280902, 0xf842985f4164108, 0x1bf92e217715ccb, 0xc837e87217fcc84, 0x4930fea1e41fc41, 0xf43c83f865a05f1, 0x7fd0e20fea1c61f, 0x41fd328c6fa0b19, 0x5a07f50e20ff21e, 0x21e417d5010bfc6, 0xf883987fd0e30fe, 0xbea80657d05d0f, 0x90afe4b20ff4c31, 0xca41bfa9a817d05, 0xe32c82faa021ff4, 0x5f4d640be9a843e, 0x617f2590efa6ba0, 0xa20dfc9743ffa1a]
def page27 : List Nat := [0x9a8817d058c6fa6, 0x7c8420cfd1430be, 0xbf29087fd434cb, 0x50ffa80985f4d71, 0xe32be9ae857f50, 0xe31c83fc83107f5, 0x7f8c821be9a821f, 0x617f5350aee2a18, 0x620ff8c841ff18a, 0xa2861745150f7a8, 0xfe61887fd01309e, 0xbea80433d45ccb, 0x8c37a86217f1093, 0x4943fea1a61fe31, 0xf258c7f883185f1, 0x5f4d641fe20a617, 0x81bc41502fa6b10, 0x3905d14542ff192, 0x92e81ff438cbf86, 0xfa6a217f90720bf, 0x1bf92863fe418c2, 0x106fa6b217f8ca4, 0xa32ff18c41fd32, 0xe43882da4a187f1]
def page28 : List Nat := [0xcfd1732be9ac43f, 0x61fc42cc2eca221, 0x4a07f0c821fe10e, 0x196217d50106f8a, 0xf884197f8c930ff, 0x1fe21c417d500c7, 0x902fa0b21dfc944, 0x620dea1e817715, 0xe328c7fc84987f1, 0x7fd0d32dfa1a81f, 0x61ff40cc2fe4b98, 0x2987f0c841fe208, 0x21465fc32c43fc8, 0x1140b7f0c620ff, 0x4f68000005f8301, 0x57c68d09100502e, 0x21f868e0384, 0x90000308712788, 0xe80178000248001, 0xe810d8a0faa855, 0x88200090c45a880, 0x50e67a2ea4, 0x4000000010000, 0x200000000c00000]
def page29 : List Nat := [0x50000000, 0x1c0000000c, 0x90000000400, 0x2c00000014000, 0xd0000000600000, 0x80000001c000000, 0x408180002040, 0x30200000101010, 0xc88280006440400, 0x200000201020000, 0x200008240800041, 0x209090001048, 0x8441000042202, 0x881000001088300, 0x40400110204000, 0x4848200024, 0xc00130202000981, 0x4c88080026040, 0x140202000a01000, 0x8380028040800, 0x208000a01080005, 0x380028640400142, 0x10810200050c8, 0x44040800220202]
def page30 : List Nat := [0x181000008808200, 0x440400230202001, 0x60008c88280046, 0x800240204001191, 0x9048200048240, 0x242208001211010, 0x88380048441800, 0x204001881000009, 0x80062040c00310, 0x190104000c808, 0x66040000321208, 0x98103000cc08080, 0x40000330210001, 0x2000d008080068, 0x340210001a01, 0xd0c8380068441, 0x130402288a1a000, 0xd000a428080452, 0x402928182011485, 0xa6a48480535040, 0xa8021a004d4d090, 0x408680251043400, 0x20a00c940c5004a, 0x280325231401928]
def page31 : List Nat := [0x1c9490d0064a48, 0x75014340192921a, 0x500c006a628080, 0x138460f02e0901a, 0x210741c0641805a, 0x2b8a8280982408c, 0x3a0da348c6300b6, 0x4a11e4690e418fa, 0x58954539464e930, 0x679926197a5d16c, 0x749cc709ba6b9a8, 0x7e1f07a1e2771d8, 0x89a1e8621282a00, 0x98a58942468ea2c, 0xa8294a22809e26e, 0xb52c6afabaad2ac, 0xc1afabd2ecb92da, 0xcbb2ac9b1cc5b10, 0xd7350d2342cf334, 0xe3b88df374dbb66, 0xf1bbeed3aae939a, 0x23fcfdbe4f6bcc, 0x6c2d0a42306415, 0x241010f20589040]
def page32 : List Nat := [0xe444841a3048718, 0x122058a16280880, 0xb202c08c0ef263b, 0x870a1270c470060, 0x486043850b14245, 0xc0c304385321628, 0x203844884587080, 0x21052e142c40918, 0x800c609043460b1, 0xb14044871628302, 0x87060470c003470, 0x4840034f077d104, 0x4382031c5db342c, 0x1c25f043a525762, 0x200189142458862, 0x620820d8232a870, 0x10808687022c612, 0x36b81c05d162493, 0x58a0e0068e16283, 0xc18005104060809, 0xf0509181e90a182, 0x424404766843916, 0xae1c0800a2520b1, 0xb160e492621010d]
def page33 : List Nat := [0xd41432f07020010, 0x50b10cc58a112c3, 0x3c2263460c021c, 0xb5907022c6090e3, 0x62d609021cc0f0e, 0x123268b32345095, 0xc121c144131538b, 0x890608e9f0e2c48, 0x58d431c58904285, 0x8a870c0991c1214, 0x1c080082d10b141, 0x1068b1418087a0, 0x434709021cbda0, 0xb141c0880c20304, 0x8416a64064c2d40, 0x42a0e3058718284, 0xc1890a1128d1628, 0x498820835f8c171, 0x1600091a2848616, 0x621c15308384077, 0xa022038b1420087, 0x86a2384880c24a3, 0x507122848c1a304, 0x981121c58a1358]
def page34 : List Nat := [0x2c3849e386090e1, 0x210087120802614, 0x442048468c17a11, 0xa5c24307160c009, 0x801626c890801c8, 0x4831634587181c0, 0x410b16283010f28, 0x2430b14803b3142, 0x22c50910114a898, 0x6b0e30b0e140a11, 0x616281010e24123, 0x876e2c508022439, 0x30b0a6dec302243, 0x1fe81fc61fa841c, 0xfc43fe41f865fa6, 0xa81fc81fe65fc63, 0x87fa65f863f881f, 0x7f885f843fe85fe, 0xf861fa87f887fc8, 0x821fc85fc41fc65, 0x21fe61f883fc83f, 0x8ca8c00e881fe, 0xc55e10850, 0xc0000400001]
def page35 : List Nat := [0xe00006000020, 0xa000048000200, 0x68000300001600, 0x302020000e000, 0x209000c8808624, 0x4c080a604004320, 0x844054020299101, 0x202a190150c802, 0x1018c4804604062, 0x80c824024020319, 0x64320321900908, 0x199101cc080e404, 0x60443418034320, 0x1d10f8e0c0a89c8, 0x5ad918171654d31, 0x8a6a5e462a09e5c, 0x805730a2ed6c6a6, 0x82cc2891826c82c, 0xb20a2462142c228, 0x30a32ca24610d40, 0xc04830830b28818, 0xd2891819482c715, 0x630b28805e30a2c, 0x714f20c20c2c835]
def page36 : List Nat := [0x620c2891845482c, 0x804b30830b28716, 0x586230a20a20b30, 0x930a1c505220c1c, 0x100e20b1c505821, 0x918874b10d28918, 0xa28920668715328, 0xd30830b20d80c2c, 0x10491881c505f28, 0x91823642c820715, 0x8a60c5f2012cc28, 0x8432d03a3388a59, 0x8eb086a9043f755, 0x71dc53294432a38, 0xcba33886b90a41, 0xe42905c7714c951, 0x93254432e8ae21a, 0x623ac229261a311, 0x43c57584325029, 0x443296a2e1b64ba, 0x6592e814e41e465, 0x35c9841482d4b80, 0xc98a59b0829864c, 0x834e9d432d0110]
def page37 : List Nat := [0xb40442a7baa6419, 0x4b2865a0db1710c, 0x65c032cd740c9a6, 0xc2ccb806598e816, 0x43a07457114b314, 0x58dc600b52e0196, 0x60000000070a92, 0x981a0205901a02, 0x349249124924924, 0x19f584524c1a4b2, 0x9741882ed600cb2, 0x82ee6210d209f5, 0xd6510620d710535, 0x94419f594418c27, 0xdd119150827d06c, 0x9150c3744145420, 0x2f5610cb41dd11, 0x36c8540ae58032d, 0x420bbc9b31486bc, 0x78d441483774145, 0x214c39c32cd740d, 0x27d650cb41b7cd8, 0x1cd721be5803244, 0x419fd58424c35d3]
def page38 : List Nat := [0xcd8414c36f32c94, 0x1d02bc4654432b7, 0xb9600cb40e70cb3, 0x149309f55b32107, 0x9fd5b414836f46, 0x8335d06bd650cb4, 0x4835e610d5209f5, 0xd650cb40d7d1835, 0x9431d714b314c27, 0xcf119510ca7d06c, 0xb314c27d650cb10, 0x836f5210530d314, 0x35d0520bbc98314, 0x740afc9b31d035c, 0xf919510cbac32c8, 0x150c2bf260c540c, 0x7774645420dd105, 0x510520d7d58324c, 0x40dbd05250c35c3, 0x55b32c86bf26cc5, 0x1483774645430bb, 0x7d650c841bbc984, 0x4c521e70cb31502, 0xdb584524c3cc32]
def page39 : List Nat := [0x8032cc74c35c852, 0x4c27d0694843b75, 0xd65104209fd5b41, 0xc841bbc9b314827, 0xf30cb31486f5610, 0x8214c35f41cd420, 0xc6f5610c9109fd5, 0x6cd4219f58325c, 0x741dbd58324867d, 0xf195314876d32c9, 0x214c36f41c94309, 0xabc36c8740be580, 0x14d420f34cb450c, 0x209f55a321075f4, 0xd05150c27f56cc5, 0x2d075c354c521dd, 0xf5610cb109fd953, 0x10520db14b414c2, 0x19f55a32d067f56, 0x8325d07cd320cb4, 0x5035f56cc5309f5, 0xd32cd741afcdb21, 0x4930db0d7214835, 0xf34c9510cb6e611]
def page40 : List Nat := [0xb418c27d56d0430, 0x83cd320c841b7cd, 0x624c521d7107350, 0x4209fd5831482ec, 0xfcd8215027d56d0, 0x250c3cc324c721a, 0x67f5610530db105, 0x6109309fd953210, 0x10af0db25d02df3, 0x55a32cc7b832d01, 0x34827d56ccb41b7, 0x5d610d5209f9944, 0xc910afc9b35d03, 0x2f30cb31c867e65, 0x5b21482cf614c83, 0x482f9600c520dbd, 0xd610cb409f58435, 0xd442bbc9b41882b, 0x9f594410c27d06c, 0xb25d02bf36c8740, 0x27d65d0630eb0c, 0x60cd721af584325, 0xb40d78cb351067d, 0xbd4b414c2f9600c]
def page41 : List Nat := [0x25d03ac32c8540d, 0x35e35d0520afcdb, 0x6c8530db107250c, 0x41f34ca510cadf3, 0x148414c27d06cd4, 0x227f56c8530db, 0x40020023c430000, 0x1c8b8203c180538, 0xa1da9424, 0x400000202926950, 0x20634c240086a4, 0x10f4e2000003000, 0x834020b0000c260, 0xab0000000060004, 0x42b58a00818000c, 0xa160e020000c020, 0x7804060c80, 0x10000000020000, 0x6000000, 0xa00000002, 0xe0000000300, 0x12000000040000, 0x600000005000000, 0x600000001]
def page42 : List Nat := [0x700000001a0, 0x8300011020a000, 0x280012020c00044, 0x14020a0004c08, 0x220202000500830, 0x22060008c080800, 0x2000cc88180023, 0xd00820003402, 0xd008300034020a, 0xc10003512040000, 0x1150204001484, 0x12034040c4540c1, 0x51204004c80c900, 0x21400c94cc50023, 0x400d484c1003353, 0x15440c100551020, 0x12100e0e0c0a060, 0xe1c1c1412121212, 0x302e28282622221, 0x838383432323232, 0x4a484646423c383, 0x858585656524e4c, 0x6462605c5c5c5a5, 0x672706e6e6a6868]
def page43 : List Nat := [0x8c8a888886827e7, 0xc9a98969290908e, 0xaeaaa8a4a2a29e9, 0x4b4b4b4b4b4b0ae, 0xc0bebcbcbcb6b4b, 0x4d2d2d2d0ceccc4, 0xdcdadadadad6d6d, 0x6f6f6eeececeae2, 0xd0b0700fefefaf, 0xb1b19171511110f, 0x23212121211f1f1, 0x228e0112b292727, 0x8c8071a00001802, 0xd29c21a5b639e44, 0x429628218109adc, 0x861470e000ba411, 0xb0a89828a7aa3b, 0x46bc91630a2263a, 0x243028063eba431, 0x4c8620e0162b0b9, 0x660c096812ba45c, 0xa3d111650a50c89, 0xc6b418058a24eb8, 0xa23a8982c6334c9]
def page44 : List Nat := [0x386c8e01221468, 0x6a1a030000e0f03, 0x83fa6290b031429, 0x731fea80657d158, 0x25d077a80887fc9, 0x78cb31dda04217f, 0x16d258c6fe6a10f, 0x18fbc8720be1ae4, 0xae436c524c2de4b, 0xe2a107f0cb10be1, 0xae9a821ff32d06e, 0x43fe8a197f10420, 0x430be82e637f25c, 0x45103fe43985b49, 0xf0c5409fa2c213f, 0x17f25cc6f84a886, 0xa06ed0110de1968, 0x28217f3510b7864, 0xaa2197f10720b79, 0xbf928837f514c2f, 0x3f883985fcd742, 0x520de10a81bf31d, 0x524c6f86a887bc8, 0xfd0720fe990837c]
def page45 : List Nat := [0x175150c2fe4a10f, 0x10ff4d721ffa086, 0x90657d50106be6b, 0xc6420df45630e69, 0xbb8a861bf35d03f, 0xc6f86a905fd4532, 0x530ffa0e617f250, 0x5010efa2a107fc8, 0xfcd721bea80657d, 0x1ef32c87f843985, 0x98dfc9743be8a86, 0x9261fe510ca788a, 0x86598d74d621be2, 0xffa0841fc410c3b, 0xcbfc65a0cf11521, 0x620fe21e417f258, 0x31c86fa0ba0cfd1, 0xfcd621df90e81ff, 0x35c35482ea2a105, 0x18ff0cb41fe9968, 0x28617f350c6faa0, 0xe4ba04fd14209fa, 0xfe196817f258c77, 0x43fe6290ffd0520]
def page46 : List Nat := [0x530bf9a883bd40c, 0x40443f883107f10, 0xfcd741b692821bf, 0x1df314c3f864885, 0x187f4c7219fa282, 0xc61ff35c86de4a, 0x882905f41721fe2, 0xaf9a8415f35043f, 0x42ba6a10578d520, 0x740fe18e417f35c, 0x43482fea2905fcd, 0xf54021ffa0c41fc, 0x1fc32106fca421d, 0x90cfd1630ffa0c6, 0x9261fd510caf86a, 0xa2b995f45632b7a, 0xbea8085fc214c2f, 0x3fe629077cc730, 0x731fe216617f25d, 0x31503fe82987f49, 0xfc8540ff98a21bf, 0x3ec32c87fe6420e, 0x88770c931fe82e6, 0x9243fc424c3fe42]
def page47 : List Nat := [0xa0b90ff0c520f61, 0x1080073ff31c83f, 0xae4e0001001ca00, 0x62894c14001f9, 0x3a8000000003c40, 0x13c0000, 0x2007b81800b1000, 0x4586c1033010022, 0x15b340002, 0x2b505030ae00388, 0x22b7c0000998095, 0x48d858780103, 0xee9010000017000, 0xcfb000017, 0x80002968102705, 0x1f400009b8, 0x8ea140000030000, 0xd40000000080000, 0xd0000004005eb, 0x64800c200000000, 0x19e00000300000, 0x7252e80166b9000, 0x416c00d7064bd3, 0xbc0800918000091]
def page48 : List Nat := [0x131020009a00003, 0x1000000000180, 0x100000000600000, 0x28000000, 0xe00000006, 0x48000000200, 0x160000000a000, 0x68000000300000, 0xe0000000e000000, 0x424000000001, 0x191000000c4800, 0x204180011020000, 0x900000480830002, 0x140012120e00090, 0x4c4800002604, 0x13220000098907, 0x500820002804040, 0x20c000a0105000, 0x800004404040014, 0x118101000884, 0x4644000023120, 0x188105000c40800, 0x404180031020c00, 0x907000c84800006]
def page49 : List Nat := [0x33020a00190, 0xcc4838006624, 0x34020200199100, 0xd00828006804100, 0x400001a0106000, 0xa42608003512, 0x8a818200454081, 0x2a6648011523240, 0x192004940c1002, 0x408013502040099, 0xa00c940c10046a2, 0x33502040192998, 0xd444810066a6428, 0x2130401a8898200, 0x403c0c024050035, 0x10a4260841c0681, 0x9114400e8360d03, 0x116c5514c4f1304, 0xb1d4711b86a1986, 0x82548f22c872087, 0x62c8b02a4a42709, 0xe32cc7304bd2e4b, 0x4388df368d6344c, 0xd3e4f63ccef3ace]
def page50 : List Nat := [0x64490f43107404f, 0x54bd2a4a1214691, 0xb519434f5394dd3, 0x157d595595453d4, 0x75d1725bd6b5916, 0xf62d866097e5ed7, 0x56819e6619664d8, 0xc6e5b66cdb06a5a, 0x8751cf731c8709b, 0xe7a9e7791de76dd, 0x880dfe7f1f67c5e, 0x287e1884a0e82e0, 0xd8de328be298962, 0x29424b922459063, 0x79926096e579565, 0x29f67a9d6709b26, 0x1420ea3a8aa1a8, 0x282860600106953, 0xe5c6c692181420b, 0xd1c3078b0a0850, 0xd02142c72c160c2, 0x818100286050630, 0x3470d4e2860d161, 0x61810100284b314]
def page51 : List Nat := [0x140c68b1a286031, 0x61418c0c145a5, 0x50028606221810, 0x10a0c100801a2c3, 0x68c1629c141610, 0x34e0d0c3170d0c3, 0x42c305002861d20, 0x1a3058604f42831, 0x1183462e1c45786, 0x1a5a0850b1c7069, 0x20a00305061a0c6, 0x208d0a2c1010c88, 0x1828206a050a0c1, 0xa3800d161870c16, 0x65061e1e30e301, 0xa1a28304002c6a9, 0xc14182000c1900, 0xa93163058550286, 0x58414141801619, 0x2c505080c3121c3, 0xa180051825c8a18, 0x160c6301a380060, 0x3002c6860014626, 0x86340858a1c1820]
def page52 : List Nat := [0x334183460a0a345, 0xc0801a305041c34, 0x1813f080c58a0c0, 0x8a45030a3068b14, 0x1a386931619a881, 0x3002860b0a1050e, 0x841a2c283181828, 0xa0c1810006b01, 0x8606082870c080c, 0x1068c142c283222, 0x82c50508043240c, 0x1c3188c1c202870, 0x5082590b18d060d, 0x41c34503001830, 0x586182822b16345, 0x588c1cc05061ac4, 0x1058514446061c3, 0x830e2b1c202840c, 0x141820206ac58d4, 0xd1c301000c00305, 0xa080858e080c68, 0xb8d160c08d14308, 0x8287081818c580c, 0x1420a789c58c503]
def page53 : List Nat := [0x61828100301000c, 0x143468318003041, 0x7141413b0a31f2a, 0xa14182001635d1, 0x2c0182820b1c346, 0x608145841618, 0x8c10b14385851c3, 0xa2c305080050334, 0x442c6060a300060, 0x518445850610506, 0x8b1818236143610, 0x60404282981019b, 0x4584542c68b0a38, 0x2c68b161450e183, 0x274e2b1a1828a0a, 0x3c7140c1c202824, 0xb520c28c1400304, 0x8b086418d4c1410, 0x60414147070808f, 0x828216105052c0c, 0x8458d1829284042, 0x3fc42fd03fc83fc, 0xfd0ff887f8cbf04, 0xd0bf443f4c3f107]
def page54 : List Nat := [0xc7fcc3f487f10ff, 0x3f4c7fd07f843f0, 0xf10bf8c3f4cbf10, 0x8c7fccbf083f483, 0x3f883f0cbf087f, 0x2f503fcc7f0c3fd, 0xe500502b00801a0, 0xed842000480000c, 0x67000000c400048, 0x8000000103e, 0x1400008000030, 0x16000070000300, 0xe0000680003000, 0x404000001e000, 0x110200191000c08, 0x981004848024040, 0x808026440131200, 0x40232201181008, 0x20198100c848064, 0x806030066440331, 0x981592910f8c8a0, 0xb28a624211e9c1a, 0xbcb9b734b1af2da, 0x1cecbc9c6c3413f]
def page55 : List Nat := [0x1c292129f295d35, 0x3485495814b4986, 0x55a4c3b9c8a3014, 0x24a8a41006622d4, 0xa595697a9690987, 0x1d2545045692200, 0xb0814b4910a5986, 0xa4ac809ad452080, 0xb30c162a4c3a152, 0xc4a8c3829253812, 0x45a8c3e20a930c0, 0xa30d0e3a9253a56, 0xd525404acc30548, 0xa4802446d4b30c0, 0x60c460db250413e, 0x840c188c1b04a88, 0xe46c9410b5cdb41, 0x9510b5cdb410432, 0x8fd1b35c434e360, 0x9501065f36c5740, 0xc65c36540419b09, 0x26c57308f119500, 0x730add1b310426f, 0xbc9b15d023f46c5]
def page56 : List Nat := [0x500c6b746cc6109, 0x34c36c94109b099, 0x609510cb1182544, 0x10cb11b250434c3, 0x918254425f36d17, 0x34e36c9410cb, 0x7f15d0005002658, 0x87dd0410dfa0e81, 0xc21dc310c3f6210, 0x82085f41741fba0, 0x7928217f45043e8, 0x27e8a187d10610b, 0x10b612a21f73104, 0x5842f86b885fcd4, 0x41731af9ae837f3, 0x7d15cc2fe0b98df, 0x8df11510be22e21, 0xc217d15102faa01, 0x210857cd440bfa2, 0xf28083bc41103ee, 0x2fe8b885f45740b, 0x10bf82e837f1510, 0x106f86a8857cd4, 0xc5430ae1aa217d5]
def page57 : List Nat := [0xdf31cc2fe6b885f, 0x84fd1731bf8ae61, 0x8217d150c2788a8, 0x63087dcc6109fa2, 0xa188217e500c7e8, 0x800a3800504f, 0xa328006a631206, 0x87526b5660000, 0x100000000, 0xc000000040, 0x9010000c481000, 0x404003302040002, 0xd444100000680, 0x350104002288820, 0x4d050066a080803, 0x30401a2808200cd, 0x86068a662803450, 0x9861861651238c2, 0x2492281e79e79c6, 0x36db6cb0baeb249, 0x4f2c9244f3ceb8e, 0x218e18617dd6d75, 0x3863c4448664e66, 0x21462a676664206]
def page58 : List Nat := [0xa673e640c647064, 0x1fe61f821fc2023, 0xf883f863fa21fe8, 0xe63f881fe83f861, 0xb2c00dc5fe21f, 0x100000600002000, 0xe00006000028000, 0x40800000200000, 0x804003120018100, 0x20088100104800, 0x900cc0806204021, 0xc06824034020198, 0xd5d12c4f34a2060, 0x840811061009d95, 0x3442248e21c0ee7, 0x88cc388aa3b9e10, 0xc4a7590f331d233, 0x413d3e880f84027, 0x46454208f91a354, 0xa20f28c9308823e, 0x750d35c878d434c, 0x454423e4645630c, 0xeb761541438f4da, 0x34c521abc9a5050]
def page59 : List Nat := [0x32e350d32c87954, 0x50d358823d46c16, 0x1486b94688210c7, 0xe12148210f14c93, 0x4d620e650d30883, 0x8f51935c823d46, 0xf524c71d434d72, 0x842d93688110c75, 0xd214d720e650d30, 0x1521ab49a5050f4, 0x8f919158ca3d369, 0x545c831d43d4532, 0x833a4548110cb48, 0x3688210f24ca308, 0x921e550d31842d9, 0x74db05c878d434c, 0x35c833543457209, 0x399434c110c7519, 0x6c1721c750d3508, 0x208f518504c63d4, 0x50d358431d434d5, 0x58823e468d521c7, 0xd1314c210c75193, 0x4c820ce91620443]
def page60 : List Nat := [0xc750f524c38d43, 0xd304823f635162, 0x4cb1d43d4131e65, 0x94688110c750f50, 0x7c750f514c2b, 0x1700180330a1, 0x600165040000000, 0x11c70020004a, 0x100002d109d580, 0x800046586d34430, 0x800000da00a, 0x206000160000408, 0x249249249200143, 0x923492492492492, 0xbffb24924924924, 0xa20843f46108408, 0x5f4d610bf82c65f, 0x41ed21c837a8688, 0xb907b8c921ae9ae, 0x99041f521842fa6, 0xba62985fd4930f6, 0x2fc904217d25843, 0x4837a86905f4563, 0x4131dea1e43ed21]
def page61 : List Nat := [0xd43c837a87105fd, 0xdf8d510ee99461b, 0x217d35882f8a098, 0x4986750d31dea1c, 0x18221ee32883bc6, 0xfc6a904f51720fd, 0x3fa98a43f930482, 0x4c3da40106f9494, 0x5420ee99263de30, 0xa308827a8b105f4, 0xef50d21fd18241f, 0x43bd5050efa0b90, 0x2907b4c921be9ae, 0xa92635d35883de4, 0xfc6a90df45620bf, 0xbe9aa41bd5150e, 0x4cbf261106750d3, 0xc210bfa8a657f50, 0xc50486fea2907e4, 0x5fd4530fa98c217, 0x217d158c33a8699, 0x590df457209f22a, 0x28265bd43083da6, 0xfc4a887e88110be]
def page62 : List Nat := [0xf699441be5050e, 0x486fa0b197e4811, 0xc110dea92877f50, 0x515c827c8a90fe4, 0x5fc1721be92c617, 0xc0400d402fa6a10, 0x380008000000021, 0xc0845b5a49c, 0x828000000000, 0x45c015d344c0994, 0x24d6c0124bcb, 0x40034080000fc00, 0x86c0000012d7, 0x42000a411cc1400, 0x1164cc000054023, 0xc000800ddec022c, 0x1bc00008d1, 0x8000000040000, 0x100000000c00000, 0x14000000, 0x240000002, 0x2c00000028, 0x264400002604000, 0x864040028040800]
def page63 : List Nat := [0x64180028640c002, 0x400004204000028, 0x46240000460, 0xc00480408004644, 0x2a6408000048241, 0xa6408026a440802, 0x5070c1020202026, 0x8891224068d1628, 0x6cd192e58a94264, 0x8911a34484f9e3a, 0x56ad529509d3254, 0x364c98b15cb962c, 0x3e70ddab568cd9b, 0x1c3850203f7cf9f, 0x23c68912244870e, 0x4674e99325ca932, 0x307205c920022a3, 0x44208801310101e, 0x89568ae10008d4a, 0x5e91002022c4240, 0x8201393205c2c6c, 0xa8a101e9104a418, 0x602082c40cc6208, 0x1fc65fa43f841fa]
def page64 : List Nat := [0xfa21fa63fe41fc6, 0xc41fa41fc217a87, 0x241fa65fe43f, 0x5c0051000048, 0xc000040000100, 0xe0000600002000, 0x5800024000, 0x240401102001010, 0x312009810048480, 0x810050c80a64401, 0x880460402202010, 0xa0321201901008c, 0x58a119e304870a0, 0x19c2d14986fdcb3, 0xa08e20b0a410527, 0x20835398870cc41, 0x11c4150ce1708cb, 0x22cc438c5108208, 0xb1d2b08a4438c41, 0x2649f290e178841, 0x1fc83f107490041, 0x42072177fc20fa4, 0x390b10fa2727265, 0x6cc53194aec2146]
def page65 : List Nat := [0x32e910931c86b74, 0xd19058c72c42456, 0x2cc6e726cc531ce, 0x3842416318f5944, 0x497318f594428c7, 0x1ad45b3510b2f45, 0x1a31d032c424d72, 0x10ba4428c721ae4, 0xd607203adc5b35, 0x1662f001a001820, 0xa63987d4c421de2, 0xde21463f531c87b, 0x2fa6a10dbc9731, 0x731fb18e43bf31d, 0x258c67e8b98efd1, 0xf4d442d6216436f, 0x17f35c437c63a06, 0xa05e41631ef98a6, 0x8a63f531c437a63, 0xa2b195f4d721fb9, 0xbe9ae21f5310c6f, 0xc6fa0b18dfcd721, 0x530f792e63bc424, 0x458c7788418f74c]
def page66 : List Nat := [0xf0c740ef98e613f, 0x37d510cb7ca2216, 0x196f54442bea806, 0x2e637f350875885, 0x100006fcd442f69, 0x6014da80002c10a, 0x22000007a00e8, 0x40008dc00000000, 0xc02b00100085e00, 0xb80049, 0x10000000040, 0xc00000004000, 0x400000001c0000, 0x60000000a000000, 0x300000001, 0xe000000068, 0x844080003020000, 0x1020004c0820000, 0x800230200000a0, 0xcc0820006604, 0x5231402001a0104, 0xcc100a4a6628050, 0x400a00882004c4, 0x14206808014013]
def page67 : List Nat := [0x3181a02008c0cc1, 0x4a6628072523140, 0x808100cc0cc500e, 0x2a4478e162c4050, 0x64c992233e70d17, 0xb464c17af5cb13a, 0xc182fdfbc74e1b, 0x7ab0d3365c98d0e, 0x611ccebea16d1a4, 0xfb4df29e2de9419, 0x81050ae805659ac, 0x6919a8340571614, 0x29f48aa32462eac, 0x69aac2b2e369ca7, 0xc87f0c7fcc3f4c7, 0xcbfc43fcc7f087f, 0x6f10bf4c2fd03f0, 0x9320013f8cbf8c, 0x6000020000, 0x70000280001, 0x500002400010, 0x24040001c0000b0, 0x200981024c08086, 0x18c08126240531]
def page68 : List Nat := [0x166040710203189, 0x33120398900cc08, 0xa99e48595943880, 0x1550c412bfce71b, 0xaa18565a148199e, 0x2a10465b14ea3aa, 0x843a0e53aa453b9, 0xca48c31280c7285, 0x119a23447ca7535, 0x1a22e163447e21a, 0x120688b30d5a23f, 0x7cdb42d037051d0, 0xbe6ba15fc9740da, 0x2be22e417d25cc2, 0x482faa0215f4174, 0x1732be92e81fb40, 0xf45886fa4a20df4, 0x6fd0b40bfa2e417, 0x657f25cc2e8a290, 0xa20dfc9431bea80, 0xa28437c45482fe4, 0xe44a05f49431bf, 0x14ae022a000, 0x400001000004]
def page69 : List Nat := [0x400001c0000a0, 0x40c000140000900, 0x4901040c883042, 0x88080420409212, 0x1082834220b2010, 0xa917356b5ad6a42, 0x94c720e1ef77bc5, 0xc0b2a42f405a781, 0x6082208220ce338, 0x1f865fe85fc43fe, 0xf843f885fe41fa4, 0xe81fe65f883f863, 0x3460a80050001f, 0x90822000000, 0x1000004000017, 0x14000080000300, 0x100000700003000, 0xb00005000024000, 0xa40410000180000, 0x3796449100d0882, 0xe6532bdeb5c6da2, 0x32aa54879a294a, 0x29c42ea50434de5, 0xe6af2694ae66087]
def page70 : List Nat := [0x465fdf2e5032a96, 0x85b494304fa7d3f, 0x30ff304032dea49, 0x40548fc30fd30fe, 0x11a21147a508234, 0x241c9f4b2a1f8d1, 0x95d35d02788a987, 0x7e207b887e98018, 0x5807fa1ff187fa0, 0x60000200000, 0x5310c4080800010, 0x8c8fa211023986, 0xa28a85795010786, 0xeba6a215d45440b, 0x40bc282876d5210, 0xc12ed8a4a0d714d, 0xd07f107f9064003, 0x43fc43fd0bf90bf, 0xbf887f8c3f503f8, 0xf90ff8cbf50ff50, 0x103fd0ffd03fcc3, 0xff903fc87f507f, 0x5bf10bfccbf1, 0x4e30020006c2240]
def page71 : List Nat := [0x54002b100004021, 0x88844444402c680, 0x21dd9995111110c, 0x63446163447fe19, 0x120201f4fa7d3f, 0x8ac021fd3f46404, 0x31495087bcc2e23, 0xe8366385c6361c4, 0xd06cca17f30a388, 0xe6c2941fe615715, 0x5803183e4c2a883, 0xb00a50bf9851c47, 0x6010e0fb13aa06e, 0xc01943be61721c9, 0x803185fcc28e23a, 0xa0a543c5951c475, 0x25420ff2cc00e6a, 0x4a05175e75418f3, 0x852c2e29b0e318a, 0x66507f89d5107cd, 0xcca878b2a388e83, 0x9950f2515715d06, 0x5285fcc28e23a0d, 0x107f9660337d50]
def page72 : List Nat := [0x26303c0000, 0xc0007c000000058, 0x640edc0088035ce, 0xa2a057c8468eb00, 0xa829661cb8a631e, 0x90b8062a05bdc02, 0x3f29aec218a5b74, 0xa57e30021e42886, 0xc02956ec00879b0, 0xe19b6855f30021a, 0xeaa2c01963f2c2, 0x7fbc4a8836651f9, 0x415de5023ac018c, 0xd9953f9c4a9ab6, 0x6d90a215be7023a, 0xf1a1e6c2976a218, 0x3faa20f9b0a55ba, 0x4359ad12a264196, 0xc02947fbc486834, 0xc6292811fd0e21a, 0xa93b0a69047ec38, 0x77b94e4b00878fa, 0xa91fed02b864a06, 0xc02947e8466f936]
def page73 : List Nat := [0xe6aa0a51fb0e21a, 0xe218ac886b7410, 0x7c8468eb00a51fb, 0xa14f90caa0a5985, 0xa82972e31e6e292, 0x6e292812fb0039a, 0xe29a0da147fb46, 0x3fac68f9b6211fb, 0x411f8d0b88a6a05, 0xc6a0c7ec366f2a6, 0xe02a6658f8b0b80, 0x90b8062a047fc32, 0x4e21a8d9b0a5b70, 0xa52fb019bea8297, 0xad905bdc02a8b00, 0xf9b0830ff0eaa0, 0xb1a3ac01953e2c2, 0x3e2c2e2b00874fa, 0x654fed1aa0a5985, 0x862947fc3aa8b00, 0xa8836651ff00bb0, 0xb083e6c2947ebc4, 0x7e8466fab6838f8, 0xa71fed1390a6a04]
def page74 : List Nat := [0xc01963eaa20f310, 0xa929e651fef12a2, 0xae2ba0d9953eb46, 0xbebc4a7a30a58fa, 0x832faf129ac0294, 0xa99047e8466e312, 0xa6218a51fb0c39a, 0x119be4da0d9ea44, 0x5fa3c8e836631fa, 0x432feb013a2d21e, 0xa4a847f43886834, 0x8eb0063cb8c6218, 0x501bac020d3e2c2, 0xbec066faa6a35de, 0x878f8b0b866daa4, 0x2d9053fac4e4b00, 0x8e292a11fd0e21a, 0xe4392c021f1fb26, 0x7dc028eb00659da, 0x411f8d0b8864a05, 0xac1947f430e6aa2, 0xa82b0658faa8b80, 0xb0a3a0d9943fc3a, 0x1faa68e31aa14fc]
def page75 : List Nat := [0x851fef121a2d907, 0x64a847ec066fab0, 0xae836651faf1b20, 0x51aa0c6a855fc22, 0x7ebc4862b6434fe, 0xa5adb0439aa8294, 0xd995ae41aa99b0, 0x8e1b2411faf1aa2, 0xe2184c8853fac6, 0x1eaa08eb00a71fb, 0xa1cbea831e64a87, 0xa69047ec38c7a12, 0xa7a30a54f90caa0, 0xa9b3e64a859ea44, 0x5e422ae836658fe, 0x65cdb04318a4a85, 0xc02956e41a8e836, 0xe3934872ff0eaa2, 0xd9bca8904be2c2, 0x7e342e2292811fd, 0xa5c7ec8218a4a84, 0xc021c7fbc686b08, 0xe2312815d904b8a, 0x71a326c294be2c2]
def page76 : List Nat := [0x3fac06eb00835be, 0xa15dd0429a0da15, 0xa99963e398a4a36, 0xae192811fc10b3e, 0x2318c2a04fcc00, 0x5fa3c8e836655eb, 0x651fed19bc42a06, 0x62a047fbc6a8836, 0x8eb0063bb0c6b80, 0x1129ac02953fac0, 0x3e29ece292816f2, 0x654fab1a32c0196, 0xc018e3fabcae836, 0xc6212a197a8e23a, 0x11a3ac029c7ec38, 0x3fb4086292a15f2, 0xa11fd0e21ac2295, 0xa4a853e3466e292, 0xa9996a12fb0e218, 0x8e23a0d98cbfc3a, 0x7bb8ce2b008797a, 0x618f8a6b3c86296, 0xad90e3faa4ec296, 0x86b08a51ff0ea18]
def page77 : List Nat := [0xb0a3a0d9947fbc4, 0x7ebc486132214f8, 0x411fb0e218ad904, 0xc22974e21a8d9b6, 0xe19b6851f90ea1a, 0xf1b2664a853e2c2, 0x6f9c08e836631fa, 0x63abea99b8a5985, 0xc02956f9c08eb00, 0x8eb00635f2119ba, 0xd02be42a065fa3c, 0x7fc3aa8836651fe, 0xa51faf12a2c0194, 0xd9971eaa08eb00, 0xa81b2411f90eaa2, 0xe218a5a847ebc6, 0x6e41a8c9b0a52fb, 0x6597e8f23ac0195, 0xa7a153eac08e836, 0xc6292811ff00bb0, 0xd9bea89072e298, 0x3e844a9ab0651fd, 0xa12feb193ec2a05, 0xc01953f9c6c8292]
def page78 : List Nat := [0xa99b0a55be7023a, 0x712a20d994be43a, 0x3fac08e836655be, 0xa1d3886a326c295, 0x6da153fb468e292, 0xf9b0838f8b0b86, 0x4318a4a863e2c2, 0x7ab88e2b0087cdd, 0x85c78862928da86, 0xad90e3e2c2e19b4, 0xe429a411faf1a18, 0x2b8086886b6aa4, 0x3eaa20f9b0a5be1, 0x618f8c7ab884a86, 0xda153fb46a9a8e, 0x862b6431fd0e29a, 0xcb80862947ec38, 0x3e39ea2a36a11ff, 0x652faf1aa664a86, 0xc01965f23e8cb00, 0x8e8366597a8e23a, 0xa81bac02965ea38, 0x9ea40a621ea38fe, 0xa51ff0cb80a7a15]
def page79 : List Nat := [0xd10e3e29aec218, 0xa6218a55f30021a, 0x7193ec2a059ea40, 0x7fbc664a36a13be, 0x851fed193e62a04, 0xc4a053fac06e836, 0xa2a36a15dd0431e, 0x2c5a2a62f1e21e, 0x8e38478a8000000, 0x1000da570e0d9, 0x820040608018000, 0x57f0633c10c1b0, 0x200001d60402020, 0x3818892821c9a0, 0x3159010016e0600, 0x802000000000000, 0x103c0001404000, 0x83bbae74003608, 0x2458001d4d00048, 0x8c503607001ea1, 0x51670009ab62400, 0x400022fa0807058, 0x20000010000240, 0x300000000000]
def page80 : List Nat := [0xa0000000, 0x1c000, 0x900000000004, 0x140000000, 0x800000000030000, 0xf00000000006, 0x220000000, 0x48000, 0x1a0000000000b, 0x3a0000000, 0x94000, 0x10300000000014, 0x202120000001, 0x4044c000, 0x911100000010c85, 0x522280000002, 0xa6464000, 0x810900000014c90, 0x1312140000008, 0x800000286454000, 0x11200000084084, 0x2422060000012, 0x8000004a6410000, 0x910a000000c8084]
def page81 : List Nat := [0x361104300000019, 0x80008c260814000, 0xa1b0001505510d, 0x631404040002b0a, 0xc628080c000, 0x1a0300018c54106, 0x320324060009312, 0x264064820001, 0x2090004c80c905, 0x362544180009919, 0x26c684828001, 0x9a180004d8d5106, 0x46253418000a302, 0x80028c6a0860001, 0x821d0009088c901, 0x5613042c0012309, 0x8004c40a6858002, 0x209000c98d510d, 0x360524000019b02, 0x684686820003, 0x203000d58d0d06, 0x64150418001b10a, 0x8008ac08286c003, 0x121b0011589090d]
def page82 : List Nat := [0x563424360022b1a, 0xae2c2280c00006, 0x93041c858450180, 0x63120606398aa02, 0xa80480220c01320, 0xb049c818c50181, 0x461106019b9931a, 0x680220480c03400, 0x300d0091844180, 0x46110601ab9310a, 0x6ec0a6684c13577, 0x282020201818080, 0x48484848484830, 0x686868686858505, 0x890888078706868, 0xd0d0c8c0a8a8a09, 0x101010100f8e8e8, 0x312921211919110, 0x151514949494941, 0x999999917169696, 0x9d9d9d1c9c1c1b9, 0xe9e9e9e1e1e1d9d, 0xa120a0201f9e9e9, 0x524a3a3a322a221]
def page83 : List Nat := [0x2726a5a5a525252, 0xa29a9a928a827a7, 0x2b2b2b2aaaaa2a2, 0xe2e2d2c2c2c2bab, 0xb0b0af2f2f2eaea, 0x2b231b1b1b0b0b0, 0xb3b3b3333332b2b, 0x53534b4b43433b3, 0x37b73736b6b6b5b, 0xaba393939393939, 0xbd3d3cbbbababab, 0x24240c0c03fbf3d, 0xc34342c2c2c2424, 0x64645c544c44443, 0xc64046c6c646464, 0x188a1361625d4c4, 0x60e0012c00295ae, 0x8530727090a022c, 0x284863c60d951d2, 0x85153e4490c0000, 0x60a206b2460b0ac, 0x8006009a9070a50, 0x4f02961c35c1b1, 0xc080498a0abd09e]
def page84 : List Nat := [0x4b3a243aa8835f1, 0x6960c3118f18f44, 0xc6800a2451a52a9, 0x5d027083d81b082, 0x6b5f858215cac02, 0x681883709002986, 0x106aa78c263c0bb, 0x6217fd9c3250243, 0xd4741b31dfa8f9b, 0x1443f793c8710ef, 0xfee4b0087bd0db2, 0x6c20df97010d10d, 0xbf51b3614a7e83e, 0xd8940cfea99b0a5, 0xa7fbb2a6215ff37, 0xf2a465df94c4314, 0x95fb7050b309fac, 0x1c364833eaa0ac1, 0x309fcec21a21bfd, 0x21ac2197de43887, 0x6613fd9e434437e, 0xc43cd852bfae229, 0x4c82fe2b864a06d, 0xfa0f21c433fdd95]
def page85 : List Nat := [0xa8294ff67d5120b, 0xbf9c863542be39a, 0x14f51cfca9ab641, 0xb7f21a0d10d7d47, 0xe29281bfd196014, 0x94fc7655132f7e8, 0xc336d06fe83e8c2, 0x30bbe6faa6653f5, 0xb80c6a0dfd17d53, 0x2a1b714c635037e, 0xf46cd852ef88629, 0x35037e23a0d98ef, 0xfecfa0e613fd9c5, 0xa621eff540d9209, 0xbf50d6114adea3c, 0x15b209fecf29a41, 0x36e31e64a04ff37, 0x19b6a93fcde4648, 0x86fd46cdb209fae, 0xc063553ef21e439, 0x20dfa8eb0063bf5, 0x3b085987be43d1b, 0x8a57b9c843cca7f, 0xd470cb409facf21]
def page86 : List Nat := [0x2542beabe8c197b, 0xf8ecaa241b718f3, 0x8d995fd71189409, 0x7f5c4535035e21a, 0x14b309fe6fab085, 0x27eb3ca79077f54, 0xfa18a57b9c84348, 0x8dee7214f32bfac, 0xcd601535e21a8c1, 0x40bfa0f2a0653f1, 0xbb087905ff3714b, 0xea3f7cdc52cc2fe, 0xd7114f40ef8a621, 0xc67eb3c87885f, 0xfae19b685bf11d6, 0xac196fd71580439, 0x7f5c4325027eb80, 0x91910cfaa82b661, 0xafeb8e4d21cff37, 0x21ea3bf41f3614, 0x96fe2191b30bfae, 0xd16c83efa1e6c2, 0x219fe6f23065bf1, 0xabac021cfc7351a]
def page87 : List Nat := [0x66377cde54ccb7f, 0xd07988539fae1ab, 0x1503beaa665a84f, 0xfe6fb22a1f718c3, 0x6da057d07d53519, 0x3f5c0625077f90e, 0x58053fb8869b0a5, 0x2ff9bca8906fd72, 0xf936a1bfd1b36c8, 0x1cfd6794c429fe6, 0xd6114a7e83cc42, 0x20cfea2a36a1bfd, 0x9bec2a06bc43919, 0xa81bf55d600caff, 0xd7110b30dfece29, 0x6d437ea386c885f, 0xfacf21c439f1494, 0x64a05ff3714940d, 0xbfcdd601067fb3e, 0x14d42ef8a629281, 0xa7e39a8d884ff67, 0xf2a6613f5c06354, 0x84fc7351b509fec, 0xdd06d067fb3864a]
def page88 : List Nat := [0x40df8862b2213f0, 0x31ec2a05fd710cb, 0x6859f5526214f7e, 0xc630c540dfae19b, 0x1cc27fbb2a7a16d, 0xfcec296617f1c94, 0x439867d54580529, 0xbf41f36106fe2be, 0x10730beae221e21, 0xbbeaa0a5984fe76, 0x79b0a59f553568c, 0x95df3795330fb88, 0x9332542bea3ca62, 0x40bfa8e29e65bfd, 0xb88a721dff570c9, 0x2a13f5c063506fe, 0xc7351852cf8c629, 0x14f7eaa2c0194f, 0xfe6f2a641df5516, 0xa81957f570c950b, 0xfb50b36c827fbb2, 0xd5052bf8e6a3641, 0xbbe29ea2a057d07, 0x7936637bc9f544c]
def page89 : List Nat := [0x6fc7258043df88, 0x9c42543dfa3864a, 0x32df8c7a8a813fd, 0x3966d2a6ff4741b, 0x661bfd1f3614b7f, 0x731c8740bfeae21, 0x1c877fa326c297f, 0xfee0aa0a5fd10f3, 0xc6a85ff37d0b50a, 0x77cdc42cc37fa38, 0xd4d429f86e83685, 0x27e83eac21cff67, 0xf21661bf10c2644, 0x5bd47d4f429fec, 0xde46c83f631442a, 0x32dfee4b00a737c, 0xbb087905fd4794f, 0xa21bfd196014e7e, 0xf3709910fec8790, 0x6c837e318a4a04f, 0xfc86b08657fcdf4, 0xc029dfd7010e21d, 0xbfd0c56c877fa3a, 0xc9b549facf21e41]
def page90 : List Nat := [0xb3f29eac214ff37, 0x8192a1bf10d6014, 0x96fe7218d54dfec, 0x19600cb7f9b2c02, 0x10dfce431a81bfd, 0x31884a85f51790f, 0x4a33fd9e434837e, 0xf54cc9509f8e6a3, 0x1067eb866d28f7, 0xf86e83443bf0dd6, 0xd994fd7018d429, 0x7f5c054ccb7e2ba, 0x51852efea9a8e61, 0xa7eb864da0e7c53, 0xf9b6415f51c5314, 0x77d5414d20dfa8, 0x1e530ca7f9b8c4a, 0x40dfecf21e437f5, 0x21e6d906fd760cb, 0xa413f0dd6014b6e, 0xc76507309fcec29, 0x6c837e21a0d10cf, 0xfece18a815f55f4, 0x8da85df37d0730b]
def page91 : List Nat := [0xbfd9c525037f992, 0x14d40bf86eb00a5, 0xafe39aa8905fe72, 0x621aa1af10d4614, 0x9cfc7650b30db8c, 0xc053d473eaa2c02, 0x52df887ab6415f5, 0xb866d2a7be43d18, 0x65bf9c56010e7e, 0xe5458032bfee0a3, 0x35437eaa20d996f, 0xf8862b641afd904, 0x86295ee7214f42d, 0xdf5533614bbe298, 0x10f21dfae231a81, 0x3fb21e6390dfd70, 0x799281bfc8646cc, 0x6fd7018d42fb8c, 0xd16c82f793c869, 0x52cfca9ab065bf9, 0x9beada0efd47cd8, 0x265ef51c325027f, 0xe53580529fecfaa, 0x6d037fa3a0d98f7]
def page92 : List Nat := [0xf8a6296813fcdf2, 0xa5a04fd67d4f42e, 0xefd1c53502feb88, 0x580529fecf98a81, 0x27f9bcc42a6fc47, 0xf10e817fd5f3150, 0x96fe5741b32bfe6, 0xc154cc2fe83e6c2, 0x53fb8879b6417ed, 0xaa0ad9057f76550, 0x6a33f59e54ccb3e, 0xe4758032afe6faa, 0x6c827eb3ca8196f, 0xfae1ab683af10d4, 0x6c296ff71580439, 0x7f15c32d036fa1e, 0x41b319facf29e85, 0xf7f2184c886fe47, 0x2292813f5c32690, 0x977d544d852bfae, 0xc85390efe83ea99, 0x529facfa18a57f9, 0x83ca9997bc43518, 0xa4177cdf544cafe]
def page93 : List Nat := [0xd7218d409fcec21, 0x314b3faa0c6a86f, 0xf8c7a12a17fdd94, 0x86295df3795132d, 0x7fcde215027fbb2, 0x41b32df8a883665, 0xb7e318c2a06fd47, 0xc21e217fdc154cc, 0x95ff57d07309fae, 0x19600cb7f2a20d9, 0x52dfe8f9b621bf5, 0x9bead906fc37580, 0x6635f55c41cc27f, 0xc63c8540dfc8793, 0x68877e23a0d996f, 0xfae0298a53f5c33, 0xa7a167f6414950a, 0xdf14e43d46dea3c, 0xd5052bfaec218a5, 0x2ff390a7a057f37, 0x723221dfd1c5254, 0x6ff5741b42d788, 0xc463502ff390c6a, 0x41dfe8eb00a5bf9]
def page94 : List Nat := [0x9b883986fd70cdb, 0xaa17e5c031502ef, 0xf37189419fece21, 0x2cc3bf9b8a4a84f, 0xfea39b6a1bf9d85, 0xa7a17ce544c832c, 0xbf150364827ebb0, 0xcda41afa0f298a5, 0xafc83c83986fd70, 0x59b6a1bfcdd6010, 0x5fc57c8740cf8a, 0x9e4314bfb98e42a, 0x32df8e2b00877f5, 0xa18ad90eff5441b, 0x8a5df5516014b7e, 0xf6795120ef8a721, 0x6c837fa3e6d904f, 0xde4f21e653fcde4, 0x64a04ff37c9b41b, 0x7f5c04314afe338, 0x15b21ef8a7a8e81, 0xe7f9bec8a96fc43, 0xcaa6617f41f4614, 0x96fc3741b419f8e]
def page95 : List Nat := [0x5d06d0b7f2bac01, 0x32bea0f98e43bf1, 0x21ac2294ff76552, 0x281bf51d600cb7f, 0xf37d1852bfecf99, 0x35427fb3e85985f, 0x7886a3065bf5c86, 0xa6906fd670c940d, 0x3fcdc56442f7390, 0xd0b30bfa0fa3065, 0xe7e39a8d905df37, 0x7b12816f51c5310, 0x1fcd544c832df8c, 0x9f325437eb92c02, 0x309f86eb00853fd, 0x23ac029cff67d53, 0x877f91d600cb7e, 0xd72cda54df8aeb0, 0x6c82ffab865a06f, 0xf8af90a819f94f5, 0x42a05ff7055032b, 0xbfcdd6014affb3c, 0x14c43dfeae83665, 0xe7eb3ea9995fd71]
def page96 : List Nat := [0xf2a6417f09d1690, 0x67f54580529fac, 0xd84314a7fb3862a, 0x50dfae19b4a93f5, 0xb866d20f7c4314b, 0x4853fd9e41cc27e, 0xd70cda429fae19b, 0x614b6e2186c886f, 0x7886a3621df94f4, 0x42886fe7258043d, 0xbf18c62503fa21e, 0x553209feecaa665, 0x27e1bac020dfc73, 0x6a30a53fd9c5250, 0x96bc4351b31bf8e, 0xdf54483bfaa4a79, 0x31dfe8eb00657fc, 0x93e83986ff47580, 0x241afd9342542ff, 0xd1790b30dfa8e1b, 0x610b7eb966daa5f, 0xfa8c9b0a53f41f5, 0xc0217bc4351b20d, 0x77cdc52cc37e1ba]
def page97 : List Nat := [0xd5330bfecf98a81, 0xabfab884a85ff27, 0x29e859f5533614, 0x14ff67d0950bfae, 0x1f560ca7e83e6c2, 0x409fece192813f4, 0xb3c87905ff27cc7, 0x685bfd9c32502fe, 0xd70c9b31df86e83, 0x35037f9ba0da14f, 0xfae19b6a97f5c46, 0x6c886fc6388540d, 0xbf55d06ccb7fa38, 0xc85409fa0f9b0a5, 0x77eb90c6aa5fc67, 0xf2a265bf91d600c, 0x86fd07cd8429fec, 0xdc62502bfab886a, 0x30bfce4298877fc, 0x21a8da857d57d0b, 0x6817fd5f31d035e, 0xf27cc540dfc439b, 0x6d06ff9b8c2a05f, 0xfe4faa2a1bfcdd0]
def page98 : List Nat := [0xc029f7c43d4750a, 0xbf10d6114b3faa2, 0x41b32dfc862b643, 0xafe83c8790efe47, 0xeb0065bf14d06d0, 0xa4fd70c9b54df88, 0x9f5494e7eb80c6a, 0x409fe6fab6815fc, 0x34000375ff27d85, 0x62e60480a0000, 0x3d106400003, 0x54001508020280, 0xc00800117844, 0xd640000a4aec7c0, 0x85f600001000000, 0x50a0087f81, 0x6001ae80e53e000, 0x52000000b083867, 0x60080080380b0, 0x4bdf780800000, 0xc01008000000060, 0x280d01053214836, 0x40808080100, 0xc82201001004000]
def page99 : List Nat := [0x1f00019c0992, 0x3a01800000000, 0x90001a65540100, 0xa01872000038000, 0xc000ff80455, 0x40003c028000010, 0x9006000000004d3, 0x3e6020120080, 0x80600200000053, 0x28020022b20, 0x101406c05002295, 0x1718d4460000, 0x200000007249596, 0x40240880400, 0x669412812034320, 0x32000bbc000673a, 0x151806034011fc8, 0xd20211380004000, 0x17b000080070042, 0x80000002038c00, 0x39e001cf80a1380, 0xa0047824cc0e002, 0x51d58000080100, 0x10340000003e000]
def page100 : List Nat := [0xb58181c200152b9, 0xf8400000000029, 0xdf00090d4480200, 0x90126f6040003, 0x98021e101811, 0x18090d98360, 0x180003c0289ac00, 0x60ece40f20901c0, 0x600000000000016, 0x200000000000, 0xa0000000, 0x30000, 0x400000000000e, 0x1200000000, 0x500000, 0x60000000000160, 0x1a000000000, 0x7000000, 0x880000000001e00, 0x240000000000, 0x98000000, 0x800000000028000, 0x2c0000000000a, 0xb80000000]
def page101 : List Nat := [0x300000, 0x340000000000c8, 0xd800000000, 0x3800000, 0x3e0000000000e80, 0x100000000000, 0x42000000, 0x600000000011000, 0x1200000000004, 0x4a0000000, 0x130000, 0x1400000000004e, 0x1020000000000, 0x408080000, 0x830000000102040, 0x1020e000000040, 0x8080000000, 0x280000002020600, 0x202240000000808, 0x848d8000000, 0x30202000, 0x2060000000c081, 0xc08280000003, 0x302100000]
def page102 : List Nat := [0x2140000000c0848, 0xc086000000030, 0x3022c00000, 0x3a0000000c08e00, 0xc4808000000302, 0x31204000000, 0xe0000000c482000, 0xc48b00000003120, 0x322060000000, 0xc8820000, 0x885000000032210, 0x3221c0000000c, 0xc88b00000, 0x8000000003223a0, 0x40204000000100, 0x10081800000, 0x480000004020a00, 0x402180000001008, 0x104830000000, 0x41236000, 0x220600000010880, 0x1088200000004, 0x422100000, 0x21c000000108848]
def page103 : List Nat := [0x1088d800000042, 0x4223a00000, 0x400000010c8080, 0x10c818000000432, 0x43208000000, 0x10c82800, 0xc8500000004321, 0x432160000001, 0x10c860000, 0xc8e00000004321c, 0x4323a00000010, 0x1408000000, 0x8600000005020a0, 0x51236000000140, 0x14880000000, 0x680000005221600, 0x522280000001488, 0x1488b0000000, 0x800000052232000, 0x22400000001488d, 0x14c8200000005, 0x532180000, 0x22e00000014c8b0, 0x14c8c000000053]
def page104 : List Nat := [0x5323200000, 0x4000000014c8e00, 0x14c910000000532, 0x54218000000, 0x1508d800, 0x408600000011020, 0x11022c0000004, 0x4408c0000, 0x80000000110232, 0x12020600000048, 0x4808280000, 0x870000001202100, 0x12022c000000480, 0x4808c800000, 0x300000012023a00, 0x2120e0000004848, 0x484870000001, 0x800000130206000, 0x20e0000004c082, 0x4c08480000013, 0x1302140000, 0x2180000004c0858, 0x4c087000000130, 0x13022c00000]
def page105 : List Nat := [0x3a0000004c08e00, 0x4c4838000001302, 0x131214000000, 0xc0000004c486000, 0xc48a80000013121, 0x1322060000004, 0x4c8840000, 0x885000000132212, 0x13221c0000004c, 0x4c88b00000, 0x808000001402000, 0x140204000000500, 0x50081800000, 0x400000014020a00, 0x402120000005008, 0x500850000001, 0x140216000, 0x21a00000050086, 0x5008900000014, 0x1402380000, 0x218000000504830, 0x5048d800000141, 0x14220600000, 0x1a0000005088200]
def page106 : List Nat := [0x5088d8000001422, 0x143202000000, 0xa00000050c81800, 0xc8400000014320, 0x1432120000005, 0x50c850000, 0xc86000000143216, 0x14323a00000050, 0x5408600000, 0x8b00000015021a0, 0x15022e000000540, 0x5408c000000, 0xe00000015023200, 0x512180000005408, 0x5488d8000001, 0x153218000, 0x420800000054c8b, 0x5508280000015, 0x15420c0000, 0x21e000000550860, 0x5508b800000154, 0x15423000000, 0x380000005508d80, 0x5508f0000001542]
def page107 : List Nat := [0x210200000000, 0x800000084083800, 0x408900000021021, 0x2202000000008, 0x880818000, 0x8b00000022020a, 0x22120000000088, 0x8848300000, 0x828000002212360, 0x2302120000008c0, 0x8c085000000, 0x100000023120200, 0x3120e0000008c48, 0x8c8818000002, 0x232210000, 0x221c0000008c885, 0x8c88a80000023, 0x23223a0000, 0x20a000000900800, 0x90084000000240, 0x24021200000, 0x180000009008580, 0x900870000002402, 0x24023a000000]
def page108 : List Nat := [0x600000090483000, 0x88180000024123, 0x2422080000009, 0x908840000, 0xc80800000242236, 0x24320400000090, 0x90c8180000, 0x8400000024320a0, 0x24321200000090c, 0x90c85000000, 0x600000024321600, 0x4322a00000090c8, 0x90c8e0000002, 0x80000025022c000, 0x22360000009448d, 0x94c8600000025, 0x25322c0000, 0x23000000094c8b8, 0x94c8e000000253, 0x25324000000, 0x360000009508600, 0x9508f0000002542, 0x310200000000, 0x4000000c4080800]
def page109 : List Nat := [0x408300000031020, 0x31020e000000c, 0xc408b0000, 0x8c800000310230, 0x320200000000c4, 0xc808180000, 0x848000003202100, 0x32021a000000c80, 0xc8087000000, 0xc80000032022c00, 0x2023a000000c808, 0xc80928000003, 0x321200000, 0x121c000000c8483, 0xc848d80000032, 0x3302020000, 0x206000000cc0810, 0xcc082800000330, 0x33021000000, 0x18000000cc08480, 0xcc0870000003302, 0x33022c000000, 0x8000000cc08c800, 0xc08e80000033023]
def page110 : List Nat := [0x331208000000c, 0xcc4838000, 0x48c00000033122c, 0x332206000000cc, 0xcc88200000, 0x850000003322100, 0x33221c000000cc8, 0xcc88a000000, 0xe80000033222c00, 0x32246000000cc88, 0xd00800000003, 0x340202000, 0x206000000d0081, 0xd008280000034, 0x3402140000, 0x218000000d00858, 0xd0087000000340, 0x34023800000, 0xc000000d008e80, 0xd04840000003412, 0x341218000000, 0xd048d800, 0x88180000034220, 0x342208000000d]
def page111 : List Nat := [0xd08840000, 0x887000000342214, 0x342236000000d0, 0xd0c8100000, 0x828000003432060, 0x343210000000d0c, 0xd0c85000000, 0x600000034321600, 0x50200000000d0c8, 0xd40860000003, 0x35021a000, 0x22e000000d408b, 0xd408c00000035, 0x3502320000, 0x218000000d44800, 0xd4486800000351, 0x35122800000, 0x40000000d448c80, 0xd488d8000003512, 0x353218000000, 0xa000000d5082000, 0x508600000035420, 0x35421a000000d, 0xd50878000]
def page112 : List Nat := [0x8e000000354236, 0x354244000000d5, 0x405010000000, 0x18000103404000, 0x332406000080c81, 0x80d0901800020, 0x180002611042c00, 0x20406000098cc10, 0xc8109018000320, 0x32242406000, 0x4300000d84410b, 0xd8c850500003611, 0x403404000000, 0x406000104cc1040, 0x88c901800042020, 0x4232040600010, 0x8000108d090400, 0x441010000430314, 0x4324140800010c, 0x600010c90902000, 0xc90200004333240, 0x4334240800010cc, 0x10cd45008000, 0x904000043354408]
def page113 : List Nat := [0x61504000001184c, 0x118c850400004, 0x20000521504000, 0x253408000148551, 0x148d4100000052, 0x200005235440800, 0x5240800014c10d0, 0x14c951020000532, 0x53332408000, 0x242c0001584410b, 0x585010000005613, 0x563214120001, 0x400000158cc1010, 0x850100000061140, 0x6214143600018, 0x60001885510200, 0x501010000631204, 0x6314040600018c, 0x800018c50105800, 0x10e00006314041, 0x6314043a00018c5, 0x18c505000000, 0x900000063141408, 0x314240600018c50]
def page114 : List Nat := [0x18c5090200006, 0xb0000631504180, 0x15043800018c541, 0x18c55100000063, 0x200006315440200, 0x2140000018c5510, 0x4188c9018001062, 0x106241418000, 0x240600041890507, 0x18cc50080010624, 0x1063324060004, 0x400000418d05000, 0x8d0901800106342, 0x11014040000041, 0x4409010000, 0x90d020001103214, 0x120032406000458, 0x600048010100000, 0xc90180012004240, 0x201424060004804, 0x480881018001, 0x900000120232406, 0x24240600048090, 0x480c850180012]
def page115 : List Nat := [0x20001262434060, 0x24343a00049890d, 0x49894d02000126, 0x680012625440800, 0x544360004989510, 0x498d0d018001262, 0x12634343a000, 0x24040004c0cc905, 0xc80c90100013133, 0x1320324060004, 0x4160004c80c9040, 0x80c907000132032, 0x13203242c0004c, 0x40004c810d0180, 0xc85018001321314, 0x1323304060004c8, 0x60004c8cc501000, 0xd0180013234240, 0x3605242c0004c8d, 0x4d8d09050001, 0x10000014011041a, 0x31040000050084, 0x500d090400014, 0x20001403514020]
def page116 : List Nat := [0x24340800050410d, 0x50808101800141, 0x200014203240600, 0x2040600050810d0, 0x508501018001421, 0x800142232406000, 0x340800050890d01, 0x8c810180014224, 0x1423324060005, 0x43800050c10d060, 0xccc905000143043, 0x14335140200050, 0x1c0005180c50600, 0xc9018001460314, 0x146053444000518, 0x800051894d06000, 0x410600014625343, 0x4631041c000518c, 0x518c81000001, 0x901800146320406, 0x6332416000518cc, 0x518cc90700014, 0x60001463504440, 0x50400000518d4d]
def page117 : List Nat := [0x54094100000150, 0x15035140000, 0x43408000540d510, 0x550149020001540, 0x154150400000, 0x40000055090d02, 0x50d450200015435, 0x1560414360005, 0x40a00055890d0e0, 0x8d0905800156342, 0x15634241a00055, 0x38000558d090d80, 0x850b0001563434, 0x16003141c000580, 0x5800c901800, 0x90000016004140, 0x600424100005801, 0x58010d008001, 0xd01800160043404, 0x4340a00058010, 0x5801490000016, 0x50001603314020, 0x424100005840c9, 0x58410d02000161]
def page118 : List Nat := [0x480016114040000, 0x40400000584c810, 0x58810d018001613, 0x162043408000, 0x40000058850100, 0x88d410000016234, 0x16332042c0005, 0x406000880501000, 0xd0100000220332, 0x22034240600088, 0x4000880d410000, 0x90d010002211404, 0x232242406000884, 0x8000908cc901800, 0x810580024324240, 0x4612041c0009184, 0x98410d020002, 0x100000261140400, 0x2043402000984d0, 0x98810d0180026, 0x8002620434080, 0x5342c00098814d, 0x98850100000262, 0x26234040000]
def page119 : List Nat := [0x41408000988d410, 0x98c109020002630, 0x310010400000, 0x1400000c4008500, 0x5890d0200031032, 0x320232406000c, 0x406000c80909018, 0x4cc901800321220, 0x321342406000c8, 0x8000c9810d0180, 0x90d058003262434, 0x32624341c000c98, 0x8000c989510d800, 0xc50b00032633140, 0x2635441a000c98c, 0xc98d510d8003, 0x901800330342410, 0x2343406000cc890, 0xcd80810180033, 0x60003360414000, 0x42400000cd8105, 0xcd810904000336, 0xe00033605041800, 0x52400000cd81410]
def page120 : List Nat := [0xcd8149020003360, 0x33605242c000, 0x1400000cd884101, 0xd89050200033624, 0x336242400000c, 0x408000cd8909018, 0x89090e800336242, 0x336254400000cd, 0x16000cd89510200, 0x951060003362544, 0x336320414000cd8, 0xcd8c810b000, 0x50200033634140, 0x36342400000cd8d, 0xcd8d09018003, 0x905800336342408, 0x6354400000cd8d0, 0xcd8d510200033, 0xe0003363544180, 0x10400000cd8d51, 0xd0010100000340, 0x34011040000, 0x21408000d009010, 0xd088c9018003422]
def page121 : List Nat := [0x342243410000, 0x1408000d08d5102, 0x180c90200034603, 0x346032410000d, 0x408000d18149020, 0x854100000346053, 0x346320410000d1, 0x8000d18cc50200, 0xd41000003463324, 0x350040400000d18, 0xd4014100000, 0x490000035005240, 0x50351400000d409, 0xd40d51000003, 0x100800351243402, 0x1340402000d44cc, 0xd44d0d0080035, 0x20003522534080, 0x32404000d48951, 0xd580c902000356, 0xb00035603241200, 0x42404000d580c90, 0xd58109020003560, 0x356042412000]
def page122 : List Nat := [0x3408000d5810d01, 0x5810d0480035604, 0x356140400000d, 0x408000d588c9010, 0x8c8101000356232, 0x35632042c000d5, 0x2c000d58cc50200, 0xd05048003563314, 0x356342436000d58, 0xd8050901800, 0x10000036114040, 0x62140406000d885, 0xd885010e8003, 0x102000362143406, 0x311042c000d8855, 0xd8c5010600036, 0x60003631404380, 0x120406000d8c541, 0xd9054106000364, 0xb00036415043800, 0x40438000d944c90, 0x458501048003651, 0x546110400001, 0x41200151848100]
def page123 : List Nat := [0xd85050100072614, 0x746110400001c, 0x418001d18481000, 0x4c501000936254, 0x96014140400258, 0xc818c5018180, 0xd09800371063416, 0x1600416000dc418, 0xdc58010980037, 0x418083716005260, 0x3605260810c0d84, 0x1cc518c81818433, 0x181073154052608, 0x60436061cd51844, 0x1cd580c98110732, 0x811073560426044, 0x4360641cd5810d, 0xcc8010d81947032, 0x94733104360451, 0x5260055098814d8, 0xd180c9821543360, 0x97004311060255c, 0x16065c0c98cc581, 0xd89098197032634]
def page124 : List Nat := [0x707261106005c0c, 0x6005c1cd8505811, 0xcd0982170756110, 0x10631406045d814, 0xcdc09844181b3, 0x505803370523546, 0x326340606cdc188, 0x8cdcc98d0581b37, 0x98133732634160, 0x56320604cdcd581, 0xcdcd58d01813373, 0xd81376330242606, 0x14160551c44010, 0x380280100077633, 0x280f00a80800480, 0xe81c01901801581, 0xd82902782402281, 0x983703403002e02, 0x504284003e83b83, 0x104e84c84a04784, 0xc85a85685485285, 0xb86886606185f05, 0xc87a07707286d06, 0xe08a08688308087]
def page125 : List Nat := [0xa89809609589308, 0x80a68a28a009b89, 0x60b38b18ad8ab0a, 0x30c10be8bc8b70b, 0xe8cd0c90c68c40c, 0x70d48d30d18d08c, 0x78e48e18dd8db0d, 0x58f40f20ed8e88e, 0xe0fb8f98f88f78f, 0x290f1069031010f, 0xc11a91891611491, 0x992712492312111, 0x913613313012d92, 0x314193f93e93d13, 0xe14a14814794494, 0xb15815395294f94, 0xd96c16896596015, 0xa17717597196f16, 0x718518297f97d17, 0x699219118c98918, 0x39a099e99c99899, 0xf9ac1a91a59a49a, 0xe1bb9b69b39b19a, 0x79c51c29c09bf9b]
def page126 : List Nat := [0x9cf1cc1ca9c91c, 0x71d69d49d29d19d, 0x9dd9dc1da9d91d, 0x19f01e89e59e19e, 0xb1f99f79f69f49f, 0x9206204a021fd1f, 0x3211a0fa0ea0da0, 0x321fa1ca19a1521, 0xb22922722622522, 0xa238a36a32a2ea2, 0x724624324023d23, 0x5a52a4e24b248a4, 0xf25ea5c259257a5, 0xda68a66262a6025, 0x8a76275273a70a6, 0x428127d27ba7a27, 0x4a9329028ba86a8, 0xe29d29c29a29629, 0xc2a8aa62a229f29, 0x4ab32b1ab02ae2a, 0xe2bbaba2b7ab62b, 0x92c82c62c4abfab, 0x5ad2ad02ce2cb2c, 0xdadcadbada2d72d]
def page127 : List Nat := [0x42e2ae12dfadead, 0xaefaedaea2e62e, 0x2b00afeaf72f42f, 0xe30a307b06b04b0, 0x9316b14b12b10b0, 0x532332031cb1ab1, 0x3b30b2bb28b27b2, 0xd33ab38336b3533, 0x8346344b4334133, 0x6354b5335134a34, 0x4b62b60b5c357b5, 0xdb6bb69b67b66b6, 0x7375b73b72370b6, 0x6b8237f37bb78b7, 0x3390b8d38a388b8, 0xe39cb9a398b9539, 0x9ba6ba53a4ba2b9, 0x63b1baf3ad3abba, 0x23c1bbe3bb3b83b, 0x3cdbcbbc7bc5bc, 0xbbd83d73d63d3bd, 0x4be2be1be0bddbd, 0x2bf03ef3ec3e93e, 0x3c003fb3f83f73f]
def page128 : List Nat := [0x3c0fc0b40940640, 0x41ec1d41bc19c1, 0x9c29427c2542142, 0x3430c2dc2bc2ac2, 0x644443fc3bc39c3, 0x7c55c5244d44944, 0x5463460c5cc5ac5, 0x4c70c6d46ac67c6, 0xe47cc7a47947647, 0x7485c84481c7f47, 0x7494c93490c8948, 0x4ca149cc99c98c9, 0xa4b5cae4aa4a74a, 0x7cc14be4bccbbcb, 0xfcce4ccccacc94c, 0x9cd7cd5cd54d1cc, 0x7ce5ce4cdecdd4d, 0x3cf24f0cefceace, 0xf4fbcf94f64f4cf, 0xad08506d05d034f, 0xad1651451150cd0, 0x9280d82b4551dd1, 0xa44050220728161, 0x2f72610c1d1be0f]
def page129 : List Nat := [0x8f7115681201a05, 0x8b2048f4f284911, 0x81a0512626dc2f3, 0x82e340360d81e48, 0xcd3322de3516cfa, 0x8a62a036a8dd6fa, 0xa0e10a9c7902804, 0x1271a16820b828, 0x39648b81f95e0a, 0x992098867f81400, 0x174ac046fabe2bc, 0x2e0a818050b51f, 0x2a781b2261f223, 0x5723e9f32712c2b, 0xd340a02e0a81805, 0x2534c54930300b, 0x82609149698360f, 0x2380d8161023a4f, 0x2dc121b20f0135c, 0x1435834100372e, 0x490041360ddaa21, 0xd3d560560bd1f4b, 0x2cfeca60b976b2, 0x8420bd18098140f]
def page130 : List Nat := [0x99cc13e00abde09, 0x1488b518ccb1867, 0x81a0500e48a9507, 0x3608d000d80607, 0xd84930300b82937, 0x363083e0b3500d, 0xb46d1152040e6ca, 0x9788c0386059974, 0x8d00d82e10cd25e, 0x8e746a5e099d2fa, 0x250ac82a0a01404, 0xe028361a0b631, 0x4f07404a0781a05, 0xaf27e03609ad40b, 0x816ff02230ada0d, 0x1c25602e0a026fc, 0x87e0a0128204844, 0x1b86f82e098d811, 0x9b4d2822c40365b, 0x82f4de08b48d1, 0x838b68b6aa81204, 0x360781a0501201, 0x2320da360b5c973, 0x3600b0366f23f01]
def page131 : List Nat := [0x82a450f20d01ca1, 0x8120380605036f9, 0x93c2f4947401e06, 0x270a049214827a, 0x82ae59c4e69320a, 0x9a02208a6696409, 0x32e0da6ed7dc0fa, 0x8280581265104d7, 0x9ae50956d01080d, 0x40d02ab07aa7251, 0x13f82e0d9460a, 0x4dc7196ca99c002, 0x23b2ead828a4b78, 0x1ea3039c09a3c10, 0x84011aace94846c, 0x2ae5707d22c8881, 0x121b8f00dbf6fd, 0x81a0eaaa6e02a05, 0xc5a9b82e0e4d285, 0x2c40d3be7302a09, 0x92ea00380b8284c, 0x2e0a818053807e, 0x3209878762608a, 0x8120181e03aa20d]
def page132 : List Nat := [0xc520e2240d81448, 0x82e0f0d910c4001, 0x154518287514809, 0x19aad99009c1e95, 0x1e136022bb3394c, 0xb6aa8980a81404, 0xcce0d90c7b9e080, 0x146a2c031834b9, 0x8980a828f102e0f, 0xaaa4c8c07a83669, 0x2aa040bc2e8380d, 0x26a0dd520797c12, 0x82f39baa098113a, 0x4e878060981a68, 0x148750fe6b06092, 0x400f5c573d5d65, 0x3a18a4a0981c00, 0xb068682cfa2beae, 0xa8c0a8153f02230, 0xa3e90032e502eb2, 0x81ecfc344210006, 0x82e0a8fe6b04c0d, 0xce8cab8c103c6c3, 0x4ec0e38e1083609]
def page133 : List Nat := [0x808818368c84610, 0x446f8400e82608, 0x9ea0f174090aa12, 0x538099603f9ac07, 0xac8779104a02e0a, 0x2b041c0f094a60b, 0x47b1e30d1dafb42, 0x810e304048836a5, 0xa4c0c028cb148ac, 0x3203583e562a80d, 0x360b012778a2a6, 0x8000502b4882636, 0x8364582e0a01804, 0x8e63914c510d70e, 0x8d48223a0494a, 0xb6aa82a0501204, 0x836460260718849, 0x12038069381e0d, 0x36408ce47401a05, 0x2b20a8140480c02, 0xd795008b6a5ac31, 0x128a50366002c09, 0x2ecc1ba0a82405, 0x9b80da800e028c2]
def page134 : List Nat := [0x8267299ab8d6653, 0x8476f48b1c99811, 0x822c1836d30273c, 0x280498aa8b4541, 0xa460d8300a89ea8, 0x81c048063604656, 0x82665846428da09, 0xcc20db36880300b, 0x50878ba0a03409, 0x80e0183725a264a, 0xc927401e0681404, 0x7e099ca0ba3011, 0x82b55d5507998ab, 0x24e7403734bb80b, 0xdb3a4e73882604, 0x82c0657c28bfc0d, 0xe09b170080235e, 0x48261e01102efe, 0x36078060681457, 0xb5a3a8d60503436, 0x1203008710380d, 0x2167582e0982c05, 0x81485836398e055, 0x1c55082f3d49e06]
def page135 : List Nat := [0x3834fc145fa6c52, 0xa6c0108a1004551, 0x83e0d9648e2368c, 0x9420d2c8a30fe36, 0x2c2782b2e52e38, 0x1a054b4080c0b7, 0x5482aaa20b02acf, 0x2ed39800d8175f, 0x464d03609950b0, 0x8360c02f1d0d05b, 0x97010bc60ba7b52, 0x8140d0da2b2640c, 0x96e040372781e0e, 0x8360d8a94952708, 0x26050126e824a8, 0x7e0a012b39646e, 0xa78068062302e7a, 0x98eb40fe6b04e87, 0x2abadaf6d24e19, 0x812038067a8362b, 0x81c438a2a8c1007, 0x41378400b03d42, 0x820044080db8c37, 0x828060120002316]
def page136 : List Nat := [0x82f469e6580140b, 0x9ec0c8290782610, 0x932098240885c0d, 0xcc0b82c050360a, 0x1e00daa21b95221, 0x482c9b20f01426, 0x242a3aac0b82747, 0x180480118a38e6, 0x140f0360982e0a, 0xa0c040485a02400, 0x82c0a8275198cbc, 0x2a0b448411780b, 0x37339380dada5f, 0x140d8400981d45, 0x850879fa0a48f1a, 0x140d82725a2614, 0x9fcc03425e89c0b, 0x1080b828060132a, 0x94a0d9f80e0c02f, 0x2607204493925e, 0x27678330e83646, 0x86c1c9b60d8360d, 0x80e0e1245902608, 0x420dae40383607]
def page137 : List Nat := [0xafca42d2920343f, 0xbeaab0b60b8ec3a, 0x36078004001a41, 0xa983683e6b0fe13, 0x384098365d88428, 0xa80dbda380e762, 0x82089326f82402, 0x9640983282ad6ac, 0x46104ecc403c0d, 0x1b8710260881236, 0x8361a02c098403a, 0x81a0500e01b5204, 0x360b0269608c07, 0x2368e99ad9a780f, 0x2604d12f78470c, 0xab8770140b036a5, 0x9c43641c5256b01, 0x36050de0702a0d, 0x356e3b603802c06, 0xd42d8161083c0e, 0x836d6836ca0c2d7, 0x1e050120380606, 0x8dc498ead625823, 0xc39079545e82666]
def page138 : List Nat := [0x39528c16b202e49, 0xb04f902a3202e11, 0x1a050120192285, 0x3d51f8123d83646, 0x3e87582c0982659, 0xd7cc5afa3082c5f, 0xb69e0360b82a09, 0x82a3a1c522a34ad, 0x8842d8b0730d00d, 0xbf0351fe358e437, 0x8580cd03158120d, 0x32072407b0328f, 0x3540db103f02c16, 0x4ae0b02a2a2000b, 0x1c40bd16b802878, 0x8372f82611d3e9b, 0x2a40a808005000b, 0x9640982b7758c5b, 0xb88c8995602dcb6, 0x1ea0d9260f82651, 0x8ea369326f82402, 0x82804840a8a829f, 0x2800e02f4d828b3, 0x576269480d82e44]
def page139 : List Nat := [0x826120080b82a06, 0x261182e0f048e4, 0x56334d01580e0e, 0x4ec9e02a0025c0e, 0xa3465aaa8583410, 0xbdef64a06404609, 0x89e0a0120121411, 0x81c0bd00b20c29a, 0x12011740984409, 0x400f02c8dba00a, 0x81a018000bbdd41, 0x9ac9f04e8788e0d, 0xc4771d9663ad03f, 0x26c0f4d2f356614, 0x482182e0e02636, 0x82a2481ca787e84, 0x9d00f4643d1ec0d, 0x6e3f9ac4201e95, 0x8851544e51bd20a, 0xa880e014fabc266, 0x8d84f0de7c02adb, 0x2e0a828e98d50c, 0x5000e8380981435, 0x2da718360b02b37]
def page140 : List Nat := [0x9fc2302e0648630, 0x8343ac5f1a02a0d, 0x35a5b56f1caf2b6, 0x4e943342a583606, 0x9c60d826859340d, 0xa98358d8ebbc0ee, 0x8360982d3482804, 0xa2a07286bf82610, 0x38d11520d84204, 0x4502ed64ae01805, 0x9fa2302e0a81805, 0x232255600d8300b, 0x8340d82c22164ba, 0xda20db8f1258e5c, 0x854098088acca0b, 0x16c7d112929c01d, 0x25495a5b09de330, 0x23e0ab4c4f02a80, 0xe471b6099da9a, 0xc4a130360981e07, 0x8fe6b0d6c7acc0f, 0x32635834c90ea49, 0x2c60d96c0e3ff5f, 0x83e09c584c0347e]
def page141 : List Nat := [0x82e0e48a30cfe35, 0xf6f441d1ab8a72, 0x48c2afa0f83c0b, 0x365482a072e45e, 0x8fe0984940c806e, 0x8127403609cee0d, 0x3ca09957314c209, 0x54e30c3741b7a1e, 0x82a0d9f62302a05, 0x2704c966000149d, 0x2ea466e231f76, 0x416b202e1cb1e0c, 0x99485bb0863bd29, 0x3c8380e8ecbac3b, 0x3003b82610c2f74, 0x21235814043220d, 0x8000e02d35836c9, 0xc3c0d922db36a04, 0x932998d6c7acc0f, 0x82e0e026c92121c, 0x848211f4e594090, 0x82d10b3a0981201, 0xa427082f2814a09, 0x1f034c1c3519635]
def page142 : List Nat := [0xcb040a14399cc7e, 0x9d68b09e0d82804, 0x8367ab85640220d, 0x82a7f2aa6e1326f, 0x2720dcaf2b0a808, 0xaa2095de6d02b38, 0x9528c0cc098380a, 0x82638a7c0d2ca16, 0xac22e2602602e0a, 0xd280d9f80e0c090, 0x25c0db2c1a94946, 0x9b82301a0536496, 0x38c1059add03609, 0x3701324126ae412, 0x19a671cedf90c87, 0x44e0a0174c9e003, 0x836055220981d13, 0x806068367107e10, 0xcf67401e0501203, 0x3431b52d181c40d, 0x3ec1003c0896422, 0x908818403a2a259, 0x2a09ccc0b8cb22, 0x81ca8dd53516c7d]
def page143 : List Nat := [0xcf93c826051d00d, 0x814048100235808, 0x99c380b6aa8548a, 0x8156ddba100220f, 0x1a0ed3465483610, 0x148dbb6ec19e67, 0x26049aa9bb0d17, 0x361fa2c3f82c0a, 0x1ba6e02a090122a, 0x8140480603836ac, 0xdeb3f2582301e06, 0x1eac6c180984979, 0x36cd01e120bc0b, 0xcea0b8395113472, 0xd5b5620c7d0574e, 0x2acdb1c0a02688, 0x1780dc480499c0e, 0x404a8ae091e0b9, 0xa005c02804804b5, 0xba28bc709c9620a, 0xa98158360a02604, 0xadee79e65822c57, 0x26512f78270f, 0x4581902e0a81805]
def page144 : List Nat := [0x8140a012010b87d, 0x1bc09ce20daac2d, 0x85aadab40eabc0e, 0x1e068140383878, 0xe028060d83647, 0x4d89608c0781a05, 0x81e06812019ea12, 0x3610043368360d, 0x8856903ebd3060f, 0x508aba2543beaf0, 0x10700c00f5bd541, 0xf80cc4406c8c0e, 0x4680d9500ab7e2b, 0x12011e405046cf, 0xc9ed801a050360a, 0x2a090721c09a0d, 0x82805d8346042aa, 0x836710d55b56a0d, 0x3e0883cfba6278, 0xbe0d82b3fa6d1d, 0x826538400981d37, 0xd7ea4a460d8300a, 0x1740dd10291d411, 0xad60da4c0c028ac]
def page145 : List Nat := [0x81a018000bcdc71, 0x8906b27e13a1e0d, 0x1f56cb6e63ad03f, 0x9640aaac5b02e35, 0xda00d82a09c3cc4, 0x82a19520960d811, 0xd4b62ad40d8300b, 0x5470797e8091ae4, 0x19a09a7411b8728, 0x2960b0276fcd32f, 0x3758aa06143848, 0x812038062a22c5f, 0xa2a0b8360692207, 0x24a13a1e0682601, 0x368521d43f8626b, 0x1804a2a2f5156c, 0x8392d0555d02e0a, 0x574a881c08b98a2, 0xd9c0d8260500012, 0x8260781c0010006, 0xcb23f9ac1305e91, 0x9b851b760d91f72, 0x3480b82c0dcfa54, 0xab45aa8e0d9b20f]
def page146 : List Nat := [0x12018d8dca2a03, 0x9c80c8361582607, 0x1a407012d88340d, 0x8140a0124ea16df, 0xd5009cc60d93427, 0xc1f061f86017e80, 0x8a953ca95341504, 0xc30090207248a0d, 0xab90b42a9525295, 0x41b41508aa8400f, 0x140e55f6e5e908, 0x89a071560a9b20f, 0x58a603740d9140d, 0x83a0d3025f9832e, 0xf01003eae9a82b, 0xb140a41f4c02706, 0x910618ce2602e0a, 0x81cbe31c0a0261e, 0x2b20da3e1603225, 0x2607080bbb7894, 0x3607cb84203ce4, 0x126670a0a68fe6b, 0x4b612036068140e, 0x8080bada0daf083]
def page147 : List Nat := [0x95776de44c9c00a, 0x2651b906549600a, 0x30a5ef21e61fe2a, 0xa0e21f721641fea, 0xe21863ff21ea3fa, 0x7f930857e2b283f, 0x9fe20e617eb0887, 0xa5fb28a217e8b6a, 0xea37f23065beaa0, 0x36a1ff29e85fe21, 0xaa6617e836637f9, 0xf20e617e8b465ff, 0x7fb22a17e8b641f, 0x7f6a1641fb90a21, 0x83ff298877ea34a, 0x641ff9b0a57f9b4, 0xb687ffa16617f23, 0x9b641fea96613ea, 0xe31281feaa6417f, 0x7e2b221fe8b4877, 0x3fe2a6617e1b641, 0x61feaa2657f9b4a, 0x6637e31283feaa6, 0x9e657f310a77f93]
def page148 : List Nat := [0xa16a1fb20a21fe2, 0xea30a7fe21a41ff, 0xfe9b485ffa36417, 0x7be298a57f9b083, 0xa5fe21e637f9b08, 0x6a1ffa0e61feb00, 0x1aa5ff218a5bfaa, 0x8b4877e8b6a77e3, 0xe29661fe93487ff, 0xfea1ea37e83485f, 0x7ff2a6617ea3621, 0xa97fab687fe29c8, 0x6a17ea36a77f9b6, 0x3683fe192a17ea3, 0x992817e2b6417e8, 0xe31aa17ea3463ff, 0xe6990657e8b6877, 0x37e2b287fe29281, 0x417e312873eab08, 0x65ff21e437fab6, 0xe817e8b4877fab, 0xa30657ea3063ff1, 0xe31263ff10e617e, 0xff996a1ff28e617]
def page149 : List Nat := [0x57e31aa97eb0065, 0xa1faa0a21ffaa26, 0xe61ff9b641be296, 0x22a5fe2a665ffa8, 0x298657e2b2817fb, 0xf90e81ffb0a81ff, 0x7e2b0657f23221f, 0x1ff98e817eb08a7, 0xa97a30a65fe21e2, 0xe61ff996817fb02, 0xa0a57f23661fea0, 0x2a641ff29e41bfa, 0xf21e637fb02a5ff, 0x7fab0857f9b443f, 0x1ff90e61bfaa6a3, 0x837f9b4a9fe21a2, 0x263feaa6657fab6, 0x3665ff992a17f23, 0x834a77eb00a77ea, 0xf23265bfaa4a77e, 0x7f232417f9b4a77, 0x3f7212417fab663, 0x877fab087ffa1ca, 0x681fe9b0a57fb0a]
def page150 : List Nat := [0x1e657e836a9fe29, 0x9b085fe29a41ff2, 0xf9b6a17f9b6857f, 0xff93487ff298857, 0x1bfa8ea17eb0865, 0xa97e8b6a1be292a, 0xa817ea34657f310, 0xb2657fb0283ff90, 0x31a837fb0a813f2, 0xeb00a57ea36417e, 0xff2a265ffa8a817, 0x57e836657fab681, 0x857f93487fea988, 0x8a5fea36417f9b4, 0x8a81fe29887ffa1, 0x298a57e8b681ff9, 0xeaa4657ea3443bf, 0x7f310877eb08a5f, 0x17f9b6817e2b643, 0x61ffa9e85ffaa24, 0x8a5bfaa2a1fe216, 0x9e657ea34a3fe21, 0x2a465ffaa665ff2, 0xe83685fe31281ff]
def page151 : List Nat := [0xbeaa6a1fe18a817, 0x57fb02857fab485, 0xa5ffa8e81fea18a, 0x8a9ff216617ea30, 0xb465fe2a2417eb0, 0x936877eb00a97fa, 0xe29e853eab4637f, 0xffa1c43fe29e81f, 0x3beaa0a77f318a9, 0x61ffa3065ff21c4, 0x681ffa9a857e2b6, 0x1c43fea1661fe19, 0x218637e83483fea, 0xe30a81ffa12a1ff, 0xfeaa065fe21c43f, 0x5fe21aa5fe31a81, 0xa9fe21e417f9b0a, 0x2a77e834a37f936, 0x30a7fb98e437fb2, 0x13221ff21e41ffa, 0xe29a857f936837e, 0xfea30a77ea3663f, 0x1fe21ea17eb0063, 0x41ff9b4857f9368]
def page152 : List Nat := [0x621ff2a665ff29a, 0x18657eb00837f9b, 0xb00a77eb0087ff2, 0xe2b2637fab487fe, 0xff21e217f936a77, 0x1ff2a0657e31a85, 0x81ff21a41ff2a24, 0xe65ff10a81fe18e, 0xb221fea9e85fe21, 0xa30657e8b4857e1, 0xf93465ffa30a5fe, 0x7e83487feb00657, 0x3fe29a81fe21ca3, 0x217e83443ffa1e4, 0x4a97eb0085ff21a, 0x1e437f9b6837e83, 0x192817eb0885fea, 0xe31a81ffb1281fe, 0xbe29ea3fe21e437, 0x73eab685bfaa0a7, 0xa1feaa2413fab68, 0x8657e1b241fe212, 0x1ea3ffa1aa5fe21, 0x18ffe21aa1ffa]
def page153 : List Nat := [0x30012f80421800, 0x1000000001a800, 0xe58007c8f600000, 0x1ce000000042e, 0x30000a000, 0x9880095be2, 0x100000000008, 0x21e0100000000, 0x18a0a02635c56, 0x4003a63b800, 0x4e0000000000, 0xfd810a3c26, 0x8800000000348a, 0xc6e18000c800, 0xe6b72000012e800, 0x2b6c380c16800, 0x100000000004, 0x1da0000007afa, 0x43a0027e51856, 0x10000000124804, 0xa78001780000018, 0x3804bc800, 0x7a72000000e8b2, 0xd8800000012aba3]
def page154 : List Nat := [0x200094b2600000, 0xae800011c238800, 0x17b25800c2800, 0x8d8000000000366, 0x80acabd882a2800, 0x2160100019806, 0x3820000040800, 0xc000b70a800, 0x93bae5a80121a1a, 0x3380c0000000000, 0x5b8000045e00000, 0x176279420044a, 0x856aa677800, 0x3220020a02000, 0xe000ed8ea, 0x28000ba, 0x2b8005c800002c2, 0x1f800002ea01000, 0x122003da00004, 0x72030108bb1e, 0xb800003aa0f000, 0xb4c620000006000, 0x4b2000000034e, 0x898000040e00004]
def page155 : List Nat := [0x626a9e200000, 0x1199b2a1800, 0x80000000001000, 0x40000000, 0x8000000018, 0xc00000002800, 0x100000000380000, 0x48000000, 0x5800000014, 0x680000001800, 0x780000001c0000, 0x28000000, 0x300000000b, 0x340000000c80, 0x380000000d8000, 0xc0000000e800000, 0xf80000003, 0x108000000400, 0x11800000044000, 0x280000004800000, 0x4e0000001, 0x52000000140, 0x20600004080000, 0x3a0000808b00002]
def page156 : List Nat := [0x84820000202, 0x848d80002122c, 0xc08e00003022c00, 0x8b00003023a0000, 0x8000322040000c4, 0x322080000c881, 0x322100000c88380, 0x21c0000c8858000, 0xa0000c88b000032, 0x1008000003223, 0x104810000412020, 0x483000041208000, 0xd80004121a00010, 0x422000001048, 0x42208000108818, 0x221200010882800, 0x1a0001088580004, 0x1088d8000422, 0x10c8080004223a, 0xc8180004320400, 0x8580004320a0001, 0x4321800010c, 0x4323800010c87, 0x5023800010c8e80]
def page157 : List Nat := [0x2080001448d8000, 0xa00014882800052, 0x1488b00005221, 0x1488d8000522320, 0xc83800053208000, 0x600005321600014, 0x5322c00014c8, 0x5323200014c8c0, 0x324400014c8e000, 0x20001508000005, 0x150820000542, 0x1508580005420a, 0x508680005421800, 0x8e0000542360001, 0x800110204000150, 0x11022c00044086, 0x202060004408c80, 0x21c000480840001, 0x20004808b000120, 0x4809280012023, 0x4848b0001212080, 0x8e000121236000, 0x80013023a0004c, 0x1312040004c48]
def page158 : List Nat := [0x1322060004c48b0, 0x221c0004c884000, 0x20004c88b00013, 0x500810001402, 0x50082800140206, 0x8400014020c00, 0x860001402160005, 0x14021c000500, 0x14023a0005008e, 0x412080005048000, 0x2060005048d8001, 0x200050882000142, 0x5088500014221, 0x5088d80014221a0, 0xc86000143204000, 0xe80014323800050, 0x15020a00050c8, 0x15022c000540860, 0x2320005408c000, 0x2c0005408e00015, 0x5448d8001512, 0x5488d80015222c, 0x4c8b00015321800, 0x800001532380005]
def page159 : List Nat := [0x154202000550, 0x15421800055082, 0x542300005508680, 0x2380005508d8001, 0xc00084086000154, 0x8808000021022, 0x884820002202060, 0x48b00022121a000, 0x180022123600088, 0x2322100008c88, 0x23223a0008c88b0, 0x23a0009008e000, 0xc0009048200024, 0x9048d8002412, 0x90881800242200, 0x88280024220800, 0x8500024220c0009, 0x800242216000908, 0x24223600090886, 0x432020009088e80, 0x20600090c810002, 0xa00090c82000243, 0x90c8500024320, 0x90c860002432160]
def page160 : List Nat := [0xc8e00024321c000, 0x24323a00090, 0x25122c0009408, 0x25222c0009448d8, 0x32180009488d800, 0x3000094c8b00025, 0x94c8e0002532, 0x95080800254200, 0x508280025420800, 0x860002542160009, 0x80025421a000950, 0x2542380009508d, 0x1022c000c408380, 0x206000c408c8003, 0xa000c8085800320, 0xc808700032021, 0xc808c80032022c0, 0x9280032023a000, 0x4800321208000c8, 0x32121a000c848, 0x32122c000c84870, 0x202000c848d800, 0x6000cc08100033, 0xcc0838003302]
def page161 : List Nat := [0xcc085800330210, 0xc08700033021800, 0x8b000330220000c, 0x330232000cc0, 0x33023a000cc08e, 0x31218000cc09280, 0x22c000cc4870003, 0x6000cc48c000331, 0xcc88200033220, 0xcc8850003322100, 0x88b00033221c000, 0x800340200000cc, 0x340204000d008, 0x34020c000d00818, 0x218000d0085000, 0x1c000d008680034, 0xd008e0003402, 0xd048000034023a, 0x48100034120200, 0x84800341208000d, 0x800341218000d04, 0x341236000d0486, 0x42208000d088180, 0x212000d08840003]
def page162 : List Nat := [0xa000d0885000342, 0xd088700034221, 0xd0c810003422360, 0xc86000343214000, 0xe00034321c000d0, 0x34323a000d0c8, 0x350218000d40858, 0x22c000d4086800, 0x32000d408c00035, 0xd408e0003502, 0xd4482000350244, 0x448b00035121a00, 0x8d800351232000d, 0x800352208000d44, 0x35322c000d488d, 0x54200000d4c8e00, 0x208000d50808003, 0x6000d5082800354, 0xd508600035421, 0xd508c00035421a0, 0x8e000354236000, 0x1800354244000d5, 0x3204340609850d0, 0x1104020c890d018]
def page163 : List Nat := [0x40210c14902036, 0x810c8850204311, 0x10ccc5008433214, 0x8d5100043351408, 0x90205235440814, 0x205632140014cd, 0x62140402158c85, 0x214140818850500, 0x4040418c5010086, 0x40818c501018631, 0x618c55102063141, 0x1890d0090624240, 0x90d009063314024, 0x902116242400440, 0x211635440045890, 0x40331402458d510, 0x324085180c9019, 0x1404518c8101946, 0x85501490014633, 0x558105001540524, 0x8d0900156041408, 0xc90195634240855, 0x9600414005800, 0x96004340458010d]
def page164 : List Nat := [0x33140458010d01, 0x424085841090016, 0x408584149001610, 0x888450100161052, 0x18cc100a2124340, 0x90d023211404009, 0x500326243402c84, 0x326341408c98d0, 0x26354408c98d510, 0x242406cc0505013, 0x3404cc090d00b30, 0x4cc490d00b3104, 0xcd8105003312434, 0x814900336042400, 0x901b36052408cd, 0x336242408cd89, 0x336340402cd8951, 0x6342400cd8d0500, 0x32408d00cc500b3, 0x408d18149023460, 0x8d44d5100346053, 0x581090035135440, 0xd0500356042408d, 0x501356341408d58]
def page165 : List Nat := [0x154611040541850, 0x1400e001cd85050, 0x5604c03c02e0200, 0x9608207806c05e0, 0xe00d00bc0b009e0, 0x2e1201140f60e60, 0x6a15e15214a13e1, 0xb61a819a18a17e1, 0xf81ec1de1cc1bc1, 0x3a22e2202162061, 0x8a27e27025e24c2, 0xd02be2b02a829a2, 0x182fe2f02e42dc2, 0x6234e3443343283, 0xae39a38a37a36e3, 0x43ea3d43ca3ba3, 0x4c44042e42240c4, 0x9248247846645a4, 0xce4c44b64a449c4, 0x1e5104fe4e84da4, 0x5c54e54053452a5, 0xae59c58a57a56c5, 0xf85e25d25c85bc5, 0x346246186086005]
def page166 : List Nat := [0x7a67265e6506426, 0xb26a469a68a6806, 0xfa6ea6e46d66c66, 0x467347247147066, 0x9478677a7667567, 0xcc7c27ba7b079c7, 0xa8007f67e67de7, 0x4c83c82e8228168, 0x9c89088086e85e8, 0xe28d48c88bc8ac8, 0x1690a8f88f08ea8, 0x5294693c92a91c9, 0x9698a97c9749629, 0xe29ca9bc9b29a29, 0x2ea1ca14a049f89, 0x74a6ca5ea4aa42a, 0xc4abcaa4a96a82a, 0x12b06afaaeaad4a, 0x4ab38b32b2ab1eb, 0x82b7ab72b62b58b, 0xbcbacba6b9cb8eb, 0x2bf0be4bd6bccb, 0x5ac48c32c1ec14c, 0x98c8cc7ec70c68c]
def page167 : List Nat := [0xe2cd0cc4cbaca8c, 0x22d16d0cd06cf8c, 0x72d66d56d46d34d, 0xb4daad96d8cd80d, 0xf6deaddedc6dbcd, 0x3ae2ce24e1ae04d, 0x82e6ee5ee50e46e, 0xc4ebaeaae9ce92e, 0x1ef06efaeeaed6e, 0x62f56f40f34f26f, 0xa6f96f8af7ef6ef, 0x2feafdefc6fb6f, 0x4103b0310230190, 0x8f0850770670570, 0xf34878d10a909b0, 0xe2c2a213107c2e7, 0x385490a38281c10, 0x675031daec0f300, 0xb9dcc8c7285d1a1, 0x901c9c051a2d210, 0x10313c5a15272f0, 0x45801e0a1a4382, 0x3a110e30a34c562, 0x27f8f6020503234]
def page168 : List Nat := [0x85d3c130e075ef0, 0x2c21b40340c05b4, 0x654155541735a60, 0x870356f90afee05, 0x9d3927b14320801, 0xb2532439380a550, 0xc20321106b6c423, 0x381557870425b92, 0x8b204c22780e9dc, 0xa94230007079f54, 0x1345a250df0f730, 0x103c1024150ee2b, 0x22c2300814057a1, 0xc76092b4e81d7f, 0xca450826170881c, 0x859eaf00b0747e0, 0x2e1a913b1de1e49, 0x5278647e0c04518, 0x1319a490f021b21, 0x330609af42e166c, 0x50fe48a9080a070, 0x80180130f073225, 0x3cf87fca2020801, 0x1808442e157ec90]
def page169 : List Nat := [0xbfd401e0d40dfaa, 0x26110f080561c0a, 0xd53aaddc1e3e420, 0x84c3c400e08022e, 0x3e190fb4434af12, 0xc2888428173d872, 0x8782a1c35044a01, 0xc81e7f9a0421308, 0x16a8842c1d33194, 0x84cfeac3f2ac321, 0xff02559f51ca60b, 0xc7e2a1f1400f401, 0xd702c4614074261, 0x701d148482d5b06, 0x101b5c381e09845, 0x8283c152f880261, 0x7a830b85a1a5c0f, 0x10f4d4426d461b1, 0x134921e0a9c49d3, 0x14a90f25c3a1a38, 0x20e3b03d6bb7484, 0x703ec60f23e512, 0x3b8f0c8f42e110b, 0xb828ba5b1795c]
def page170 : List Nat := [0xb2194ce08835961, 0x401206028100664, 0x30e02c9d065e054, 0x154ae6e10850395, 0xee8b0e87202ff90, 0x1988103c1d10c75, 0x839a4192a071a22, 0x42210b078921408, 0x7828502a1c0c845, 0xf0321f68868220, 0x321f6886896c903, 0x18095c98ca09498, 0x94c240e813fc282, 0x1f0f45c381a2a, 0xc9d4e428964bcec, 0x8dd181709859921, 0xbef87b879faff71, 0xd0a865c2fc7db81, 0x7820d208978141, 0x22150ed371c5b65, 0xe0c84e904f0e878, 0x85727a53e421b21, 0x3a1390849a41d09, 0xdd2485561e5d29c]
def page171 : List Nat := [0x2686a1a0a8d83d6, 0x408a0e845121c8e, 0x937044285710872, 0x46181e8684c2a8, 0x360e098582a8841, 0xf08830321f0b856, 0x5004110a8716a2, 0x12520f8782c150c, 0xd0a0441c8a2b871, 0x52c24032e04c2a1, 0x2a1cb95c4220e0b, 0x10e05028031a84c, 0x3c9a2119ecf0a02, 0x98c97984c3b837a, 0x9fcf43814c12f1, 0x74390b08820062, 0x671802818f61390, 0x70b06834b18a2d1, 0x2583e1c0d0400c1, 0x381a7e2d2040d06, 0x60e8482a167facc, 0x40dfb016a84c223, 0x2b350f3fda81d0d, 0x70e0561b320d06c]
def page172 : List Nat := [0x85cdcb0098443c7, 0x5f6106170321355, 0x30885e93480f2d4, 0x75181c541f6821, 0xa4210e9ac2c6d36, 0xa0f054385799cc0, 0x520221814edd81, 0xce1f869a5ff390e, 0x58642a123f30864, 0x7c3a0d07058343, 0x3e0c0a8d83c630f, 0x44c703ed91ac2c, 0xbd5e0f48ba10392, 0x761c09bce25100e, 0x70a0706eba0eae5, 0x8703b0808820325, 0x2b060881c0a174f, 0x588074381a8bc48, 0x85c9e157313b330, 0xd00c5585c340c0a, 0x688878341586c5d, 0xc64390146886191, 0x240c0581702150f, 0x50b95a8e55a2874]
def page173 : List Nat := [0x855dc1eab48c075, 0xdc1e6cbb0340c77, 0x61088018de7638d, 0x844203b0a8803c1, 0x32b40b8731a1c68, 0xa4844381409844, 0xd2a92140be7c15a, 0x3b017ae7b3b3a9c, 0x5363fde8f17cbdc, 0x74161c27084941, 0x5e0c0cb8c2217a8, 0x90e0442817caad4, 0x84d5820d082b454, 0x1b0a84a394a0e08, 0xd1c821a21c09856, 0x435346e0d056189, 0xf01d0a8403e160d, 0x5bd1b9601110878, 0x885d00c0b854437, 0x1c130b0568c1e0b, 0xc071681a580f0fc, 0xb002c1f2c9e8105, 0x413f0e14428171b, 0x30f3182c1a08820]
def page174 : List Nat := [0x8743ad4964b5aa7, 0x2a1c66822901e08, 0x42b87028028304c, 0xc5caa212a87e101, 0x301d0d0501d188a, 0x50cd8b466ea407a, 0x341941e08841a21, 0x3e1a07054be1e86, 0xe68880221c2e1c4, 0x442d903e4208a1, 0x43985a8bc152810, 0x9109f0242c0e854, 0x170320c6d1108cd, 0x6e1c22065a21f0d, 0x103814ec160ee11, 0xcda6b3b0a0842e1, 0x60994d9483e570b, 0xd0e08446060e085, 0x3d512380e0543e0, 0x88179bc0261d7a, 0x5004603b170e069, 0x4c3b1c0e0382c1, 0x268d27070460657, 0xc0fd805a4f0e864]
def page175 : List Nat := [0xa7438211bae51e1, 0x77374507c22142b, 0x43fb8d081c0a226, 0xaa0fa7c6ec842ee, 0x12160ab4c3c1d10, 0x651915d02409844, 0x9143c1c628fd444, 0x9cc60f87022b709, 0xe0d070339486878, 0x4b8ab2d2bc89261, 0x3a5c0a8641c1c0a, 0xc2d96892480f028, 0x7026890aa12998, 0x396a408460a1d83, 0x10b88c0c1d08a30, 0xbcf9086c368ae2, 0x22b85583418170d, 0xd5b8d16caa5404c, 0x81c0c050bdf82c1, 0x8c1e08872fa1106, 0x70301429590905d, 0x6582a21ac044140, 0x3d4910848180b03, 0x55a83a7d3f94520]
def page176 : List Nat := [0x2f9f81e7f914b72, 0x90172190882f87b, 0xe2ad09389a4287a, 0x64280da78709e4, 0x1c160d151940e06, 0xc0fc202adb0c834, 0x8381b490f3661b0, 0x510a84d00321308, 0x20fad418b75c38d, 0x708a892007dc23, 0xd024940444216ad, 0xb088b4268a0aa25, 0x855734990782e1, 0xae000b08428690e, 0xe0e154ac144ba58, 0x522f398c085940, 0x1aac0f870351389, 0x17b0f824fc63084, 0x8841a060e08588c, 0xbe1c0a054d07134, 0xe45074c61f08820, 0xc22150e2c0d01, 0xb85f0f0382c150a, 0xc10c94320e9355c]
def page177 : List Nat := [0x448280e88c402a5, 0x3a21112ce572e5a, 0xe0b99cf8190f348, 0x33da4202f171561, 0xfe190e04f00b359, 0xdcd064301c1a87a, 0x8203c150ecac260, 0x6a0e098467e9308, 0xc0a8d67c5b61a45, 0xc483d118786a281, 0x3d007fc05263419, 0x54bad1fa907c2f8, 0x85834c80e04d669, 0xcd26885432000b, 0x29426a4e9d08840, 0x8f474890f9b8412, 0x6551262cc9f1c40, 0x1548d83cc80e065, 0x87d503052864261, 0x404e10a110e860a, 0x42bb6c381e0c835, 0xbb3221308c30321, 0x3c0c2491c981c0a, 0x6098703ceb74928]
def page178 : List Nat := [0x8742c21c383710d, 0xea1d1f83026170a, 0xe2e074021783c11, 0xca832087103b381, 0x220c6433c381510, 0x60e8a4241674b30, 0x8442416098444e2, 0x3c21c28370cc70e, 0x60e068320e0697c, 0x74421005a5c3a9, 0x2e160a864b80e0f, 0xe0e856642109844, 0x72612f25124901, 0x3c1c0d2bc3c1160, 0x4374202adb10b14, 0xc85b8190f8361ae, 0x2a16712a0650a84, 0x70885832130885c, 0x702a20bb0e87a1, 0x22210ab44221006, 0x8bb850240c05814, 0x970421e0a876f37, 0x28150b9a03c1f0e, 0x40a87022082f870]
def page179 : List Nat := [0x55a21a09844681, 0x1c92100842c1169, 0x91ab886c1e5a8be, 0xb8ce2e4850c1b81, 0xdea73748440de0f, 0x65078221568868, 0x6a301516c5ce0d, 0x621c09acd0eb445, 0xd2487a1a4e0a865, 0x9f1472794292184, 0x261116074561c0a, 0x50984a3c1da7064, 0x72cc0d03016ce7, 0x2a0d0c5b06a190f, 0x22a66d1c142a871, 0x84c6a34198c01a1, 0x2a1c190c56a2e3c, 0xb02d8c2a211a878, 0x835a84e1083c180, 0x4810e8543e1d0c, 0x52d969081e08839, 0x87252177a0765af, 0x98210984562b40b, 0x1b2844161c68855]
def page180 : List Nat := [0x86c3c1122a24382, 0x221c74031c61708, 0x5cb865a41d90344, 0xa5190137a0752cf, 0xc05be0442c1d79, 0x54384c3815bd834, 0x446833412003c3, 0x808294489121f42, 0xc0581854200f854, 0x13abf5eae850240, 0x90c80ebc825527a, 0xf9d8502ef31d928, 0x38b9480f074c05, 0xe973088382c0a2f, 0xb539c1581111056, 0x1c6848e1004c22a, 0x369920115344639, 0x1050802c1560081, 0x702a205a8bc261, 0x592d508cc8e3506, 0x496ce65d3b0f282, 0x1243c154d13c381, 0x28ffc83fa209926, 0x7f4c7fe85ff54ff]
def page181 : List Nat := [0x10bf8a5fd53fe90, 0x3fe43ff53ffa07f, 0xaa9fc32ff10ffd4, 0x5fe41ff29ff50ff, 0xe54fea97f90ffe6, 0x2ffa1ff50bfc63f, 0xf98ff153fa65fe3, 0x87fd07fe61fd41f, 0xf503f883fc31ff8, 0x47f887fc53ff217, 0xf2c00100fea87fd, 0x89a685a29040012, 0x7122a081470e311, 0x300001000004, 0x3000014000080, 0x24000100000700, 0x180000b00005000, 0x600007000034000, 0x800068000320001, 0x3a0001c0000d, 0x2300011000080, 0x14000094000480, 0x410412001910300, 0x22110410880082]
def page182 : List Nat := [0x10c81886408432, 0xa8400522082910, 0x102048810115082, 0x10250080a80401, 0x48128240140206a, 0x40542200a090450, 0xa190350c81286, 0x550822a8401522, 0x482402212091090, 0x422072110090482, 0x190390c81486406, 0x824a8402512012, 0x413212019010395, 0x798102cc080e42, 0x1cc481662407302, 0x68040f40205a010, 0x42201a0904d0480, 0x1902d0c80e84413, 0x4826a240343207a, 0x354209aa100d4, 0x723316094321205, 0x635180b450240fc, 0x28d36954620cf87, 0xaecf63b0976b454]
def page183 : List Nat := [0x83bf9e8ec71b75, 0xd0e732d90c6a2b1, 0x4ca922212b955a5, 0xe549114e987032c, 0x634c9208381032, 0x71e38b130efc70c, 0xe24ed6d61808bd, 0x995244678d180a8, 0x8682064490e0a58, 0x5490e1608c13223, 0x4391071c3082326, 0x2238e8c045cf152, 0x1992c68b1528c83, 0x1626487022e5899, 0xb1986386060a122, 0xc38406381172644, 0x55b0e18dc593849, 0xe389851c08b9222, 0x3045a0c161c1351, 0x126c988d162980e, 0x8f1c4c90e1608c9, 0x70d04449381819c, 0xc2bc1a2c50e2264, 0x3018d3249f3d501]
def page184 : List Nat := [0x3058282389b31c, 0x1c6490e024c9118, 0x2a2388af1a30182, 0x172a4888d162a9d, 0x70e1a0011222381, 0x520c0e08ba52c4c, 0x1a40e2c4ca91241, 0x831716263c71524, 0x16284048f1a2915, 0xc0d38b132a4870e, 0x912438193224a68, 0x601384c7121c149, 0x468b140c718226c, 0x38a9228ad50708a, 0x2e8386180c1182e, 0x921c28e045cb132, 0xd16290a03e4471a, 0x90c142552a4898, 0x70b046019127507, 0xd1944688fc]
def storagePage (p : Nat) : List Nat := (if p < 92 then (if p < 46 then (if p < 23 then (if p < 11 then (if p < 5 then (if p < 2 then (if p < 1 then page0 else page1) else (if p < 3 then page2 else (if p < 4 then page3 else page4))) else (if p < 8 then (if p < 6 then page5 else (if p < 7 then page6 else page7)) else (if p < 9 then page8 else (if p < 10 then page9 else page10)))) else (if p < 17 then (if p < 14 then (if p < 12 then page11 else (if p < 13 then page12 else page13)) else (if p < 15 then page14 else (if p < 16 then page15 else page16))) else (if p < 20 then (if p < 18 then page17 else (if p < 19 then page18 else page19)) else (if p < 21 then page20 else (if p < 22 then page21 else page22))))) else (if p < 34 then (if p < 28 then (if p < 25 then (if p < 24 then page23 else page24) else (if p < 26 then page25 else (if p < 27 then page26 else page27))) else (if p < 31 then (if p < 29 then page28 else (if p < 30 then page29 else page30)) else (if p < 32 then page31 else (if p < 33 then page32 else page33)))) else (if p < 40 then (if p < 37 then (if p < 35 then page34 else (if p < 36 then page35 else page36)) else (if p < 38 then page37 else (if p < 39 then page38 else page39))) else (if p < 43 then (if p < 41 then page40 else (if p < 42 then page41 else page42)) else (if p < 44 then page43 else (if p < 45 then page44 else page45)))))) else (if p < 69 then (if p < 57 then (if p < 51 then (if p < 48 then (if p < 47 then page46 else page47) else (if p < 49 then page48 else (if p < 50 then page49 else page50))) else (if p < 54 then (if p < 52 then page51 else (if p < 53 then page52 else page53)) else (if p < 55 then page54 else (if p < 56 then page55 else page56)))) else (if p < 63 then (if p < 60 then (if p < 58 then page57 else (if p < 59 then page58 else page59)) else (if p < 61 then page60 else (if p < 62 then page61 else page62))) else (if p < 66 then (if p < 64 then page63 else (if p < 65 then page64 else page65)) else (if p < 67 then page66 else (if p < 68 then page67 else page68))))) else (if p < 80 then (if p < 74 then (if p < 71 then (if p < 70 then page69 else page70) else (if p < 72 then page71 else (if p < 73 then page72 else page73))) else (if p < 77 then (if p < 75 then page74 else (if p < 76 then page75 else page76)) else (if p < 78 then page77 else (if p < 79 then page78 else page79)))) else (if p < 86 then (if p < 83 then (if p < 81 then page80 else (if p < 82 then page81 else page82)) else (if p < 84 then page83 else (if p < 85 then page84 else page85))) else (if p < 89 then (if p < 87 then page86 else (if p < 88 then page87 else page88)) else (if p < 90 then page89 else (if p < 91 then page90 else page91))))))) else (if p < 138 then (if p < 115 then (if p < 103 then (if p < 97 then (if p < 94 then (if p < 93 then page92 else page93) else (if p < 95 then page94 else (if p < 96 then page95 else page96))) else (if p < 100 then (if p < 98 then page97 else (if p < 99 then page98 else page99)) else (if p < 101 then page100 else (if p < 102 then page101 else page102)))) else (if p < 109 then (if p < 106 then (if p < 104 then page103 else (if p < 105 then page104 else page105)) else (if p < 107 then page106 else (if p < 108 then page107 else page108))) else (if p < 112 then (if p < 110 then page109 else (if p < 111 then page110 else page111)) else (if p < 113 then page112 else (if p < 114 then page113 else page114))))) else (if p < 126 then (if p < 120 then (if p < 117 then (if p < 116 then page115 else page116) else (if p < 118 then page117 else (if p < 119 then page118 else page119))) else (if p < 123 then (if p < 121 then page120 else (if p < 122 then page121 else page122)) else (if p < 124 then page123 else (if p < 125 then page124 else page125)))) else (if p < 132 then (if p < 129 then (if p < 127 then page126 else (if p < 128 then page127 else page128)) else (if p < 130 then page129 else (if p < 131 then page130 else page131))) else (if p < 135 then (if p < 133 then page132 else (if p < 134 then page133 else page134)) else (if p < 136 then page135 else (if p < 137 then page136 else page137)))))) else (if p < 161 then (if p < 149 then (if p < 143 then (if p < 140 then (if p < 139 then page138 else page139) else (if p < 141 then page140 else (if p < 142 then page141 else page142))) else (if p < 146 then (if p < 144 then page143 else (if p < 145 then page144 else page145)) else (if p < 147 then page146 else (if p < 148 then page147 else page148)))) else (if p < 155 then (if p < 152 then (if p < 150 then page149 else (if p < 151 then page150 else page151)) else (if p < 153 then page152 else (if p < 154 then page153 else page154))) else (if p < 158 then (if p < 156 then page155 else (if p < 157 then page156 else page157)) else (if p < 159 then page158 else (if p < 160 then page159 else page160))))) else (if p < 173 then (if p < 167 then (if p < 164 then (if p < 162 then page161 else (if p < 163 then page162 else page163)) else (if p < 165 then page164 else (if p < 166 then page165 else page166))) else (if p < 170 then (if p < 168 then page167 else (if p < 169 then page168 else page169)) else (if p < 171 then page170 else (if p < 172 then page171 else page172)))) else (if p < 179 then (if p < 176 then (if p < 174 then page173 else (if p < 175 then page174 else page175)) else (if p < 177 then page176 else (if p < 178 then page177 else page178))) else (if p < 182 then (if p < 180 then page179 else (if p < 181 then page180 else page181)) else (if p < 183 then page182 else (if p < 184 then page183 else page184))))))))
def storageWord (i : Nat) := (storagePage (i / 24)).getD (i % 24) 0
def a0Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdf67df67df67df6, 0xf67df67df67df67, 0xf67df67d])
  | 2 => BitVec.ofNat 152 (big [0xedbbedbbedbbedb, 0xdbbedbbedbbedbb, 0xdbbedbbe])
  | 5 => BitVec.ofNat 152 (big [0x812281228122812, 0x122812281228122, 0x12281228])
  | _ => 0

def a0Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xa280a280a280a2, 0xa280a280a280a28, 0xa280a280])
  | 2 => BitVec.ofNat 152 (big [0x58405840584058, 0x584058405840584, 0x58405840])
  | 5 => BitVec.ofNat 152 (big [0xbfadbfadbfadbfa, 0xfadbfadbfadbfad, 0xfadbfadb])
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
def a0 : Atlas := ⟨3,rawDecor 37 a0Pos a0Neg,repeatWord 11574427655608138490,a0Count,a0Rec,(fun _ _ => 0),a0Loc⟩
def a0Domains : Catalog := []
def a1Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x687687687687687, 0x687687687687687, 0x87687687])
  | 3 => BitVec.ofNat 152 (big [0x978978978978978, 0x978978978978978, 0x78978978])
  | 5 => BitVec.ofNat 152 (big [0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff])
  | _ => 0

def a1Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xa55a55a55a55a55, 0xa55a55a55a55a55, 0x55a55a55])
  | 3 => BitVec.ofNat 152 (big [0x671671671671671, 0x671671671671671, 0x71671671])
  | 5 => BitVec.ofNat 152 (big [0x1b01b01b01b01b, 0x1b01b01b01b01b, 0x1b01b01b])
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
  | 2 => field storageWord (57+i*14) 14
  | 3 => field storageWord (117+i*3) 3
  | _ => 0

def a1Loc (k tag : Nat) : Nat :=
  match k with
  | 1 => hashRow 2 2 (field storageWord (53+(tag % 2)*2) 2) tag
  | 2 => hashRow 4 2 (field storageWord (113+(tag % 2)*2) 2) tag
  | 3 => 0
  | _ => 0

def a1Hints : Hints := fun _ _ => []
def a1 : Atlas := ⟨3,rawDecor 44 a1Pos a1Neg,repeatWord 1148435428446044160,a1Count,a1Rec,(fun _ _ => 0),a1Loc⟩
def a1Domains : Catalog := []
def a2Pos : Nat → Bits
  | 3 => BitVec.ofNat 152 (big [0xaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaa, 0xaaaaaaaa])
  | 4 => BitVec.ofNat 152 (big [0x555555555555555, 0x555555555555555, 0x55555555])
  | _ => 0

def a2Neg : Nat → Bits
  | 3 => BitVec.ofNat 152 (big [0xccccccccccccccc, 0xccccccccccccccc, 0xcccccccc])
  | 4 => BitVec.ofNat 152 (big [0xccccccccccccccc, 0xccccccccccccccc, 0xcccccccc])
  | _ => 0

def a2Count (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def a2Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (120+i*2) 2
  | _ => 0

def a2Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => 0
  | _ => 0

def a2Hints : Hints := fun _ _ => []
def a2 : Atlas := ⟨2,rawDecor 24 a2Pos a2Neg,repeatWord 72056494543077120,a2Count,a2Rec,(fun _ _ => 0),a2Loc⟩
def a2Domains : Catalog := []
def a3Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x2aa3c16dc0288f5, 0x551e0b6e01447ae, 0xa23d71])
  | 3 => BitVec.ofNat 152 (big [0x3d56048056d479a, 0xeab02402b6a3cd5, 0x5b51e6a9])
  | 4 => BitVec.ofNat 152 (big [0xff7b7b3eefff0be, 0xfbdbd9f77ff85f7, 0xbffc2fbf])
  | 5 => BitVec.ofNat 152 (big [0x7abe9ecf563efd1, 0xd5f4f67ab1f7e8f, 0x58fbf47b])
  | _ => 0

def a3Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xd646bf9de4641f7, 0xb235fcef2320fb9, 0x91907dce])
  | 3 => BitVec.ofNat 152 (big [0xde8ceb99ce643bb, 0xf4675cce7321dda, 0x3990eed6])
  | 4 => BitVec.ofNat 152 (big [0x4821800040a2, 0x2410c00020510, 0x102880])
  | 5 => BitVec.ofNat 152 (big [0xa5010900053ad11, 0x2808480029d6888, 0x14eb4445])
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
  | 3 => field storageWord (122+i*37) 37
  | 4 => field storageWord (203+i*26) 26
  | 5 => field storageWord (641+i*15) 15
  | 6 => field storageWord (813+i*4) 4
  | _ => 0

def a3Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 2 2 (field storageWord (196+(tag % 2)*1) 1) tag
  | 4 => hashRow 13 5 (field storageWord (541+(tag % 5)*4) 4) tag
  | 5 => hashRow 5 2 (field storageWord (716+(tag % 2)*2) 2) tag
  | 6 => 0
  | _ => 0

def a3Hints (k i : Nat) : List Nat :=
  match k with
  | 3 => hintsAt storageWord 199 1 202 1 198 1 i
  | 4 => hintsAt storageWord 569 4 625 2 561 2 i
  | 5 => hintsAt storageWord 735 5 765 3 720 3 i
  | 6 => hintsAt storageWord 826 2 830 2 817 3 i
  | _ => []

def a3 : Atlas := ⟨6,rawDecor 60 a3Pos a3Neg,repeatWord 18446480122467778560,a3Count,a3Rec,(fun _ _ => 0),a3Loc⟩
def a3Domains : Catalog := [(repeatWord 17361641481138401520, 4), (repeatWord 18374966859414961920, 4), (repeatWord 281470681808895, 4), (repeatWord 18446744069414584320, 4), (repeatWord 281470681743360, 3)]
def a4Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x15482a905520aa4, 0x15482a905520aa4, 0x5520aa4])
  | 3 => BitVec.ofNat 152 (big [0xd7cdaf9b5f36be6, 0xd7cdaf9b5f36be6, 0xb5f36be6])
  | 5 => BitVec.ofNat 152 (big [0x28325064a0c9419, 0x28325064a0c9419, 0x4a0c9419])
  | _ => 0

def a4Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xeb69d6d3ada75b4, 0xeb69d6d3ada75b4, 0x3ada75b4])
  | 3 => BitVec.ofNat 152 (big [0x26984d309a6134c, 0x26984d309a6134c, 0x9a6134c])
  | 5 => BitVec.ofNat 152 (big [0xa7b94f729ee53dc, 0xa7b94f729ee53dc, 0x29ee53dc])
  | _ => 0

def a4Count (k : Nat) : Nat :=
  match k with
  | 1 => 2
  | 2 => 4
  | 3 => 1
  | _ => 0

def a4Rec (k i : Nat) : Nat :=
  match k with
  | 1 => field storageWord (836+i*25) 25
  | 2 => field storageWord (890+i*14) 14
  | 3 => field storageWord (948+i*3) 3
  | _ => 0

def a4Loc (k tag : Nat) : Nat :=
  match k with
  | 1 => hashRow 2 2 (field storageWord (886+(tag % 2)*2) 2) tag
  | 2 => hashRow 4 2 (field storageWord (946+(tag % 2)*1) 1) tag
  | 3 => 0
  | _ => 0

def a4Hints : Hints := fun _ _ => []
def a4 : Atlas := ⟨3,rawDecor 44 a4Pos a4Neg,repeatWord 4222193353424640,a4Count,a4Rec,(fun _ _ => 0),a4Loc⟩
def a4Domains : Catalog := []
def a5Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xf5eef5eef5eef5e, 0x5eef5eef5eef5ee, 0x5eef5eef])
  | 4 => BitVec.ofNat 152 (big [0x8e398e398e398e3, 0xe398e398e398e39, 0xe398e398])
  | 5 => BitVec.ofNat 152 (big [0x114211421142114, 0x142114211421142, 0x14211421])
  | _ => 0

def a5Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x292029202920292, 0x920292029202920, 0x92029202])
  | 4 => BitVec.ofNat 152 (big [0xbb24bb24bb24bb2, 0xb24bb24bb24bb24, 0xb24bb24b])
  | 5 => BitVec.ofNat 152 (big [0xfb6dfb6dfb6dfb6, 0xb6dfb6dfb6dfb6d, 0xb6dfb6df])
  | _ => 0

def a5Count (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0

def a5Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (951+i*3) 3
  | _ => 0

def a5Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => 0
  | _ => 0

def a5Hints : Hints := fun _ _ => []
def a5 : Atlas := ⟨2,rawDecor 52 a5Pos a5Neg,repeatWord 264917877780720,a5Count,a5Rec,(fun _ _ => 0),a5Loc⟩
def a5Domains : Catalog := []
def a6Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xffddbd8be77fa07, 0xffddbd8be77fa07, 0xbe77fa07])
  | 3 => BitVec.ofNat 152 (big [0x226194c87114f83, 0x226194c87114f83, 0x87114f83])
  | 4 => BitVec.ofNat 152 (big [0x3d82773f88c287a, 0x3d82773f88c287a, 0xf88c287a])
  | 5 => BitVec.ofNat 152 (big [0xb1fb5dc8d9d8dae, 0xb1fb5dc8d9d8dae, 0x8d9d8dae])
  | _ => 0

def a6Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x3040108502a00, 0x3040108502a00, 0x8502a00])
  | 3 => BitVec.ofNat 152 (big [0xdebf5a7acf56f33, 0xdebf5a7acf56f33, 0xacf56f33])
  | 4 => BitVec.ofNat 152 (big [0xc6b54a5acd46e32, 0xc6b54a5acd46e32, 0xacd46e32])
  | 5 => BitVec.ofNat 152 (big [0x4600af8440604ae, 0x4600af8440604ae, 0x440604ae])
  | _ => 0

def a6Count (k : Nat) : Nat :=
  match k with
  | 2 => 2
  | 3 => 12
  | 4 => 27
  | 5 => 10
  | 6 => 1
  | _ => 0

def a6Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (954+i*48) 48
  | 3 => field storageWord (1054+i*37) 37
  | 4 => field storageWord (1546+i*26) 26
  | 5 => field storageWord (3127+i*15) 15
  | 6 => field storageWord (3589+i*4) 4
  | _ => 0

def a6Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => hashRow 2 2 (field storageWord (1050+(tag % 2)*2) 2) tag
  | 3 => hashRow 12 12 (field storageWord (1498+(tag % 12)*4) 4) tag
  | 4 => hashRow 27 54 (field storageWord (2248+(tag % 54)*6) 6) tag
  | 5 => hashRow 10 5 (field storageWord (3277+(tag % 5)*5) 5) tag
  | 6 => 0
  | _ => 0

def a6Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2803 6 2971 4 2572 21 i
  | 5 => hintsAt storageWord 3421 6 3487 3 3302 17 i
  | 6 => hintsAt storageWord 3599 2 3603 1 3593 3 i
  | _ => []

def a6 : Atlas := ⟨6,rawDecor 60 a6Pos a6Neg,repeatWord 17365880094437929200,a6Count,a6Rec,(fun _ _ => 0),a6Loc⟩
def a6Domains : Catalog := [(repeatWord 1085102592571150095, 4), (repeatWord 18374966859414961920, 4), (repeatWord 18446744069414584320, 4), (repeatWord 17298308644996116495, 4), (repeatWord 281474976645120, 4), (repeatWord 4294967295, 3), (repeatWord 1085102592318504960, 3)]
def a7Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x38eb5febe70e9f8, 0x8eb5febe70e9f8e, 0x70e9f8e3])
  | 3 => BitVec.ofNat 152 (big [0x5353fececfe1b33, 0x353fececfe1b33b, 0xfe1b33b5])
  | 4 => BitVec.ofNat 152 (big [0xd7e765739f99fa4, 0x7e765739f99fa4c, 0xf99fa4cd])
  | 5 => BitVec.ofNat 152 (big [0x100004420400920, 0x44204009200, 0x40092001])
  | _ => 0

def a7Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xc602b108a65a8f0, 0x602b108a65a8f01, 0x65a8f01c])
  | 3 => BitVec.ofNat 152 (big [0xa8c42312e1e0b11, 0x8c42312e1e0b114, 0x1e0b114a])
  | 4 => BitVec.ofNat 152 (big [0x2299125103337a0, 0x299125103337a03, 0x3337a032])
  | 5 => BitVec.ofNat 152 (big [0xefffbf5ff7ffff1, 0xfffbf5ff7ffff1f, 0x7ffff1fe])
  | _ => 0

def a7Count (k : Nat) : Nat :=
  match k with
  | 4 => 12
  | 5 => 1
  | _ => 0

def a7Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (3605+i*15) 15
  | 5 => field storageWord (3902+i*4) 4
  | _ => 0

def a7Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 12 12 (field storageWord (3785+(tag % 12)*5) 5) tag
  | 5 => 0
  | _ => 0

def a7Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 3851 3 3890 2 3845 2 i
  | 5 => hintsAt storageWord 3924 3 3930 3 3906 3 i
  | _ => []

def a7 : Atlas := ⟨5,rawDecor 60 a7Pos a7Neg,repeatWord 17293822573397671920,a7Count,a7Rec,(fun _ _ => 0),a7Loc⟩
def a7Domains : Catalog := [(repeatWord 17298308644996116495, 4), (repeatWord 17361393124654452495, 4), (repeatWord 17361641477348724495, 4), (repeatWord 18374687579166474495, 4), (repeatWord 18374966855153418495, 4), (repeatWord 18446462598732906495, 4)]
def a8Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x7601d66269f04ce, 0x33b00eb3134f826, 0x5989a7c1])
  | 3 => BitVec.ofNat 152 (big [0x4f7fd1de85e7d49, 0x527bfe8ef42f3ea, 0x477a179f])
  | 4 => BitVec.ofNat 152 (big [0xa79f3ee537ce674, 0x9d3cf9f729be733, 0xfb94df39])
  | 5 => BitVec.ofNat 152 (big [0x8a0a3109848e751, 0xd45051884c2473a, 0xc4261239])
  | _ => 0

def a8Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0xe9edab91e3f64dd, 0x374f6d5c8f1fb26, 0xae478fd9])
  | 3 => BitVec.ofNat 152 (big [0x488422104102409, 0x24421108208120, 0x88410409])
  | 4 => BitVec.ofNat 152 (big [0xa04081800254054, 0x1502040c0012a02, 0x6000950])
  | 5 => BitVec.ofNat 152 (big [0xedfdff91fff77dd, 0xf76feffc8fffbbe, 0xfe47ffdd])
  | _ => 0

def a8Count (k : Nat) : Nat :=
  match k with
  | 2 => 2
  | 3 => 6
  | 4 => 6
  | 5 => 1
  | _ => 0

def a8Rec (k i : Nat) : Nat :=
  match k with
  | 2 => field storageWord (3948+i*37) 37
  | 3 => field storageWord (4024+i*26) 26
  | 4 => field storageWord (4204+i*15) 15
  | 5 => field storageWord (4370+i*4) 4
  | _ => 0

def a8Loc (k tag : Nat) : Nat :=
  match k with
  | 2 => hashRow 2 2 (field storageWord (4022+(tag % 2)*1) 1) tag
  | 3 => hashRow 6 6 (field storageWord (4180+(tag % 6)*4) 4) tag
  | 4 => hashRow 6 6 (field storageWord (4294+(tag % 6)*4) 4) tag
  | 5 => 0
  | _ => 0

def a8Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 4326 4 4354 2 4318 2 i
  | 5 => hintsAt storageWord 4380 2 4384 2 4374 2 i
  | _ => []

def a8 : Atlas := ⟨5,rawDecor 60 a8Pos a8Neg,repeatWord 18378925101291667440,a8Count,a8Rec,(fun _ _ => 0),a8Loc⟩
def a8Domains : Catalog := [(repeatWord 18446744069414584320, 4), (repeatWord 17361641477348724495, 4), (repeatWord 71777214294589695, 3), (repeatWord 281470681808895, 3)]
def a9Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xffd7ffeffbfe7f6, 0xfd7ffeffbfe7f6f, 0xbfe7f6ff])
  | 2 => BitVec.ofNat 152 (big [0xd4c54f07ba7c2d4, 0x4c54f07ba7c2d42, 0xa7c2d42d])
  | 4 => BitVec.ofNat 152 (big [0xeaaf9eb0ddf38bb, 0xaaf9eb0ddf38bbc, 0xdf38bbce])
  | 5 => BitVec.ofNat 152 (big [0x5ec012065ad0076, 0xec012065ad00768, 0xad007685])
  | _ => 0

def a9Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x804000114424, 0x8040001144240, 0x11442400])
  | 2 => BitVec.ofNat 152 (big [0x3ba6609b92e92d1, 0xba6609b92e92d1d, 0x2e92d1d3])
  | 4 => BitVec.ofNat 152 (big [0x1c1360919a82893, 0xc1360919a828933, 0xa8289331])
  | 5 => BitVec.ofNat 152 (big [0x873fc754cfdec76, 0x73fc754cfdec767, 0xfdec7678])
  | _ => 0

def a9Count (k : Nat) : Nat :=
  match k with
  | 3 => 15
  | 4 => 12
  | 5 => 1
  | _ => 0

def a9Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (4390+i*26) 26
  | 4 => field storageWord (4855+i*15) 15
  | 5 => field storageWord (5105+i*4) 4
  | _ => 0

def a9Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 15 15 (field storageWord (4780+(tag % 15)*5) 5) tag
  | 4 => hashRow 12 6 (field storageWord (5035+(tag % 6)*4) 4) tag
  | 5 => 0
  | _ => 0

def a9Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 5060 3 5099 1 5059 1 i
  | 5 => hintsAt storageWord 5110 1 5112 1 5109 1 i
  | _ => []

def a9 : Atlas := ⟨5,rawDecor 53 a9Pos a9Neg,repeatWord 12297818344491297450,a9Count,a9Rec,(fun _ _ => 0),a9Loc⟩
def a9Domains : Catalog := [(repeatWord 1085102592571150095, 4)]
def a10Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf57bddfca9fd676, 0xf57bddfca9fd676, 0xca9fd676])
  | 2 => BitVec.ofNat 152 (big [0x6e579e6ee6cb70b, 0x6e579e6ee6cb70b, 0xee6cb70b])
  | 4 => BitVec.ofNat 152 (big [0x3ccafbbb1577cb8, 0x3ccafbbb1577cb8, 0xb1577cb8])
  | 5 => BitVec.ofNat 152 (big [0x4010dac0078632, 0x4010dac0078632, 0xc0078632])
  | _ => 0

def a10Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x804a0008044016, 0x804a0008044016, 0x8044016])
  | 2 => BitVec.ofNat 152 (big [0x91d8012506a1609, 0x91d8012506a1609, 0x506a1609])
  | 4 => BitVec.ofNat 152 (big [0xc23b001f0221c28, 0xc23b001f0221c28, 0xf0221c28])
  | 5 => BitVec.ofNat 152 (big [0xfbffeb7fdefde3f, 0xfbffeb7fdefde3f, 0xfdefde3f])
  | _ => 0

def a10Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a10Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (5113+i*4) 4
  | _ => 0

def a10Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a10Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 5118 1 5120 1 5117 1 i
  | _ => []

def a10 : Atlas := ⟨4,rawDecor 53 a10Pos a10Neg,repeatWord 12297818345838738170,a10Count,a10Rec,(fun _ _ => 0),a10Loc⟩
def a10Domains : Catalog := [(repeatWord 1085102592571150095, 4)]
def a11Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xa284050c8044a28, 0x44a284050c8044, 0x284050c8])
  | 2 => BitVec.ofNat 152 (big [0x1684803090a016, 0x90a01684803090a, 0x16848030])
  | 3 => BitVec.ofNat 152 (big [0x141212303600141, 0x600141212303600, 0x41212303])
  | 5 => BitVec.ofNat 152 (big [0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff])
  | _ => 0

def a11Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xf2ab7aea9536f2a, 0x536f2ab7aea9536, 0x2ab7aea9])
  | 2 => BitVec.ofNat 152 (big [0x45e7c6fcc70f45e, 0x70f45e7c6fcc70f, 0x5e7c6fcc])
  | 3 => BitVec.ofNat 152 (big [0x965de9ad16af965, 0x6af965de9ad16af, 0x65de9ad1])
  | 5 => BitVec.ofNat 152 (big [0x56e00a84042756e, 0x42756e00a840427, 0x6e00a840])
  | _ => 0

def a11Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a11Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (5121+i*4) 4
  | _ => 0

def a11Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a11Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 5126 1 5128 1 5125 1 i
  | _ => []

def a11 : Atlas := ⟨4,rawDecor 46 a11Pos a11Neg,repeatWord 233909274764378112,a11Count,a11Rec,(fun _ _ => 0),a11Loc⟩
def a11Domains : Catalog := [(repeatWord 18446744069414584320, 4)]
def a12Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdf5fff3fb7ffb77, 0xdf5fff3fb7ffb77, 0xfb7ffb77])
  | 2 => BitVec.ofNat 152 (big [0x1c1b763c16b6b46, 0x1c1b763c16b6b46, 0xc16b6b46])
  | 3 => BitVec.ofNat 152 (big [0xf7edffeffdebcbf, 0xf7edffeffdebcbf, 0xffdebcbf])
  | 5 => BitVec.ofNat 152 (big [0xb9bbcbf45bddfe8, 0xb9bbcbf45bddfe8, 0x45bddfe8])
  | _ => 0

def a12Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x20810c71808a172, 0x20810c71808a172, 0x1808a172])
  | 2 => BitVec.ofNat 152 (big [0xe17c19a6d664a4e, 0xe17c19a6d664a4e, 0x6d664a4e])
  | 3 => BitVec.ofNat 152 (big [0x914408e006588d, 0x914408e006588d, 0xe006588d])
  | 5 => BitVec.ofNat 152 (big [0x4604174151f4f28, 0x4604174151f4f28, 0x151f4f28])
  | _ => 0

def a12Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a12Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (5129+i*4) 4
  | _ => 0

def a12Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a12Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 5134 1 5136 1 5133 1 i
  | _ => []

def a12 : Atlas := ⟨4,rawDecor 45 a12Pos a12Neg,repeatWord 12655308057492892160,a12Count,a12Rec,(fun _ _ => 0),a12Loc⟩
def a12Domains : Catalog := [(repeatWord 18446744069414584320, 3)]
def a13Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xbfbffb7fffd71ff, 0xfdffdbfffeb8fff, 0xff5c7ffd])
  | 1 => BitVec.ofNat 152 (big [0xdeec35f4b529ec5, 0xf761afa5a94f629, 0xd4a7b14e])
  | 4 => BitVec.ofNat 152 (big [0xefd0fffe6d7ae37, 0x7e87fff36bd71bd, 0xb5eb8def])
  | 5 => BitVec.ofNat 152 (big [0x8810191e4402027, 0x4080c8f2201013c, 0x100809e4])
  | _ => 0

def a13Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x44408028049108e, 0x220401402488470, 0x12442382])
  | 1 => BitVec.ofNat 152 (big [0x2b5ac06e13a06c5, 0x5ad603709d0362e, 0x4e81b171])
  | 4 => BitVec.ofNat 152 (big [0x102970d32042a31, 0x814b8699021518a, 0x810a8c50])
  | 5 => BitVec.ofNat 152 (big [0x765fe7fe54f52af, 0xb2ff3ff2a7a957b, 0x53d4abdb])
  | _ => 0

def a13Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a13Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (5137+i*4) 4
  | _ => 0

def a13Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a13Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 5142 1 5144 1 5141 1 i
  | _ => []

def a13 : Atlas := ⟨4,rawDecor 51 a13Pos a13Neg,repeatWord 12297641736497179306,a13Count,a13Rec,(fun _ _ => 0),a13Loc⟩
def a13Domains : Catalog := [(repeatWord 14757395258967641292, 4)]
def a14Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf6ff7dbe6df7a7e, 0xb7fbedf36fbd3f7, 0xb7de9fbf])
  | 2 => BitVec.ofNat 152 (big [0xeb97de7bf6e87a3, 0x5cbef3dfb743d1e, 0xdba1e8f7])
  | 3 => BitVec.ofNat 152 (big [0xd553ef8b28beec8, 0xaa9f7c5945f7641, 0xa2fbb20e])
  | 4 => BitVec.ofNat 152 (big [0x94aa58942dd323c, 0xa552c4a16e991e2, 0xb74c8f14])
  | _ => 0

def a14Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x10200928000052, 0x81004940000290, 0x1480])
  | 2 => BitVec.ofNat 152 (big [0x3009206528602a1, 0x804903294301509, 0xa180a849])
  | 3 => BitVec.ofNat 152 (big [0x28ac664819f4e88, 0x45633240cfa7446, 0x67d3a231])
  | 4 => BitVec.ofNat 152 (big [0x7ac9ae652fe62ad, 0xd64d73297f3156d, 0xbf98ab6b])
  | _ => 0

def a14Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a14Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (5145+i*4) 4
  | _ => 0

def a14Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a14Hints : Hints := fun _ _ => []
def a14 : Atlas := ⟨3,rawDecor 29 a14Pos a14Neg,repeatWord 12297917644050987760,a14Count,a14Rec,(fun _ _ => 0),a14Loc⟩
def a14Domains : Catalog := []
def a15Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x9fff9beff0f5bf1, 0xfff9beff0f5bf1f, 0xf5bf1f9])
  | 2 => BitVec.ofNat 152 (big [0xf9deffb95fbb59f, 0x9deffb95fbb59fe, 0xfbb59fef])
  | 3 => BitVec.ofNat 152 (big [0x7ef1d17fa8cdf64, 0xef1d17fa8cdf647, 0x8cdf6477])
  | 5 => BitVec.ofNat 152 (big [0x88ad114d60349d0, 0x8ad114d60349d04, 0x349d048])
  | _ => 0

def a15Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x5800608a00a62c1, 0x800608a00a62c10, 0xa62c105])
  | 2 => BitVec.ofNat 152 (big [0x2018b604108512, 0x2018b6041085121, 0x10851210])
  | 3 => BitVec.ofNat 152 (big [0x821a1c65cd01d24, 0x21a1c65cd01d248, 0xd01d2488])
  | 5 => BitVec.ofNat 152 (big [0x7799afebeb18dd2, 0x799afebeb18dd2b, 0xb18dd2b7])
  | _ => 0

def a15Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def a15Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (5149+i*4) 4
  | _ => 0

def a15Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | _ => 0

def a15Hints : Hints := fun _ _ => []
def a15 : Atlas := ⟨3,rawDecor 45 a15Pos a15Neg,repeatWord 12295014591103040240,a15Count,a15Rec,(fun _ _ => 0),a15Loc⟩
def a15Domains : Catalog := []
def a16Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xdd9d054905e9ba7, 0xefbfffdaf7fafbe, 0xbcf91bdf])
  | 2 => BitVec.ofNat 152 (big [0xb3f2eb51799e235, 0x87ff7701eeda5eb, 0x7dfbec8e])
  | 3 => BitVec.ofNat 152 (big [0x99f505080c19bb6, 0x2f96deda98c22ac, 0x50493b0a])
  | 4 => BitVec.ofNat 152 (big [0xd76efea7be70f58, 0x7b047aeed965d54, 0xcff6fefd])
  | 5 => BitVec.ofNat 152 (big [0x287f699c48575d7, 0xbeece71f9f71661, 0x590e315f])
  | _ => 0

def a16Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xa49d000580e9803, 0x88504c480208412, 0x240c81])
  | 2 => BitVec.ofNat 152 (big [0x1802c1607904234, 0x74212120c8d01cd, 0x12c03108])
  | 3 => BitVec.ofNat 152 (big [0xdf66f5da1c1dfbc, 0xe72f77a298633af, 0x8febd37b])
  | 4 => BitVec.ofNat 152 (big [0x432230881c10708, 0x450722a0106010c, 0x8c0a9040])
  | 5 => BitVec.ofNat 152 (big [0x2850781c00565d7, 0x23980b9a852d4b0, 0xe94982b4])
  | _ => 0

def a16Count (k : Nat) : Nat :=
  match k with
  | 4 => 5
  | 5 => 127
  | 6 => 132
  | 7 => 21
  | 8 => 1
  | _ => 0

def a16Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (5153+i*49) 49
  | 5 => field storageWord (5502+i*38) 38
  | 6 => field storageWord (13750+i*27) 27
  | 7 => field storageWord (27492+i*16) 16
  | 8 => field storageWord (29918+i*5) 5
  | _ => 0

def a16Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 5 3 (field storageWord (5398+(tag % 3)*2) 2) tag
  | 5 => hashRow 127 64 (field storageWord (10328+(tag % 64)*8) 8) tag
  | 6 => hashRow 132 132 (field storageWord (17314+(tag % 132)*9) 9) tag
  | 7 => hashRow 21 7 (field storageWord (27828+(tag % 7)*6) 6) tag
  | 8 => 0
  | _ => 0

def a16Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 5488 2 5500 1 5404 42 i
  | 5 => hintsAt storageWord 12380 7 13276 6 10840 44 i
  | 6 => hintsAt storageWord 22165 10 23495 7 18502 33 i
  | 7 => hintsAt storageWord 28962 8 29138 6 27870 21 i
  | 8 => hintsAt storageWord 29931 3 29937 2 29923 2 i
  | _ => []

def a16 : Atlas := ⟨8,rawDecor 62 a16Pos a16Neg,repeatWord 18230515151222587584,a16Count,a16Rec,(fun _ _ => 0),a16Loc⟩
def a16Domains : Catalog := [(repeatWord 4340410370284600380, 7), (repeatWord 3689517697150995660, 7), (repeatWord 18374966859414961920, 6), (repeatWord 18446744069414584320, 6), (repeatWord 17361393124654452495, 6), (repeatWord 3689348814741910323, 5), (repeatWord 17361641481138401520, 5), (repeatWord 281470681808895, 5), (repeatWord 14714328930390887475, 5), (repeatWord 1148435428713435120, 5), (repeatWord 18446462598732906495, 5), (repeatWord 1085102592571150095, 4), (repeatWord 4294967295, 4), (repeatWord 3472328296227680304, 4), (repeatWord 3689348813882916864, 4), (repeatWord 1085102592318504960, 3), (repeatWord 281470681743360, 3)]
def a17Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x6faf5dffa7fe770, 0x37ffedfc9b37fe9, 0x3775f5ff])
  | 2 => BitVec.ofNat 152 (big [0xaecf141ae2fa449, 0x372d31b5a1113e1, 0x1c30f899])
  | 3 => BitVec.ofNat 152 (big [0xfc71b751796399f, 0xcd76bf377fee93f, 0xefde9bd3])
  | 4 => BitVec.ofNat 152 (big [0xdfeecbb4d4d5a6b, 0x7ea75b5bb6d1e32, 0xdfd6fa5])
  | 5 => BitVec.ofNat 152 (big [0x9656beebce0a4ff, 0xa1cb99e76a5a8e6, 0xd9363edc])
  | _ => 0

def a17Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x800508087a4410, 0x1000208c123a209, 0x81500490])
  | 2 => BitVec.ofNat 152 (big [0xfcceec56e0fac4d, 0x6cb8c93701851fc, 0x60b7fe07])
  | 3 => BitVec.ofNat 152 (big [0x74e1a241384290d, 0x641889300084180, 0x4230002])
  | 4 => BitVec.ofNat 152 (big [0xe68289164051a63, 0xa0040a42e001c32, 0x18871047])
  | 5 => BitVec.ofNat 152 (big [0x12041c6a460a0fe, 0x5593330b6a79da4, 0x12ecd2e1])
  | _ => 0

def a17Count (k : Nat) : Nat :=
  match k with
  | 5 => 108
  | 6 => 121
  | 7 => 30
  | 8 => 1
  | _ => 0

def a17Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (29945+i*38) 38
  | 6 => field storageWord (37868+i*27) 27
  | 7 => field storageWord (49749+i*16) 16
  | 8 => field storageWord (52472+i*5) 5
  | _ => 0

def a17Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 108 216 (field storageWord (34049+(tag % 216)*8) 8) tag
  | 6 => hashRow 121 61 (field storageWord (41135+(tag % 61)*8) 8) tag
  | 7 => hashRow 30 15 (field storageWord (50229+(tag % 15)*6) 6) tag
  | 8 => 0
  | _ => 0

def a17Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 36635 7 37398 5 35777 33 i
  | 6 => hintsAt storageWord 44791 10 46011 7 41623 33 i
  | 7 => hintsAt storageWord 51138 8 51386 6 50319 21 i
  | 8 => hintsAt storageWord 52479 2 52483 1 52477 1 i
  | _ => []

def a17 : Atlas := ⟨8,rawDecor 61 a17Pos a17Neg,repeatWord 18422730330389260800,a17Count,a17Rec,(fun _ _ => 0),a17Loc⟩
def a17Domains : Catalog := [(repeatWord 6172840429334713770, 7), (repeatWord 17361641481138401520, 6), (repeatWord 6149008514797120170, 6), (repeatWord 12297829381041378645, 6), (repeatWord 18374687579166474495, 6), (repeatWord 71777218556133120, 6), (repeatWord 6148914691236517205, 5), (repeatWord 1085102592571150095, 5), (repeatWord 18374966859414961920, 5), (repeatWord 281470681808895, 5), (repeatWord 4294967295, 5), (repeatWord 18446744069414584320, 5), (repeatWord 6124988953138320640, 4), (repeatWord 252645135, 4), (repeatWord 281470681743360, 3)]
def a18Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x55074bf6ff3226a, 0xff7793fdfcf1e7f, 0xf6fe7a27])
  | 2 => BitVec.ofNat 152 (big [0xbef4f87949d9ce5, 0x27fdfddb9f27bb0, 0xefadd5fb])
  | 3 => BitVec.ofNat 152 (big [0x366b5f43869539f, 0xd3afa76a23f93cb, 0x995ce4a6])
  | 4 => BitVec.ofNat 152 (big [0x439f56dfb1ae791, 0xfdf75b6fc708d86, 0x451aaedc])
  | 5 => BitVec.ofNat 152 (big [0x450049729b922a9, 0xf7d281bf775102c, 0xa0c80086])
  | _ => 0

def a18Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x400188905420068, 0x4023a7000e0800, 0x120])
  | 2 => BitVec.ofNat 152 (big [0x298440400958085, 0x3b0d400015053b8, 0x11240005])
  | 3 => BitVec.ofNat 152 (big [0x142a32418295307, 0x7021c50a201432d, 0x1280aa9b])
  | 4 => BitVec.ofNat 152 (big [0x8b04420f218e690, 0xa4c8409f208086, 0x2c39160c])
  | 5 => BitVec.ofNat 152 (big [0x2dac4bffdbde2ad, 0xbb9dd72f378f3bd, 0xb5bfa76d])
  | _ => 0

def a18Count (k : Nat) : Nat :=
  match k with
  | 4 => 23
  | 5 => 146
  | 6 => 158
  | 7 => 34
  | 8 => 1
  | _ => 0

def a18Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (52485+i*49) 49
  | 5 => field storageWord (53838+i*38) 38
  | 6 => field storageWord (63507+i*27) 27
  | 7 => field storageWord (77574+i*16) 16
  | 8 => field storageWord (80041+i*5) 5
  | _ => 0

def a18Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 23 8 (field storageWord (53612+(tag % 8)*6) 6) tag
  | 5 => hashRow 146 73 (field storageWord (59386+(tag % 73)*9) 9) tag
  | 6 => hashRow 158 158 (field storageWord (67773+(tag % 158)*9) 9) tag
  | 7 => hashRow 34 34 (field storageWord (78118+(tag % 34)*6) 6) tag
  | 8 => 0
  | _ => 0

def a18Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 53756 3 53828 2 53660 32 i
  | 5 => hintsAt storageWord 61437 8 62613 6 60043 34 i
  | 6 => hintsAt storageWord 71406 10 72996 7 69195 33 i
  | 7 => hintsAt storageWord 78931 8 79211 5 78322 21 i
  | 8 => hintsAt storageWord 80047 1 80049 1 80046 1 i
  | _ => []

def a18 : Atlas := ⟨8,rawDecor 61 a18Pos a18Neg,repeatWord 18062436863988923120,a18Count,a18Rec,(fun _ _ => 0),a18Loc⟩
def a18Domains : Catalog := [(repeatWord 18446744069414584320, 6), (repeatWord 6510615555426900570, 6), (repeatWord 6148914692668172970, 6), (repeatWord 6148914691236517205, 5), (repeatWord 1085102592571150095, 5), (repeatWord 18374966859414961920, 5), (repeatWord 18446462603027742720, 5), (repeatWord 4294967295, 5), (repeatWord 17298308644996116495, 5), (repeatWord 17361393124654452495, 5), (repeatWord 18374687579166474495, 5), (repeatWord 71777214294589695, 4), (repeatWord 281470681808895, 4), (repeatWord 6124988953138320640, 4), (repeatWord 6148820867675914240, 4), (repeatWord 252645135, 4)]
def a19Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x7effd7ffff6fdfe, 0xffffffffffbfff7, 0xf7fcffef])
  | 2 => BitVec.ofNat 152 (big [0xeffdbebd2ff0a7b, 0x5ff77e3f70f6eef, 0xefd7bbb7])
  | 3 => BitVec.ofNat 152 (big [0xbd93ed57d59f7b5, 0xe1fdb5f6dffd138, 0xba6bc5d8])
  | 4 => BitVec.ofNat 152 (big [0xa9ba6af1c4ddb4d, 0xb0b7edc50f5c3fb, 0x3d1b0eb2])
  | 5 => BitVec.ofNat 152 (big [0xb735fbb790b6fd3, 0x97ad4c50ba4b23c, 0x6b6bd4da])
  | _ => 0

def a19Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x12914260f94ad06, 0x402403351822c40, 0x41420a08])
  | 2 => BitVec.ofNat 152 (big [0xac4c0c9c06b0278, 0x82c8a80ae4042ad, 0x209445a6])
  | 3 => BitVec.ofNat 152 (big [0xa148a51585172b5, 0x2138cc04f795510, 0xe0adb620])
  | 4 => BitVec.ofNat 152 (big [0x1bba01b164dd949, 0x829146794f5802f, 0x9c26810d])
  | 5 => BitVec.ofNat 152 (big [0x3631ff0b40a4fd3, 0xf8554b11a148a35, 0x1692dc94])
  | _ => 0

def a19Count (k : Nat) : Nat :=
  match k with
  | 3 => 2
  | 4 => 22
  | 5 => 50
  | 6 => 12
  | 7 => 1
  | _ => 0

def a19Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (80050+i*49) 49
  | 4 => field storageWord (80150+i*38) 38
  | 5 => field storageWord (81034+i*27) 27
  | 6 => field storageWord (83589+i*16) 16
  | 7 => field storageWord (84559+i*5) 5
  | _ => 0

def a19Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 2 2 (field storageWord (80148+(tag % 2)*1) 1) tag
  | 4 => hashRow 22 8 (field storageWord (80986+(tag % 8)*6) 6) tag
  | 5 => hashRow 50 25 (field storageWord (82384+(tag % 25)*7) 7) tag
  | 6 => hashRow 12 6 (field storageWord (83781+(tag % 6)*5) 5) tag
  | 7 => 0
  | _ => 0

def a19Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 83087 6 83393 4 82559 33 i
  | 6 => hintsAt storageWord 84231 6 84309 5 83811 21 i
  | 7 => hintsAt storageWord 84572 2 84576 1 84564 4 i
  | _ => []

def a19 : Atlas := ⟨7,rawDecor 62 a19Pos a19Neg,repeatWord 18212782021527257280,a19Count,a19Rec,(fun _ _ => 0),a19Loc⟩
def a19Domains : Catalog := [(repeatWord 18374966859414961920, 6), (repeatWord 18446462603027742720, 5), (repeatWord 18446744069414584320, 5), (repeatWord 4340410370284600380, 5), (repeatWord 3689517697150995660, 5), (repeatWord 3689348817318890700, 5), (repeatWord 17361393124654452495, 5), (repeatWord 17361641477348724495, 5), (repeatWord 18446462598732840960, 4)]
def a20Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xd477a21d477a21d, 0x1d477a21d477a21, 0x21d477a2])
  | 3 => BitVec.ofNat 152 (big [0xa7614d3a7614d3a, 0x3a7614d3a7614d3, 0xd3a7614d])
  | 4 => BitVec.ofNat 152 (big [0xfd57a90fd57a90, 0x90fd57a90fd57a9, 0xa90fd57a])
  | 5 => BitVec.ofNat 152 (big [0x8f3f9548f3f9548, 0x48f3f9548f3f954, 0x548f3f95])
  | _ => 0

def a20Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xb98d8b1b98d8b1b, 0x1b98d8b1b98d8b1, 0xb1b98d8b])
  | 3 => BitVec.ofNat 152 (big [0xb98d8b1b98d8b1b, 0x1b98d8b1b98d8b1, 0xb1b98d8b])
  | 4 => BitVec.ofNat 152 (big [0x0])
  | 5 => BitVec.ofNat 152 (big [0x0])
  | _ => 0

def a20Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a20Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (84578+i*4) 4
  | _ => 0

def a20Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a20Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 84583 1 84585 1 84582 1 i
  | _ => []

def a20 : Atlas := ⟨4,rawDecor 58 a20Pos a20Neg,repeatWord 18446744073709499340,a20Count,a20Rec,(fun _ _ => 0),a20Loc⟩
def a20Domains : Catalog := [(repeatWord 281470681808895, 4)]
def a21Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x11f91a2b3423f23, 0x68acd08fc8d159a, 0x566847e4])
  | 3 => BitVec.ofNat 152 (big [0x53c18fff6aa7831, 0x3ffdaa9e0c7ffb5, 0xfed54f06])
  | 4 => BitVec.ofNat 152 (big [0xea472ac629d48e5, 0xab18a7523956314, 0x8c53a91c])
  | 5 => BitVec.ofNat 152 (big [0xe52d469db3ca5a8, 0x1a76cf296a34ed9, 0x3b6794b5])
  | _ => 0

def a21Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x6fed3df1e4dfda7, 0xf7c7937f69ef8f2, 0xe3c9bfb4])
  | 3 => BitVec.ofNat 152 (big [0x0])
  | 4 => BitVec.ofNat 152 (big [0x6fed3df1e4dfda7, 0xf7c7937f69ef8f2, 0xe3c9bfb4])
  | 5 => BitVec.ofNat 152 (big [0x4d4d0170049a9a0, 0x5c0126a680b802, 0xe0093534])
  | _ => 0

def a21Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a21Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (84586+i*4) 4
  | _ => 0

def a21Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a21Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 84591 1 84593 1 84590 1 i
  | _ => []

def a21 : Atlas := ⟨4,rawDecor 58 a21Pos a21Neg,repeatWord 18389323178447208396,a21Count,a21Rec,(fun _ _ => 0),a21Loc⟩
def a21Domains : Catalog := [(repeatWord 71777214294589695, 4)]
def a22Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x8e3b5392b3889d6, 0x34ae8e163a58639, 0x88d086f1])
  | 2 => BitVec.ofNat 152 (big [0xec3ff253ba8138f, 0x67eea57fbe9429c, 0xfdce2cf5])
  | 3 => BitVec.ofNat 152 (big [0x2e123fcc139c54, 0x79cfef805ded777, 0xf6bbef4f])
  | 4 => BitVec.ofNat 152 (big [0x374cefbd0d468e3, 0xaa513dda9b72a28, 0xa9ff9b99])
  | 5 => BitVec.ofNat 152 (big [0xd40753cbc95833a, 0x7af48aa96fabce1, 0xafea16a6])
  | _ => 0

def a22Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xbff947b3a18adf6, 0xfe7c55f3bc71ee5, 0x77a0efca])
  | 2 => BitVec.ofNat 152 (big [0x228400a01201, 0x8000420001a, 0x80031001])
  | 3 => BitVec.ofNat 152 (big [0x5100900000c14, 0x11102400044, 0xa00000])
  | 4 => BitVec.ofNat 152 (big [0x3200462321020e2, 0x366804a08030221, 0x64004c0a])
  | 5 => BitVec.ofNat 152 (big [0xe04170b855812a, 0xcdc14c2688b9981, 0x154c844a])
  | _ => 0

def a22Count (k : Nat) : Nat :=
  match k with
  | 4 => 55
  | 5 => 85
  | 6 => 14
  | 7 => 1
  | _ => 0

def a22Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (84594+i*38) 38
  | 5 => field storageWord (87311+i*27) 27
  | 6 => field storageWord (92093+i*16) 16
  | 7 => field storageWord (93340+i*5) 5
  | _ => 0

def a22Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 55 55 (field storageWord (86684+(tag % 55)*7) 7) tag
  | 5 => hashRow 85 85 (field storageWord (89606+(tag % 85)*8) 8) tag
  | 6 => hashRow 14 14 (field storageWord (92317+(tag % 14)*5) 5) tag
  | 7 => 0
  | _ => 0

def a22Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 87129 3 87297 2 87069 20 i
  | 5 => hintsAt storageWord 91086 7 91688 5 90286 32 i
  | 6 => hintsAt storageWord 92870 7 92975 5 92387 21 i
  | 7 => hintsAt storageWord 93351 2 93355 2 93345 2 i
  | _ => []

def a22 : Atlas := ⟨7,rawDecor 62 a22Pos a22Neg,repeatWord 18443366309563724736,a22Count,a22Rec,(fun _ _ => 0),a22Loc⟩
def a22Domains : Catalog := [(repeatWord 4294967295, 6), (repeatWord 1085102592571150095, 5), (repeatWord 281470681808895, 5), (repeatWord 4340410370284600380, 5), (repeatWord 14714328930390887475, 5), (repeatWord 3689348817318890700, 5), (repeatWord 1148435428713435120, 5), (repeatWord 1085350949055099120, 5), (repeatWord 71777218556133120, 5), (repeatWord 71777214294589695, 4), (repeatWord 16711935, 3), (repeatWord 65535, 3)]
def a23Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x310cb96aa347986, 0x618865cb551a3cc, 0xe5aa8d1e])
  | 3 => BitVec.ofNat 152 (big [0x1f7fee03fd754c3, 0x30fbff701febaa6, 0xb80ff5d5])
  | 4 => BitVec.ofNat 152 (big [0xc9a1c49544f92b9, 0xae4d0e24aa27c95, 0x125513e4])
  | 5 => BitVec.ofNat 152 (big [0x23ebb02f6c4d7a4, 0xe91f5d817b626bd, 0xc0bdb135])
  | _ => 0

def a23Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x5edb1ee7a6d31ab, 0x6af6d8f73d3698d, 0x7b9e9b4c])
  | 3 => BitVec.ofNat 152 (big [0x188212830200083, 0x20c410941810004, 0x4a0c0800])
  | 4 => BitVec.ofNat 152 (big [0x5edb1ee7a6d31ab, 0x6af6d8f73d3698d, 0x7b9e9b4c])
  | 5 => BitVec.ofNat 152 (big [0x2444cd507485724, 0xc922266a83a42b9, 0x3541d215])
  | _ => 0

def a23Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | 4 => 4
  | 5 => 1
  | _ => 0

def a23Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (93361+i*26) 26
  | 4 => field storageWord (93387+i*15) 15
  | 5 => field storageWord (93511+i*4) 4
  | _ => 0

def a23Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | 4 => hashRow 4 4 (field storageWord (93447+(tag % 4)*3) 3) tag
  | 5 => 0
  | _ => 0

def a23Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 93467 4 93487 2 93459 2 i
  | 5 => hintsAt storageWord 93521 2 93525 1 93515 3 i
  | _ => []

def a23 : Atlas := ⟨5,rawDecor 60 a23Pos a23Neg,repeatWord 18379190010832224240,a23Count,a23Rec,(fun _ _ => 0),a23Loc⟩
def a23Domains : Catalog := [(repeatWord 4294967295, 4), (repeatWord 18446744069414584320, 4), (repeatWord 17298308644996116495, 4), (repeatWord 18374687579166474495, 4), (repeatWord 16711935, 3)]
def a24Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x7ffec79a723d4da, 0x743f45b7cafa437, 0xffb3cf7c])
  | 2 => BitVec.ofNat 152 (big [0xf1042ef5ecc6a97, 0xbfa1f66dbf3fb2c, 0xd3ccf6d7])
  | 3 => BitVec.ofNat 152 (big [0x4a09d35a17f0167, 0xf4cfbe56976fedb, 0xf17d7db4])
  | 4 => BitVec.ofNat 152 (big [0x45fe8190124d41f, 0x7015c796d898c36, 0x9eb76b78])
  | 5 => BitVec.ofNat 152 (big [0x84555c16516b3b5, 0x8a45aad9d15eecf, 0x17fee36c])
  | _ => 0

def a24Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x2104000c60214c0, 0x54051902242090, 0x11400030])
  | 2 => BitVec.ofNat 152 (big [0x500804f00406817, 0x1292000858a830c, 0x290308])
  | 3 => BitVec.ofNat 152 (big [0x2c9e3b216d0123, 0x2a2226448025600, 0x68827302])
  | 4 => BitVec.ofNat 152 (big [0x52db0df3164e83f, 0x9297ae4ed8b9f6e, 0xe2abdb0b])
  | 5 => BitVec.ofNat 152 (big [0x24460d0e916b2b4, 0x95994551c91a9cb, 0x30f498c5])
  | _ => 0

def a24Count (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | 4 => 14
  | 5 => 42
  | 6 => 13
  | 7 => 1
  | _ => 0

def a24Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (93527+i*49) 49
  | 4 => field storageWord (93576+i*38) 38
  | 5 => field storageWord (94185+i*27) 27
  | 6 => field storageWord (97322+i*16) 16
  | 7 => field storageWord (98422+i*5) 5
  | _ => 0

def a24Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => 0
  | 4 => hashRow 14 7 (field storageWord (94108+(tag % 7)*4) 4) tag
  | 5 => hashRow 42 42 (field storageWord (95319+(tag % 42)*7) 7) tag
  | 6 => hashRow 13 5 (field storageWord (97530+(tag % 5)*5) 5) tag
  | 7 => 0
  | _ => 0

def a24Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 94169 1 94184 1 94136 33 i
  | 5 => hintsAt storageWord 96636 7 96937 5 95613 33 i
  | 6 => hintsAt storageWord 98038 6 98122 5 97555 21 i
  | 7 => hintsAt storageWord 98442 3 98448 3 98427 3 i
  | _ => []

def a24 : Atlas := ⟨7,rawDecor 61 a24Pos a24Neg,repeatWord 18062530664643361520,a24Count,a24Rec,(fun _ _ => 0),a24Loc⟩
def a24Domains : Catalog := [(repeatWord 6172840429334713770, 7), (repeatWord 18446744069414584320, 6), (repeatWord 6510615555426900570, 6), (repeatWord 6148914691236517205, 5), (repeatWord 18374966859414961920, 5), (repeatWord 6149008514797120170, 5), (repeatWord 18446462598732906495, 5), (repeatWord 1085102592571150095, 4), (repeatWord 4294967295, 4), (repeatWord 6124988953138320640, 4), (repeatWord 6148914689804861440, 4), (repeatWord 17361393124654452495, 4), (repeatWord 71777214294589695, 3), (repeatWord 1085102592318504960, 3), (repeatWord 16711935, 3)]
def a25Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x9effdea12887fb9, 0x53f7b3bb73faa1d, 0xd7cc779d])
  | 1 => BitVec.ofNat 152 (big [0xfc44e1ffff6066c, 0xfffbdb641f751eb, 0x25ffaa4d])
  | 2 => BitVec.ofNat 152 (big [0x6ff2a17bf61e4d6, 0xed5ddc6c9617f67, 0x6fa382eb])
  | 3 => BitVec.ofNat 152 (big [0x83fd92bec1ff326, 0x7e8ca7e1cd4cebc, 0x4f3abd37])
  | 5 => BitVec.ofNat 152 (big [0x91967c178ff889b, 0xe46faf5bb8f6d97, 0xf95f78bb])
  | _ => 0

def a25Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x140515202002d38, 0x40aa100120d, 0x19803c])
  | 1 => BitVec.ofNat 152 (big [0xc004c60ded20268, 0x813ff00301141, 0x436c283])
  | 2 => BitVec.ofNat 152 (big [0xad301721216496, 0x415a00067410406, 0x11011c34])
  | 3 => BitVec.ofNat 152 (big [0x80e0829041cd206, 0x5d208844c0cc8f0, 0xe0040243])
  | 5 => BitVec.ofNat 152 (big [0x411020438ef8081, 0x38b6b51128fe800, 0x21203980])
  | _ => 0

def a25Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 7 => 1
  | _ => 0

def a25Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (98463+i*16) 16
  | 7 => field storageWord (98521+i*5) 5
  | _ => 0

def a25Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | 7 => 0
  | _ => 0

def a25Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 98497 3 98503 3 98479 3 i
  | 7 => hintsAt storageWord 98544 3 98550 3 98526 3 i
  | _ => []

def a25 : Atlas := ⟨7,rawDecor 47 a25Pos a25Neg,repeatWord 18368774315098303168,a25Count,a25Rec,(fun _ _ => 0),a25Loc⟩
def a25Domains : Catalog := [(repeatWord 3689348814741910323, 5), (repeatWord 14757395258967641292, 5), (repeatWord 1085102592571150095, 5), (repeatWord 17361641481138401520, 5), (repeatWord 18446744069414584320, 5), (repeatWord 6124988953138320640, 4), (repeatWord 6148914689804861440, 4)]
def a26Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xebf1c337b29972b, 0xf5dcf5e3d3b2d9d, 0xfad5e9f5])
  | 2 => BitVec.ofNat 152 (big [0x2738e633bd889e5, 0x82b7b0579f8b3ba, 0xbfb77465])
  | 3 => BitVec.ofNat 152 (big [0x96ed6fd59d166da, 0xf3d937fc785ae25, 0xcdf9ffcc])
  | 4 => BitVec.ofNat 152 (big [0x6e0b19b8c7e9c5c, 0x1feffa766f2d5e6, 0xceb625db])
  | 5 => BitVec.ofNat 152 (big [0xa7700316959854b, 0x13442447c11ac10, 0xa6506124])
  | _ => 0

def a26Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x82c062c219229, 0x290280230232c04, 0x50901048])
  | 2 => BitVec.ofNat 152 (big [0x57c04113d80984, 0xc0e01a489d041e8, 0x5082d11])
  | 3 => BitVec.ofNat 152 (big [0x8341039914044d2, 0x6c619c0040220, 0x28034802])
  | 4 => BitVec.ofNat 152 (big [0xaa0b082a83c845c, 0x20055370c04d900, 0x994243e8])
  | 5 => BitVec.ofNat 152 (big [0xbfeb9fbf97dc5df, 0xbe6dfbfec56ff38, 0xfb5befef])
  | _ => 0

def a26Count (k : Nat) : Nat :=
  match k with
  | 4 => 2
  | 5 => 21
  | 6 => 12
  | 7 => 1
  | _ => 0

def a26Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (98568+i*38) 38
  | 5 => field storageWord (98648+i*27) 27
  | 6 => field storageWord (99893+i*16) 16
  | 7 => field storageWord (100842+i*5) 5
  | _ => 0

def a26Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 2 2 (field storageWord (98644+(tag % 2)*2) 2) tag
  | 5 => hashRow 21 11 (field storageWord (99215+(tag % 11)*6) 6) tag
  | 6 => hashRow 12 24 (field storageWord (100085+(tag % 24)*5) 5) tag
  | 7 => 0
  | _ => 0

def a26Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 99638 5 99748 5 99281 21 i
  | 6 => hintsAt storageWord 100520 6 100598 4 100205 21 i
  | 7 => hintsAt storageWord 100855 2 100859 1 100847 4 i
  | _ => []

def a26 : Atlas := ⟨7,rawDecor 62 a26Pos a26Neg,repeatWord 18212782022387040192,a26Count,a26Rec,(fun _ _ => 0),a26Loc⟩
def a26Domains : Catalog := [(repeatWord 3689517697150995660, 6), (repeatWord 3689348817318890700, 6), (repeatWord 17361641477348724495, 6), (repeatWord 3689348814741910323, 5), (repeatWord 17361641481138401520, 5), (repeatWord 18446462603027742720, 5), (repeatWord 18446744069414584320, 5), (repeatWord 3732415143318664140, 5), (repeatWord 18374966855153418495, 5), (repeatWord 1085102592571150095, 4), (repeatWord 281470681808895, 4), (repeatWord 3472328296227680304, 4), (repeatWord 18446462598732840960, 4)]
def a27Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdffffdfff5feffe, 0xfbffffbf6effff7, 0xffdfffff])
  | 2 => BitVec.ofNat 152 (big [0xbd7c9b6e8a39d5d, 0x9474afd49dc51dc, 0xd2361f54])
  | 3 => BitVec.ofNat 152 (big [0xb5cae2799f25ec3, 0xfc6b1de5f7bfb2e, 0x2eff71e6])
  | 4 => BitVec.ofNat 152 (big [0xff091f936acb8b7, 0x9f91cf5affdcccb, 0xb97ef6d9])
  | 5 => BitVec.ofNat 152 (big [0xf2f4de0f0a1f36b, 0xa42721f2b777518, 0xf7f6ea53])
  | _ => 0

def a27Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xe30882172304, 0x981000900031c84, 0x21880140])
  | 2 => BitVec.ofNat 152 (big [0xbb6838f44a28d5d, 0xa2a0f32488c5358, 0x99caf026])
  | 3 => BitVec.ofNat 152 (big [0x15a086319605cc3, 0x23643b2d7c0e308, 0x1a654089])
  | 4 => BitVec.ofNat 152 (big [0x9e010d364a898b2, 0x36a4c4bbf8a002, 0x5211f415])
  | 5 => BitVec.ofNat 152 (big [0xea73c60f381f26b, 0x4d17d834075e000, 0x425737c2])
  | _ => 0

def a27Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a27Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (100861+i*5) 5
  | _ => 0

def a27Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a27Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 100867 1 100869 1 100866 1 i
  | _ => []

def a27 : Atlas := ⟨6,rawDecor 61 a27Pos a27Neg,repeatWord 18062436862557596160,a27Count,a27Rec,(fun _ _ => 0),a27Loc⟩
def a27Domains : Catalog := [(repeatWord 17361641481138401520, 6)]
def a28Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x6ed0cbe5750ea8c, 0xb7efd7f7ef755d3, 0x7f6ab81d])
  | 1 => BitVec.ofNat 152 (big [0xd127350ffb69473, 0xcd93669b37be82e, 0x7f9ddfea])
  | 2 => BitVec.ofNat 152 (big [0x88c9757f2c93935, 0xe552f95ab9a8e4d, 0xd3b1a947])
  | 4 => BitVec.ofNat 152 (big [0x9a3a0f38ddd45c5, 0x27315a2b84e2b65, 0x9b1ee7df])
  | 5 => BitVec.ofNat 152 (big [0xe15e38710fb5b42, 0xa9aae85d00f32af, 0xebff14af])
  | _ => 0

def a28Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x0])
  | 1 => BitVec.ofNat 152 (big [0x440000003068010, 0x804000050002808, 0x80108010])
  | 2 => BitVec.ofNat 152 (big [0x2acd912f8c83925, 0x1f208090c530404, 0xd470ac3])
  | 4 => BitVec.ofNat 152 (big [0x82a10fb0cb944c5, 0x2cf34a57200e1, 0x340911a4])
  | 5 => BitVec.ofNat 152 (big [0xa03622430715b42, 0x710676608890697, 0x1a065948])
  | _ => 0

def a28Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a28Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (100870+i*5) 5
  | _ => 0

def a28Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a28Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 100876 1 100878 1 100875 1 i
  | _ => []

def a28 : Atlas := ⟨6,rawDecor 55 a28Pos a28Neg,repeatWord 18374386239696464618,a28Count,a28Rec,(fun _ _ => 0),a28Loc⟩
def a28Domains : Catalog := [(repeatWord 6148914691236517205, 6)]
def a29Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf5787bf56d9bca2, 0xec6ffb632727cf5, 0xa2eabb78])
  | 1 => BitVec.ofNat 152 (big [0x7ba7c506aa74d59, 0xffd84ffedde8f19, 0x7d7f4eb2])
  | 2 => BitVec.ofNat 152 (big [0x84b7935af1616fc, 0x3ff97cfe3fd143e, 0x9e6cef77])
  | 3 => BitVec.ofNat 152 (big [0xfb09cccab69432f, 0xfe97c72fe25dbe2, 0xe3bf8ca7])
  | 4 => BitVec.ofNat 152 (big [0x604bb3addb0ab56, 0xb4aea719763b913, 0xdb5c7bbd])
  | _ => 0

def a29Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xb00002152418c80, 0x800218080490, 0xc0020a2])
  | 1 => BitVec.ofNat 152 (big [0x630000332830d41, 0xe880a0089d88091, 0x84030e3])
  | 2 => BitVec.ofNat 152 (big [0xcf711489141238, 0x141648422244000, 0xc018c308])
  | 3 => BitVec.ofNat 152 (big [0x899c400028422e, 0x20315c62007962, 0x402a4900])
  | 4 => BitVec.ofNat 152 (big [0x464485a0db02156, 0x6715aa184e33840, 0x2978811])
  | _ => 0

def a29Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a29Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (100879+i*5) 5
  | _ => 0

def a29Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a29Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 100885 1 100887 1 100884 1 i
  | _ => []

def a29 : Atlas := ⟨6,rawDecor 31 a29Pos a29Neg,repeatWord 18368756680300883680,a29Count,a29Rec,(fun _ _ => 0),a29Loc⟩
def a29Domains : Catalog := [(repeatWord 3689348814741910323, 6)]
def a30Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdf7e3ab1f4aadbe, 0xcfc1fffacafe1b4, 0x27ed2c2f])
  | 2 => BitVec.ofNat 152 (big [0xb3615b8b085bed8, 0xbe9f63dfbd5674e, 0x99727b86])
  | 3 => BitVec.ofNat 152 (big [0xe19eaf6fb70c2f3, 0xdf73cc7b07959f1, 0x7cdece5c])
  | 4 => BitVec.ofNat 152 (big [0x3ea5c57f4bf5745, 0xf1fedf257feff6f, 0xff33f3f7])
  | 5 => BitVec.ofNat 152 (big [0xffc5bec3d12b1d, 0xea4221929f6508a, 0x35f699ef])
  | _ => 0

def a30Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x512120005028d28, 0xc025045082681a0, 0x1004909])
  | 2 => BitVec.ofNat 152 (big [0xc34b1a0b401b6d8, 0x958024082445b4e, 0x4067e5cd])
  | 3 => BitVec.ofNat 152 (big [0x809a932107002d2, 0x238870030495a58, 0x700402c4])
  | 4 => BitVec.ofNat 152 (big [0x2804041408c4005, 0x520b241902000, 0x80000])
  | 5 => BitVec.ofNat 152 (big [0x862cfdf83d12b15, 0x3c110a162b0d058, 0xc610a212])
  | _ => 0

def a30Count (k : Nat) : Nat :=
  match k with
  | 4 => 2
  | 5 => 4
  | 6 => 1
  | _ => 0

def a30Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (100888+i*27) 27
  | 5 => field storageWord (100956+i*16) 16
  | 6 => field storageWord (101112+i*5) 5
  | _ => 0

def a30Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 2 7 (field storageWord (100942+(tag % 7)*2) 2) tag
  | 5 => hashRow 4 5 (field storageWord (101020+(tag % 5)*3) 3) tag
  | 6 => 0
  | _ => 0

def a30Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 101050 4 101070 3 101035 3 i
  | 6 => hintsAt storageWord 101126 2 101130 2 101117 3 i
  | _ => []

def a30 : Atlas := ⟨6,rawDecor 61 a30Pos a30Neg,repeatWord 18445242832315394560,a30Count,a30Rec,(fun _ _ => 0),a30Loc⟩
def a30Domains : Catalog := [(repeatWord 71777214294589695, 5), (repeatWord 4294967295, 5), (repeatWord 18446744069414584320, 5), (repeatWord 11936128518282651045, 5), (repeatWord 1085350949055099120, 5), (repeatWord 252645135, 4)]
def a31Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xdbc1f7ff7e09cd9, 0x9cffbb36cdf0aab, 0x96ebf9fe])
  | 2 => BitVec.ofNat 152 (big [0x70f9fcf314d46ff, 0x534fde679e8cffa, 0xdcffba7d])
  | 3 => BitVec.ofNat 152 (big [0x9f9e1bcfeb3bb2e, 0xeffd75d971ff677, 0xffdaedce])
  | 4 => BitVec.ofNat 152 (big [0x5900d6493618a8d, 0x94021126d9486a3, 0x965909fc])
  | 5 => BitVec.ofNat 152 (big [0xbe725db89ad6f05, 0xc6621444136efe8, 0xdc14b625])
  | _ => 0

def a31Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x880036a2ea014c1, 0x64094328827008a, 0x91645440])
  | 2 => BitVec.ofNat 152 (big [0x70cd4811149423a, 0x898090c21884021, 0x80a2081])
  | 3 => BitVec.ofNat 152 (big [0x5210084c011890e, 0xa24a0814083601, 0x4008811])
  | 4 => BitVec.ofNat 152 (big [0xf33bdc7d371cb8f, 0xab2eb3a559df627, 0x7e6bde9f])
  | 5 => BitVec.ofNat 152 (big [0x8a3231b0da46f05, 0xc15129246b0dae0, 0xe379cc24])
  | _ => 0

def a31Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a31Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (101136+i*5) 5
  | _ => 0

def a31Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a31Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 101149 3 101155 2 101141 2 i
  | _ => []

def a31 : Atlas := ⟨6,rawDecor 62 a31Pos a31Neg,repeatWord 18212838302778720192,a31Count,a31Rec,(fun _ _ => 0),a31Loc⟩
def a31Domains : Catalog := [(repeatWord 3689348814741910323, 5), (repeatWord 17361641481138401520, 5), (repeatWord 18446462603027742720, 5), (repeatWord 18446744069414584320, 5)]
def a32Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xf8b17f6b78f5aae, 0xfed26efed9ebb3e, 0xeffa7efd])
  | 1 => BitVec.ofNat 152 (big [0x47cf8cbda72bf55, 0x4b2fb3a5a634dfb, 0x58c5f1be])
  | 2 => BitVec.ofNat 152 (big [0xc77f74de898a5e7, 0xfe3fef2bf936d61, 0x9117e2fe])
  | 4 => BitVec.ofNat 152 (big [0xb5b288b1567a872, 0x7966ddbaf6edaca, 0x6a783bae])
  | 5 => BitVec.ofNat 152 (big [0xa4ec44cd89f2865, 0xea528ba0f1e3620, 0xb0562216])
  | _ => 0

def a32Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x88050802084180c, 0x80010a4008a020, 0x830400a])
  | 1 => BitVec.ofNat 152 (big [0x4c8d0d300321b54, 0x60cc122004e6413, 0x32180a])
  | 2 => BitVec.ofNat 152 (big [0x160600c008a4a3, 0x11051be9119c4, 0x7042395])
  | 4 => BitVec.ofNat 152 (big [0x10526281163a062, 0xa43bca19f265eca, 0x434485a5])
  | 5 => BitVec.ofNat 152 (big [0xbce54ccb8bf386d, 0xebef57ec9eff473, 0x4fbb75ca])
  | _ => 0

def a32Count (k : Nat) : Nat :=
  match k with
  | 4 => 2
  | 5 => 6
  | 6 => 1
  | _ => 0

def a32Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (101163+i*27) 27
  | 5 => field storageWord (101231+i*16) 16
  | 6 => field storageWord (101499+i*5) 5
  | _ => 0

def a32Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 2 7 (field storageWord (101217+(tag % 7)*2) 2) tag
  | 5 => hashRow 6 3 (field storageWord (101327+(tag % 3)*4) 4) tag
  | 6 => 0
  | _ => 0

def a32Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 101444 4 101472 3 101339 21 i
  | 6 => hintsAt storageWord 101516 3 101522 2 101504 3 i
  | _ => []

def a32 : Atlas := ⟨6,rawDecor 55 a32Pos a32Neg,repeatWord 16927589406111361770,a32Count,a32Rec,(fun _ _ => 0),a32Loc⟩
def a32Domains : Catalog := [(repeatWord 14757395258967641292, 5), (repeatWord 1085102592571150095, 5), (repeatWord 7378697629483820646, 5), (repeatWord 281470681808895, 4), (repeatWord 18446744069414584320, 4)]
def a33Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xb3f7bed6dee0f6b, 0xaf19bb49eb3bc66, 0xfcf72cfe])
  | 1 => BitVec.ofNat 152 (big [0x4f8ff3b9257f49d, 0xd9f7efb71def3d9, 0xebbbd757])
  | 2 => BitVec.ofNat 152 (big [0x6fbd896eeef3996, 0xdfeec1b72ffffd8, 0xd5bb79db])
  | 3 => BitVec.ofNat 152 (big [0xf9fa7edbd90c7ff, 0xb7d97ec8d1a7a2f, 0xaa67a7bc])
  | 5 => BitVec.ofNat 152 (big [0x9c36d05783deb45, 0xac722c8ebbde655, 0x57afdac5])
  | _ => 0

def a33Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x979206605e60c41, 0x45310b40281a161, 0x2207b52])
  | 1 => BitVec.ofNat 152 (big [0x868bb2012166489, 0x5000200464833e1, 0xe0086a18])
  | 2 => BitVec.ofNat 152 (big [0x69140d2e8e91116, 0x202550139964400, 0x4f38525])
  | 3 => BitVec.ofNat 152 (big [0x2860009a000c3be, 0x800e3492d521e0c, 0xc59848d])
  | 5 => BitVec.ofNat 152 (big [0xa664d35881dab45, 0xf84e48cab38e491, 0x2a421016])
  | _ => 0

def a33Count (k : Nat) : Nat :=
  match k with
  | 4 => 8
  | 5 => 24
  | 6 => 1
  | _ => 0

def a33Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (101530+i*27) 27
  | 5 => field storageWord (101778+i*16) 16
  | 6 => field storageWord (102434+i*5) 5
  | _ => 0

def a33Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 8 8 (field storageWord (101746+(tag % 8)*4) 4) tag
  | 5 => hashRow 24 24 (field storageWord (102162+(tag % 24)*6) 6) tag
  | 6 => 0
  | _ => 0

def a33Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 102318 4 102418 2 102306 3 i
  | 6 => hintsAt storageWord 102457 3 102463 3 102439 3 i
  | _ => []

def a33 : Atlas := ⟨6,rawDecor 47 a33Pos a33Neg,repeatWord 17213020425588632256,a33Count,a33Rec,(fun _ _ => 0),a33Loc⟩
def a33Domains : Catalog := [(repeatWord 11936128518282651045, 6), (repeatWord 14714328930390887475, 6), (repeatWord 7378697629483820646, 5), (repeatWord 6172840429334713770, 5), (repeatWord 4340410370284600380, 5), (repeatWord 1148435428713435120, 5)]
def a34Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xe13ac709a6a9a69, 0x97b1cc7629e7795, 0x3b3e6bae])
  | 2 => BitVec.ofNat 152 (big [0xce1b3cd73ad4074, 0xfcec378e79b5c68, 0xfff7f7f7])
  | 3 => BitVec.ofNat 152 (big [0x11c73129cf32d83, 0x929b5ff18e7bbaf, 0x6ecfed75])
  | 4 => BitVec.ofNat 152 (big [0xf8e8fa80d5cf388, 0xa363ea2eceb3bb0, 0xd35cee1e])
  | 5 => BitVec.ofNat 152 (big [0x97d8d66478e647, 0x849d6745d29a13e, 0x8c57fd8f])
  | _ => 0

def a34Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x811002238281a61, 0x1a03140dc800551, 0x4c05205])
  | 2 => BitVec.ofNat 152 (big [0x0])
  | 3 => BitVec.ofNat 152 (big [0x24311000030480, 0xc4c0000130080, 0x90040000])
  | 4 => BitVec.ofNat 152 (big [0x702c2814154e108, 0xc438080010cd220, 0xa212c50])
  | 5 => BitVec.ofNat 152 (big [0x3c0c8626568e247, 0xff380a90e40252d, 0x6be80317])
  | _ => 0

def a34Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a34Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (102481+i*5) 5
  | _ => 0

def a34Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a34Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 102487 1 102489 1 102486 1 i
  | _ => []

def a34 : Atlas := ⟨5,rawDecor 61 a34Pos a34Neg,repeatWord 18445336634401159920,a34Count,a34Rec,(fun _ _ => 0),a34Loc⟩
def a34Domains : Catalog := [(repeatWord 1085102592571150095, 5)]
def a35Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x7fe7ffd9d6dff29, 0xf3eff67fbfb1fe5, 0xd3f6f7bf])
  | 1 => BitVec.ofNat 152 (big [0x923919766f60fd6, 0x2ed89de9ef6f29e, 0x6f8df956])
  | 3 => BitVec.ofNat 152 (big [0xbbfccda77bae9de, 0x7ede2fd57deea3f, 0x7fbf7e7f])
  | 4 => BitVec.ofNat 152 (big [0xc59fbedecdd96b3, 0xffeddf2ba2775fc, 0xb474e384])
  | 5 => BitVec.ofNat 152 (big [0x4ab7b02b222a6fd, 0x7dd96fa6674bb17, 0xac3d4e53])
  | _ => 0

def a35Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x24b410256c01, 0x300802726501ca0, 0x4c88048])
  | 1 => BitVec.ofNat 152 (big [0x760b4a104760f52, 0x35c19e0e668a9c, 0x66c04ad])
  | 3 => BitVec.ofNat 152 (big [0x28b0848439a818c, 0x8880440118b6313, 0xc8161013])
  | 4 => BitVec.ofNat 152 (big [0xcd94141a4c892b2, 0x2944509121c14e, 0x78226b82])
  | 5 => BitVec.ofNat 152 (big [0x4a27b432020a6fd, 0x6762165461cfdce, 0x96e2ddca])
  | _ => 0

def a35Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a35Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (102490+i*5) 5
  | _ => 0

def a35Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a35Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 102496 1 102498 1 102495 1 i
  | _ => []

def a35 : Atlas := ⟨5,rawDecor 59 a35Pos a35Neg,repeatWord 17197819814839233024,a35Count,a35Rec,(fun _ _ => 0),a35Loc⟩
def a35Domains : Catalog := [(repeatWord 14757395258967641292, 5)]
def a36Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfe35eff37f32a8c, 0xf6dfdead168900d, 0xfe2d9fff])
  | 1 => BitVec.ofNat 152 (big [0x89ce5334bb99553, 0x49af2bb36b765f6, 0xf5d67cab])
  | 2 => BitVec.ofNat 152 (big [0xb121b09cecedc34, 0xc9331cdfed67f66, 0xb98eeb83])
  | 3 => BitVec.ofNat 152 (big [0x9cbaf5846641fb, 0xf3f6bc6bd18ff3, 0xd0df0634])
  | 5 => BitVec.ofNat 152 (big [0x9593718b1fc6da2, 0x90f81d53b25cb43, 0xdb173296])
  | _ => 0

def a36Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x0])
  | 1 => BitVec.ofNat 152 (big [0xe8010243b18442, 0x2401280a800412, 0xa0208090])
  | 2 => BitVec.ofNat 152 (big [0xe141889984a5834, 0x8536a9110207124, 0x1209084d])
  | 3 => BitVec.ofNat 152 (big [0x582f104464199, 0xb08d811a059b940, 0x1c846605])
  | 5 => BitVec.ofNat 152 (big [0xb51b65258bc2da2, 0x21805a20ce4025b, 0xe8ef2d52])
  | _ => 0

def a36Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a36Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (102499+i*5) 5
  | _ => 0

def a36Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a36Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 102505 1 102507 1 102504 1 i
  | _ => []

def a36 : Atlas := ⟨5,rawDecor 47 a36Pos a36Neg,repeatWord 18368774315168165610,a36Count,a36Rec,(fun _ _ => 0),a36Loc⟩
def a36Domains : Catalog := [(repeatWord 6148914691236517205, 5)]
def a37Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xcfff586abedfa50, 0xfe777e766fd76e7, 0x6cefaef8])
  | 1 => BitVec.ofNat 152 (big [0xfe53a795c57c5ef, 0xadbfe9c9d72af9d, 0xdfd87d9f])
  | 2 => BitVec.ofNat 152 (big [0x7b88e9b947c273b, 0xb8bcdbdcd66bb1d, 0x595b5fd7])
  | 3 => BitVec.ofNat 152 (big [0xc1bb56e7e2a79cd, 0x5d6d6d1f7c44f92, 0xbf021af8])
  | 4 => BitVec.ofNat 152 (big [0xef4f9f4d79b8695, 0x2bbf732723d1d6c, 0xfaa7e42b])
  | _ => 0

def a37Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x8d630000c4ea00, 0x144020c847204, 0x8000708c])
  | 1 => BitVec.ofNat 152 (big [0x34032200043c4e8, 0xcc040c601aa0f84, 0x80809472])
  | 2 => BitVec.ofNat 152 (big [0x4b04cd8943c2313, 0x33615096c45c013, 0x56686101])
  | 3 => BitVec.ofNat 152 (big [0xc109c42ae2811cd, 0x29093d0b2428132, 0xcf40b63])
  | 4 => BitVec.ofNat 152 (big [0xd208c44f31b0415, 0xb42183860390c38, 0xa2a0300])
  | _ => 0

def a37Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a37Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (102508+i*5) 5
  | _ => 0

def a37Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a37Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 102555 2 102559 1 102513 21 i
  | _ => []

def a37 : Atlas := ⟨5,rawDecor 31 a37Pos a37Neg,repeatWord 17215830639940135616,a37Count,a37Rec,(fun _ _ => 0),a37Loc⟩
def a37Domains : Catalog := [(repeatWord 7378697629483820646, 6)]
def a38Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xaeffa907fcb8b37, 0xea0ff6df8da89b3, 0xabffcfd2])
  | 1 => BitVec.ofNat 152 (big [0x710777f81b576c8, 0xdff2bf73fedf76c, 0x57a5b66f])
  | 3 => BitVec.ofNat 152 (big [0x2298351dfbade20, 0x79a960dc036c797, 0x8de0e78a])
  | 4 => BitVec.ofNat 152 (big [0x9f30a7be4649d51, 0xbdb7ab74c5f17a4, 0xc82c4ad8])
  | 5 => BitVec.ofNat 152 (big [0xe669dca0214d0b6, 0xe6f27a3c1bbcf0f, 0x3f3be333])
  | _ => 0

def a38Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x800000041090104, 0x200001402c00002, 0x1000020])
  | 1 => BitVec.ofNat 152 (big [0x700205000100608, 0x1000000000010, 0x20002c0])
  | 3 => BitVec.ofNat 152 (big [0x7a6a3531eb2de28, 0x54153a11414d7d8, 0x5e561fd3])
  | 4 => BitVec.ofNat 152 (big [0xa38ba2a8249851, 0xc9644e90d0f35a4, 0x34756114])
  | 5 => BitVec.ofNat 152 (big [0x4691ae3004d0b2, 0x558f7206d3e838d, 0x1071b404])
  | _ => 0

def a38Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a38Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (102561+i*5) 5
  | _ => 0

def a38Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a38Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 102567 1 102569 1 102566 1 i
  | _ => []

def a38 : Atlas := ⟨5,rawDecor 59 a38Pos a38Neg,repeatWord 17216961135462230732,a38Count,a38Rec,(fun _ _ => 0),a38Loc⟩
def a38Domains : Catalog := [(repeatWord 281470681808895, 5)]
def a39Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xc5ff2f3dcdfeacd, 0x4fffbebbbeefeb0, 0x375fdf7f])
  | 1 => BitVec.ofNat 152 (big [0xbfd9dbd6b225ffa, 0xbd85f9d4657d54f, 0xdbab209d])
  | 2 => BitVec.ofNat 152 (big [0xbfded5f27679d3f, 0xfd9d5564fd735ff, 0xd8ef769e])
  | 4 => BitVec.ofNat 152 (big [0x52f72f6fbd873d5, 0xde6fafdbae8cea7, 0xb7ff9f6b])
  | 5 => BitVec.ofNat 152 (big [0xe233c976c8d93ae, 0x27d2d678f1b3232, 0xc9dddb84])
  | _ => 0

def a39Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xc8ca2b0c04bea08, 0x168e00890873070, 0x8446040])
  | 1 => BitVec.ofNat 152 (big [0x4e90f3168204bda, 0x1368001204df105, 0xf96a4540])
  | 2 => BitVec.ofNat 152 (big [0x914404a81469425, 0x1375647300662, 0x411823e])
  | 4 => BitVec.ofNat 152 (big [0x21154c1b9011d5, 0x89506f42b784681, 0x621a14ac])
  | 5 => BitVec.ofNat 152 (big [0x60334f7348d13ae, 0x85009115b1f6303, 0x22e381fe])
  | _ => 0

def a39Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a39Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (102570+i*5) 5
  | _ => 0

def a39Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a39Hints : Hints := fun _ _ => []
def a39 : Atlas := ⟨4,rawDecor 55 a39Pos a39Neg,repeatWord 16927589406043979968,a39Count,a39Rec,(fun _ _ => 0),a39Loc⟩
def a39Domains : Catalog := []
def a40Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdfe77e06d42c5ce, 0xd976fabfa3377c6, 0xabd66eff])
  | 1 => BitVec.ofNat 152 (big [0xe629817deff3859, 0x34a9bdcb7eced7d, 0xde38bf2b])
  | 2 => BitVec.ofNat 152 (big [0xb8fca4e2e9ce731, 0x1a8d133a64c152d, 0xd49fddbb])
  | 3 => BitVec.ofNat 152 (big [0xfa9a479b22b5ae7, 0x2e74a7cc9c7fabd, 0x2b3daa51])
  | 4 => BitVec.ofNat 152 (big [0x551bbb8f1758638, 0xe7274e475f0606a, 0x73ef80ec])
  | 5 => BitVec.ofNat 152 (big [0x14f48b9c392bbaa, 0x4e05013bfddec12, 0x8e3b6212])
  | _ => 0

def a40Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x44241404d4205c4, 0x1809a20a002380, 0x80503a2d])
  | 1 => BitVec.ofNat 152 (big [0xc221814584b3858, 0x11b87163980a0d8, 0x4e18280a])
  | 2 => BitVec.ofNat 152 (big [0x10c824a2694c721, 0xa04021840c1c07, 0x80c69571])
  | 3 => BitVec.ofNat 152 (big [0xaa9a429b2285203, 0xac74059c0c1582d, 0x1050040])
  | 4 => BitVec.ofNat 152 (big [0x111bab0a0358238, 0xe4054043061c062, 0x332a81c0])
  | 5 => BitVec.ofNat 152 (big [0x14f48b9c392a8aa, 0x2249107af55fe43, 0xb394216])
  | _ => 0

def a40Count (k : Nat) : Nat :=
  match k with
  | 5 => 18
  | 6 => 207
  | 7 => 519
  | 8 => 304
  | 9 => 43
  | 10 => 1
  | _ => 0

def a40Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (102575+i*61) 61
  | 6 => field storageWord (103853+i*50) 50
  | 7 => field storageWord (121390+i*39) 39
  | 8 => field storageWord (211789+i*28) 28
  | 9 => field storageWord (260537+i*17) 17
  | 10 => field storageWord (266102+i*6) 6
  | _ => 0

def a40Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 18 36 (field storageWord (103673+(tag % 36)*5) 5) tag
  | 6 => hashRow 207 104 (field storageWord (114203+(tag % 104)*9) 9) tag
  | 7 => hashRow 519 260 (field storageWord (141631+(tag % 260)*11) 11) tag
  | 8 => hashRow 304 304 (field storageWord (220301+(tag % 304)*10) 10) tag
  | 9 => hashRow 43 22 (field storageWord (261268+(tag % 22)*7) 7) tag
  | 10 => 0
  | _ => 0

def a40Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 118739 8 120403 7 115139 45 i
  | 7 => hintsAt storageWord 179359 12 185599 10 144491 46 i
  | 8 => hintsAt storageWord 237689 12 241349 9 223341 34 i
  | 9 => hintsAt storageWord 263270 9 263666 7 261422 21 i
  | 10 => hintsAt storageWord 266123 3 266129 3 266108 3 i
  | _ => []

def a40 : Atlas := ⟨10,rawDecor 63 a40Pos a40Neg,repeatWord 18368756680032447168,a40Count,a40Rec,(fun _ _ => 0),a40Loc⟩
def a40Domains : Catalog := [(repeatWord 6172840429334713770, 9), (repeatWord 4340410370284600380, 9), (repeatWord 3689348817318890700, 9), (repeatWord 17361641477348724495, 9), (repeatWord 6148914691236517205, 8), (repeatWord 7378697629483820646, 8), (repeatWord 14714328930390887475, 8), (repeatWord 3689517697150995660, 8), (repeatWord 18446462598732906495, 8), (repeatWord 6148914692668172970, 8), (repeatWord 18374966855153418495, 8), (repeatWord 3689348814741910323, 7), (repeatWord 17361641481138401520, 7), (repeatWord 18374966859414961920, 7), (repeatWord 18446744069414584320, 7), (repeatWord 11936128518282651045, 7), (repeatWord 14757226376558555955, 7), (repeatWord 6149008514797120170, 7), (repeatWord 12297829381041378645, 7), (repeatWord 17361393124654452495, 7), (repeatWord 18374687579166474495, 7), (repeatWord 71777218556133120, 7), (repeatWord 281470681808895, 7), (repeatWord 14757395258967641292, 6), (repeatWord 1085102592571150095, 6), (repeatWord 18446462603027742720, 6), (repeatWord 4294967295, 6), (repeatWord 6124988953138320640, 6), (repeatWord 3472328296227680304, 6), (repeatWord 3689348813882916864, 6), (repeatWord 1148435428713435120, 6), (repeatWord 71777214294589695, 5), (repeatWord 6148820867675914240, 5), (repeatWord 6148914689804861440, 5), (repeatWord 868082074056920076, 5), (repeatWord 3435973836, 5), (repeatWord 252645135, 5), (repeatWord 18446462598732840960, 5), (repeatWord 1085102592318504960, 4), (repeatWord 71777214277877760, 4), (repeatWord 6148820866244280320, 4), (repeatWord 202116108, 4)]
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
theorem a3S4P0 : segment (checkRow a3 a3Domains a3Hints 4) 0 13 = true := by decide +kernel
theorem a3S4 (j : Nat) (hj : j < 13) : (checkRow a3 a3Domains a3Hints 4) j = true := by
  exact segmentRange a3S4P0 j (by omega) (by omega)
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
theorem a4S1P0 : segment (checkRow a4 a4Domains a4Hints 1) 0 2 = true := by decide +kernel
theorem a4S1 (j : Nat) (hj : j < 2) : (checkRow a4 a4Domains a4Hints 1) j = true := by
  exact segmentRange a4S1P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S2P0 : segment (checkRow a4 a4Domains a4Hints 2) 0 4 = true := by decide +kernel
theorem a4S2 (j : Nat) (hj : j < 4) : (checkRow a4 a4Domains a4Hints 2) j = true := by
  exact segmentRange a4S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4S3P0 : segment (checkRow a4 a4Domains a4Hints 3) 0 1 = true := by decide +kernel
theorem a4S3 (j : Nat) (hj : j < 1) : (checkRow a4 a4Domains a4Hints 3) j = true := by
  exact segmentRange a4S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Complete : Complete a4 a4Domains a4Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a4S1 j hj
  · exact a4S2 j hj
  · exact a4S3 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5S2P0 : segment (checkRow a5 a5Domains a5Hints 2) 0 1 = true := by decide +kernel
theorem a5S2 (j : Nat) (hj : j < 1) : (checkRow a5 a5Domains a5Hints 2) j = true := by
  exact segmentRange a5S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Complete : Complete a5 a5Domains a5Hints := by
  intro k hk j hj
  change k ≤ 2 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a5S2 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S2P0 : segment (checkRow a6 a6Domains a6Hints 2) 0 2 = true := by decide +kernel
theorem a6S2 (j : Nat) (hj : j < 2) : (checkRow a6 a6Domains a6Hints 2) j = true := by
  exact segmentRange a6S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S3P0 : segment (checkRow a6 a6Domains a6Hints 3) 0 12 = true := by decide +kernel
theorem a6S3 (j : Nat) (hj : j < 12) : (checkRow a6 a6Domains a6Hints 3) j = true := by
  exact segmentRange a6S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S4P0 : segment (checkRow a6 a6Domains a6Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S4P1 : segment (checkRow a6 a6Domains a6Hints 4) 16 11 = true := by decide +kernel
theorem a6S4 (j : Nat) (hj : j < 27) : (checkRow a6 a6Domains a6Hints 4) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a6S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a6S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P0 : segment (checkRow a6 a6Domains a6Hints 5) 0 10 = true := by decide +kernel
theorem a6S5 (j : Nat) (hj : j < 10) : (checkRow a6 a6Domains a6Hints 5) j = true := by
  exact segmentRange a6S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S6P0 : segment (checkRow a6 a6Domains a6Hints 6) 0 1 = true := by decide +kernel
theorem a6S6 (j : Nat) (hj : j < 1) : (checkRow a6 a6Domains a6Hints 6) j = true := by
  exact segmentRange a6S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Complete : Complete a6 a6Domains a6Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a6S2 j hj
  · exact a6S3 j hj
  · exact a6S4 j hj
  · exact a6S5 j hj
  · exact a6S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7S4P0 : segment (checkRow a7 a7Domains a7Hints 4) 0 12 = true := by decide +kernel
theorem a7S4 (j : Nat) (hj : j < 12) : (checkRow a7 a7Domains a7Hints 4) j = true := by
  exact segmentRange a7S4P0 j (by omega) (by omega)
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
theorem a8S2P0 : segment (checkRow a8 a8Domains a8Hints 2) 0 2 = true := by decide +kernel
theorem a8S2 (j : Nat) (hj : j < 2) : (checkRow a8 a8Domains a8Hints 2) j = true := by
  exact segmentRange a8S2P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S3P0 : segment (checkRow a8 a8Domains a8Hints 3) 0 6 = true := by decide +kernel
theorem a8S3 (j : Nat) (hj : j < 6) : (checkRow a8 a8Domains a8Hints 3) j = true := by
  exact segmentRange a8S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S4P0 : segment (checkRow a8 a8Domains a8Hints 4) 0 6 = true := by decide +kernel
theorem a8S4 (j : Nat) (hj : j < 6) : (checkRow a8 a8Domains a8Hints 4) j = true := by
  exact segmentRange a8S4P0 j (by omega) (by omega)
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
  · exact a8S2 j hj
  · exact a8S3 j hj
  · exact a8S4 j hj
  · exact a8S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S3P0 : segment (checkRow a9 a9Domains a9Hints 3) 0 15 = true := by decide +kernel
theorem a9S3 (j : Nat) (hj : j < 15) : (checkRow a9 a9Domains a9Hints 3) j = true := by
  exact segmentRange a9S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9S4P0 : segment (checkRow a9 a9Domains a9Hints 4) 0 12 = true := by decide +kernel
theorem a9S4 (j : Nat) (hj : j < 12) : (checkRow a9 a9Domains a9Hints 4) j = true := by
  exact segmentRange a9S4P0 j (by omega) (by omega)
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
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a9S3 j hj
  · exact a9S4 j hj
  · exact a9S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S4P0 : segment (checkRow a10 a10Domains a10Hints 4) 0 1 = true := by decide +kernel
theorem a10S4 (j : Nat) (hj : j < 1) : (checkRow a10 a10Domains a10Hints 4) j = true := by
  exact segmentRange a10S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Complete : Complete a10 a10Domains a10Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a10S4 j hj
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
theorem a14S3P0 : segment (checkRow a14 a14Domains a14Hints 3) 0 1 = true := by decide +kernel
theorem a14S3 (j : Nat) (hj : j < 1) : (checkRow a14 a14Domains a14Hints 3) j = true := by
  exact segmentRange a14S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Complete : Complete a14 a14Domains a14Hints := by
  intro k hk j hj
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a14S3 j hj
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
theorem a16S4P0 : segment (checkRow a16 a16Domains a16Hints 4) 0 5 = true := by decide +kernel
theorem a16S4 (j : Nat) (hj : j < 5) : (checkRow a16 a16Domains a16Hints 4) j = true := by
  exact segmentRange a16S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P0 : segment (checkRow a16 a16Domains a16Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P1 : segment (checkRow a16 a16Domains a16Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P2 : segment (checkRow a16 a16Domains a16Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P3 : segment (checkRow a16 a16Domains a16Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P4 : segment (checkRow a16 a16Domains a16Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P5 : segment (checkRow a16 a16Domains a16Hints 5) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P6 : segment (checkRow a16 a16Domains a16Hints 5) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P7 : segment (checkRow a16 a16Domains a16Hints 5) 112 15 = true := by decide +kernel
theorem a16S5 (j : Nat) (hj : j < 127) : (checkRow a16 a16Domains a16Hints 5) j = true := by
  by_cases bound : j < 64
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a16S5P0 j (by omega) (by omega)
      ·
        exact segmentRange a16S5P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a16S5P2 j (by omega) (by omega)
      ·
        exact segmentRange a16S5P3 j (by omega) (by omega)
  ·
    by_cases bound : j < 96
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a16S5P4 j (by omega) (by omega)
      ·
        exact segmentRange a16S5P5 j (by omega) (by omega)
    ·
      by_cases bound : j < 112
      ·
        exact segmentRange a16S5P6 j (by omega) (by omega)
      ·
        exact segmentRange a16S5P7 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P0 : segment (checkRow a16 a16Domains a16Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P1 : segment (checkRow a16 a16Domains a16Hints 6) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P2 : segment (checkRow a16 a16Domains a16Hints 6) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P3 : segment (checkRow a16 a16Domains a16Hints 6) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P4 : segment (checkRow a16 a16Domains a16Hints 6) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P5 : segment (checkRow a16 a16Domains a16Hints 6) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P6 : segment (checkRow a16 a16Domains a16Hints 6) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P7 : segment (checkRow a16 a16Domains a16Hints 6) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S6P8 : segment (checkRow a16 a16Domains a16Hints 6) 128 4 = true := by decide +kernel
theorem a16S6 (j : Nat) (hj : j < 132) : (checkRow a16 a16Domains a16Hints 6) j = true := by
  by_cases bound : j < 64
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a16S6P0 j (by omega) (by omega)
      ·
        exact segmentRange a16S6P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a16S6P2 j (by omega) (by omega)
      ·
        exact segmentRange a16S6P3 j (by omega) (by omega)
  ·
    by_cases bound : j < 96
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a16S6P4 j (by omega) (by omega)
      ·
        exact segmentRange a16S6P5 j (by omega) (by omega)
    ·
      by_cases bound : j < 112
      ·
        exact segmentRange a16S6P6 j (by omega) (by omega)
      ·
        by_cases bound : j < 128
        ·
          exact segmentRange a16S6P7 j (by omega) (by omega)
        ·
          exact segmentRange a16S6P8 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S7P0 : segment (checkRow a16 a16Domains a16Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S7P1 : segment (checkRow a16 a16Domains a16Hints 7) 16 5 = true := by decide +kernel
theorem a16S7 (j : Nat) (hj : j < 21) : (checkRow a16 a16Domains a16Hints 7) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a16S7P0 j (by omega) (by omega)
  ·
    exact segmentRange a16S7P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S8P0 : segment (checkRow a16 a16Domains a16Hints 8) 0 1 = true := by decide +kernel
theorem a16S8 (j : Nat) (hj : j < 1) : (checkRow a16 a16Domains a16Hints 8) j = true := by
  exact segmentRange a16S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Complete : Complete a16 a16Domains a16Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a16S4 j hj
  · exact a16S5 j hj
  · exact a16S6 j hj
  · exact a16S7 j hj
  · exact a16S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P0 : segment (checkRow a17 a17Domains a17Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P1 : segment (checkRow a17 a17Domains a17Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P2 : segment (checkRow a17 a17Domains a17Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P3 : segment (checkRow a17 a17Domains a17Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P4 : segment (checkRow a17 a17Domains a17Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P5 : segment (checkRow a17 a17Domains a17Hints 5) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P6 : segment (checkRow a17 a17Domains a17Hints 5) 96 12 = true := by decide +kernel
theorem a17S5 (j : Nat) (hj : j < 108) : (checkRow a17 a17Domains a17Hints 5) j = true := by
  by_cases bound : j < 48
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a17S5P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 32
      ·
        exact segmentRange a17S5P1 j (by omega) (by omega)
      ·
        exact segmentRange a17S5P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 80
    ·
      by_cases bound : j < 64
      ·
        exact segmentRange a17S5P3 j (by omega) (by omega)
      ·
        exact segmentRange a17S5P4 j (by omega) (by omega)
    ·
      by_cases bound : j < 96
      ·
        exact segmentRange a17S5P5 j (by omega) (by omega)
      ·
        exact segmentRange a17S5P6 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P0 : segment (checkRow a17 a17Domains a17Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P1 : segment (checkRow a17 a17Domains a17Hints 6) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P2 : segment (checkRow a17 a17Domains a17Hints 6) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P3 : segment (checkRow a17 a17Domains a17Hints 6) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P4 : segment (checkRow a17 a17Domains a17Hints 6) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P5 : segment (checkRow a17 a17Domains a17Hints 6) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P6 : segment (checkRow a17 a17Domains a17Hints 6) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S6P7 : segment (checkRow a17 a17Domains a17Hints 6) 112 9 = true := by decide +kernel
theorem a17S6 (j : Nat) (hj : j < 121) : (checkRow a17 a17Domains a17Hints 6) j = true := by
  by_cases bound : j < 64
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a17S6P0 j (by omega) (by omega)
      ·
        exact segmentRange a17S6P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a17S6P2 j (by omega) (by omega)
      ·
        exact segmentRange a17S6P3 j (by omega) (by omega)
  ·
    by_cases bound : j < 96
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a17S6P4 j (by omega) (by omega)
      ·
        exact segmentRange a17S6P5 j (by omega) (by omega)
    ·
      by_cases bound : j < 112
      ·
        exact segmentRange a17S6P6 j (by omega) (by omega)
      ·
        exact segmentRange a17S6P7 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P0 : segment (checkRow a17 a17Domains a17Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S7P1 : segment (checkRow a17 a17Domains a17Hints 7) 16 14 = true := by decide +kernel
theorem a17S7 (j : Nat) (hj : j < 30) : (checkRow a17 a17Domains a17Hints 7) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a17S7P0 j (by omega) (by omega)
  ·
    exact segmentRange a17S7P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S8P0 : segment (checkRow a17 a17Domains a17Hints 8) 0 1 = true := by decide +kernel
theorem a17S8 (j : Nat) (hj : j < 1) : (checkRow a17 a17Domains a17Hints 8) j = true := by
  exact segmentRange a17S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Complete : Complete a17 a17Domains a17Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a17S5 j hj
  · exact a17S6 j hj
  · exact a17S7 j hj
  · exact a17S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S4P0 : segment (checkRow a18 a18Domains a18Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S4P1 : segment (checkRow a18 a18Domains a18Hints 4) 16 7 = true := by decide +kernel
theorem a18S4 (j : Nat) (hj : j < 23) : (checkRow a18 a18Domains a18Hints 4) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a18S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a18S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P0 : segment (checkRow a18 a18Domains a18Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P1 : segment (checkRow a18 a18Domains a18Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P2 : segment (checkRow a18 a18Domains a18Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P3 : segment (checkRow a18 a18Domains a18Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P4 : segment (checkRow a18 a18Domains a18Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P5 : segment (checkRow a18 a18Domains a18Hints 5) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P6 : segment (checkRow a18 a18Domains a18Hints 5) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P7 : segment (checkRow a18 a18Domains a18Hints 5) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P8 : segment (checkRow a18 a18Domains a18Hints 5) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P9 : segment (checkRow a18 a18Domains a18Hints 5) 144 2 = true := by decide +kernel
theorem a18S5 (j : Nat) (hj : j < 146) : (checkRow a18 a18Domains a18Hints 5) j = true := by
  by_cases bound : j < 80
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a18S5P0 j (by omega) (by omega)
      ·
        exact segmentRange a18S5P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a18S5P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 64
        ·
          exact segmentRange a18S5P3 j (by omega) (by omega)
        ·
          exact segmentRange a18S5P4 j (by omega) (by omega)
  ·
    by_cases bound : j < 112
    ·
      by_cases bound : j < 96
      ·
        exact segmentRange a18S5P5 j (by omega) (by omega)
      ·
        exact segmentRange a18S5P6 j (by omega) (by omega)
    ·
      by_cases bound : j < 128
      ·
        exact segmentRange a18S5P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 144
        ·
          exact segmentRange a18S5P8 j (by omega) (by omega)
        ·
          exact segmentRange a18S5P9 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P0 : segment (checkRow a18 a18Domains a18Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P1 : segment (checkRow a18 a18Domains a18Hints 6) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P2 : segment (checkRow a18 a18Domains a18Hints 6) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P3 : segment (checkRow a18 a18Domains a18Hints 6) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P4 : segment (checkRow a18 a18Domains a18Hints 6) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P5 : segment (checkRow a18 a18Domains a18Hints 6) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P6 : segment (checkRow a18 a18Domains a18Hints 6) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P7 : segment (checkRow a18 a18Domains a18Hints 6) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P8 : segment (checkRow a18 a18Domains a18Hints 6) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S6P9 : segment (checkRow a18 a18Domains a18Hints 6) 144 14 = true := by decide +kernel
theorem a18S6 (j : Nat) (hj : j < 158) : (checkRow a18 a18Domains a18Hints 6) j = true := by
  by_cases bound : j < 80
  ·
    by_cases bound : j < 32
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a18S6P0 j (by omega) (by omega)
      ·
        exact segmentRange a18S6P1 j (by omega) (by omega)
    ·
      by_cases bound : j < 48
      ·
        exact segmentRange a18S6P2 j (by omega) (by omega)
      ·
        by_cases bound : j < 64
        ·
          exact segmentRange a18S6P3 j (by omega) (by omega)
        ·
          exact segmentRange a18S6P4 j (by omega) (by omega)
  ·
    by_cases bound : j < 112
    ·
      by_cases bound : j < 96
      ·
        exact segmentRange a18S6P5 j (by omega) (by omega)
      ·
        exact segmentRange a18S6P6 j (by omega) (by omega)
    ·
      by_cases bound : j < 128
      ·
        exact segmentRange a18S6P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 144
        ·
          exact segmentRange a18S6P8 j (by omega) (by omega)
        ·
          exact segmentRange a18S6P9 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S7P0 : segment (checkRow a18 a18Domains a18Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S7P1 : segment (checkRow a18 a18Domains a18Hints 7) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S7P2 : segment (checkRow a18 a18Domains a18Hints 7) 32 2 = true := by decide +kernel
theorem a18S7 (j : Nat) (hj : j < 34) : (checkRow a18 a18Domains a18Hints 7) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a18S7P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 32
    ·
      exact segmentRange a18S7P1 j (by omega) (by omega)
    ·
      exact segmentRange a18S7P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S8P0 : segment (checkRow a18 a18Domains a18Hints 8) 0 1 = true := by decide +kernel
theorem a18S8 (j : Nat) (hj : j < 1) : (checkRow a18 a18Domains a18Hints 8) j = true := by
  exact segmentRange a18S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Complete : Complete a18 a18Domains a18Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a18S4 j hj
  · exact a18S5 j hj
  · exact a18S6 j hj
  · exact a18S7 j hj
  · exact a18S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S3P0 : segment (checkRow a19 a19Domains a19Hints 3) 0 2 = true := by decide +kernel
theorem a19S3 (j : Nat) (hj : j < 2) : (checkRow a19 a19Domains a19Hints 3) j = true := by
  exact segmentRange a19S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S4P0 : segment (checkRow a19 a19Domains a19Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S4P1 : segment (checkRow a19 a19Domains a19Hints 4) 16 6 = true := by decide +kernel
theorem a19S4 (j : Nat) (hj : j < 22) : (checkRow a19 a19Domains a19Hints 4) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a19S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a19S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P0 : segment (checkRow a19 a19Domains a19Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P1 : segment (checkRow a19 a19Domains a19Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P2 : segment (checkRow a19 a19Domains a19Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P3 : segment (checkRow a19 a19Domains a19Hints 5) 48 2 = true := by decide +kernel
theorem a19S5 (j : Nat) (hj : j < 50) : (checkRow a19 a19Domains a19Hints 5) j = true := by
  by_cases bound : j < 32
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a19S5P0 j (by omega) (by omega)
    ·
      exact segmentRange a19S5P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 48
    ·
      exact segmentRange a19S5P2 j (by omega) (by omega)
    ·
      exact segmentRange a19S5P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P0 : segment (checkRow a19 a19Domains a19Hints 6) 0 12 = true := by decide +kernel
theorem a19S6 (j : Nat) (hj : j < 12) : (checkRow a19 a19Domains a19Hints 6) j = true := by
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
  · exact a19S3 j hj
  · exact a19S4 j hj
  · exact a19S5 j hj
  · exact a19S6 j hj
  · exact a19S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20S4P0 : segment (checkRow a20 a20Domains a20Hints 4) 0 1 = true := by decide +kernel
theorem a20S4 (j : Nat) (hj : j < 1) : (checkRow a20 a20Domains a20Hints 4) j = true := by
  exact segmentRange a20S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20Complete : Complete a20 a20Domains a20Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a20S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21S4P0 : segment (checkRow a21 a21Domains a21Hints 4) 0 1 = true := by decide +kernel
theorem a21S4 (j : Nat) (hj : j < 1) : (checkRow a21 a21Domains a21Hints 4) j = true := by
  exact segmentRange a21S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21Complete : Complete a21 a21Domains a21Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a21S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S4P0 : segment (checkRow a22 a22Domains a22Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S4P1 : segment (checkRow a22 a22Domains a22Hints 4) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S4P2 : segment (checkRow a22 a22Domains a22Hints 4) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S4P3 : segment (checkRow a22 a22Domains a22Hints 4) 48 7 = true := by decide +kernel
theorem a22S4 (j : Nat) (hj : j < 55) : (checkRow a22 a22Domains a22Hints 4) j = true := by
  by_cases bound : j < 32
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a22S4P0 j (by omega) (by omega)
    ·
      exact segmentRange a22S4P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 48
    ·
      exact segmentRange a22S4P2 j (by omega) (by omega)
    ·
      exact segmentRange a22S4P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S5P0 : segment (checkRow a22 a22Domains a22Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S5P1 : segment (checkRow a22 a22Domains a22Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S5P2 : segment (checkRow a22 a22Domains a22Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S5P3 : segment (checkRow a22 a22Domains a22Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S5P4 : segment (checkRow a22 a22Domains a22Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S5P5 : segment (checkRow a22 a22Domains a22Hints 5) 80 5 = true := by decide +kernel
theorem a22S5 (j : Nat) (hj : j < 85) : (checkRow a22 a22Domains a22Hints 5) j = true := by
  by_cases bound : j < 48
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a22S5P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 32
      ·
        exact segmentRange a22S5P1 j (by omega) (by omega)
      ·
        exact segmentRange a22S5P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 64
    ·
      exact segmentRange a22S5P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a22S5P4 j (by omega) (by omega)
      ·
        exact segmentRange a22S5P5 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S6P0 : segment (checkRow a22 a22Domains a22Hints 6) 0 14 = true := by decide +kernel
theorem a22S6 (j : Nat) (hj : j < 14) : (checkRow a22 a22Domains a22Hints 6) j = true := by
  exact segmentRange a22S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22S7P0 : segment (checkRow a22 a22Domains a22Hints 7) 0 1 = true := by decide +kernel
theorem a22S7 (j : Nat) (hj : j < 1) : (checkRow a22 a22Domains a22Hints 7) j = true := by
  exact segmentRange a22S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22Complete : Complete a22 a22Domains a22Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a22S4 j hj
  · exact a22S5 j hj
  · exact a22S6 j hj
  · exact a22S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23S3P0 : segment (checkRow a23 a23Domains a23Hints 3) 0 1 = true := by decide +kernel
theorem a23S3 (j : Nat) (hj : j < 1) : (checkRow a23 a23Domains a23Hints 3) j = true := by
  exact segmentRange a23S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23S4P0 : segment (checkRow a23 a23Domains a23Hints 4) 0 4 = true := by decide +kernel
theorem a23S4 (j : Nat) (hj : j < 4) : (checkRow a23 a23Domains a23Hints 4) j = true := by
  exact segmentRange a23S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23S5P0 : segment (checkRow a23 a23Domains a23Hints 5) 0 1 = true := by decide +kernel
theorem a23S5 (j : Nat) (hj : j < 1) : (checkRow a23 a23Domains a23Hints 5) j = true := by
  exact segmentRange a23S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23Complete : Complete a23 a23Domains a23Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a23S3 j hj
  · exact a23S4 j hj
  · exact a23S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S3P0 : segment (checkRow a24 a24Domains a24Hints 3) 0 1 = true := by decide +kernel
theorem a24S3 (j : Nat) (hj : j < 1) : (checkRow a24 a24Domains a24Hints 3) j = true := by
  exact segmentRange a24S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S4P0 : segment (checkRow a24 a24Domains a24Hints 4) 0 14 = true := by decide +kernel
theorem a24S4 (j : Nat) (hj : j < 14) : (checkRow a24 a24Domains a24Hints 4) j = true := by
  exact segmentRange a24S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S5P0 : segment (checkRow a24 a24Domains a24Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S5P1 : segment (checkRow a24 a24Domains a24Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S5P2 : segment (checkRow a24 a24Domains a24Hints 5) 32 10 = true := by decide +kernel
theorem a24S5 (j : Nat) (hj : j < 42) : (checkRow a24 a24Domains a24Hints 5) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a24S5P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 32
    ·
      exact segmentRange a24S5P1 j (by omega) (by omega)
    ·
      exact segmentRange a24S5P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S6P0 : segment (checkRow a24 a24Domains a24Hints 6) 0 13 = true := by decide +kernel
theorem a24S6 (j : Nat) (hj : j < 13) : (checkRow a24 a24Domains a24Hints 6) j = true := by
  exact segmentRange a24S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24S7P0 : segment (checkRow a24 a24Domains a24Hints 7) 0 1 = true := by decide +kernel
theorem a24S7 (j : Nat) (hj : j < 1) : (checkRow a24 a24Domains a24Hints 7) j = true := by
  exact segmentRange a24S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24Complete : Complete a24 a24Domains a24Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a24S3 j hj
  · exact a24S4 j hj
  · exact a24S5 j hj
  · exact a24S6 j hj
  · exact a24S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25S6P0 : segment (checkRow a25 a25Domains a25Hints 6) 0 1 = true := by decide +kernel
theorem a25S6 (j : Nat) (hj : j < 1) : (checkRow a25 a25Domains a25Hints 6) j = true := by
  exact segmentRange a25S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25S7P0 : segment (checkRow a25 a25Domains a25Hints 7) 0 1 = true := by decide +kernel
theorem a25S7 (j : Nat) (hj : j < 1) : (checkRow a25 a25Domains a25Hints 7) j = true := by
  exact segmentRange a25S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25Complete : Complete a25 a25Domains a25Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a25S6 j hj
  · exact a25S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26S4P0 : segment (checkRow a26 a26Domains a26Hints 4) 0 2 = true := by decide +kernel
theorem a26S4 (j : Nat) (hj : j < 2) : (checkRow a26 a26Domains a26Hints 4) j = true := by
  exact segmentRange a26S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26S5P0 : segment (checkRow a26 a26Domains a26Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26S5P1 : segment (checkRow a26 a26Domains a26Hints 5) 16 5 = true := by decide +kernel
theorem a26S5 (j : Nat) (hj : j < 21) : (checkRow a26 a26Domains a26Hints 5) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a26S5P0 j (by omega) (by omega)
  ·
    exact segmentRange a26S5P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26S6P0 : segment (checkRow a26 a26Domains a26Hints 6) 0 12 = true := by decide +kernel
theorem a26S6 (j : Nat) (hj : j < 12) : (checkRow a26 a26Domains a26Hints 6) j = true := by
  exact segmentRange a26S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26S7P0 : segment (checkRow a26 a26Domains a26Hints 7) 0 1 = true := by decide +kernel
theorem a26S7 (j : Nat) (hj : j < 1) : (checkRow a26 a26Domains a26Hints 7) j = true := by
  exact segmentRange a26S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26Complete : Complete a26 a26Domains a26Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a26S4 j hj
  · exact a26S5 j hj
  · exact a26S6 j hj
  · exact a26S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27S6P0 : segment (checkRow a27 a27Domains a27Hints 6) 0 1 = true := by decide +kernel
theorem a27S6 (j : Nat) (hj : j < 1) : (checkRow a27 a27Domains a27Hints 6) j = true := by
  exact segmentRange a27S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27Complete : Complete a27 a27Domains a27Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a27S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28S6P0 : segment (checkRow a28 a28Domains a28Hints 6) 0 1 = true := by decide +kernel
theorem a28S6 (j : Nat) (hj : j < 1) : (checkRow a28 a28Domains a28Hints 6) j = true := by
  exact segmentRange a28S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28Complete : Complete a28 a28Domains a28Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a28S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29S6P0 : segment (checkRow a29 a29Domains a29Hints 6) 0 1 = true := by decide +kernel
theorem a29S6 (j : Nat) (hj : j < 1) : (checkRow a29 a29Domains a29Hints 6) j = true := by
  exact segmentRange a29S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29Complete : Complete a29 a29Domains a29Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a29S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30S4P0 : segment (checkRow a30 a30Domains a30Hints 4) 0 2 = true := by decide +kernel
theorem a30S4 (j : Nat) (hj : j < 2) : (checkRow a30 a30Domains a30Hints 4) j = true := by
  exact segmentRange a30S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30S5P0 : segment (checkRow a30 a30Domains a30Hints 5) 0 4 = true := by decide +kernel
theorem a30S5 (j : Nat) (hj : j < 4) : (checkRow a30 a30Domains a30Hints 5) j = true := by
  exact segmentRange a30S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30S6P0 : segment (checkRow a30 a30Domains a30Hints 6) 0 1 = true := by decide +kernel
theorem a30S6 (j : Nat) (hj : j < 1) : (checkRow a30 a30Domains a30Hints 6) j = true := by
  exact segmentRange a30S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30Complete : Complete a30 a30Domains a30Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a30S4 j hj
  · exact a30S5 j hj
  · exact a30S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a31S6P0 : segment (checkRow a31 a31Domains a31Hints 6) 0 1 = true := by decide +kernel
theorem a31S6 (j : Nat) (hj : j < 1) : (checkRow a31 a31Domains a31Hints 6) j = true := by
  exact segmentRange a31S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a31Complete : Complete a31 a31Domains a31Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a31S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32S4P0 : segment (checkRow a32 a32Domains a32Hints 4) 0 2 = true := by decide +kernel
theorem a32S4 (j : Nat) (hj : j < 2) : (checkRow a32 a32Domains a32Hints 4) j = true := by
  exact segmentRange a32S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32S5P0 : segment (checkRow a32 a32Domains a32Hints 5) 0 6 = true := by decide +kernel
theorem a32S5 (j : Nat) (hj : j < 6) : (checkRow a32 a32Domains a32Hints 5) j = true := by
  exact segmentRange a32S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32S6P0 : segment (checkRow a32 a32Domains a32Hints 6) 0 1 = true := by decide +kernel
theorem a32S6 (j : Nat) (hj : j < 1) : (checkRow a32 a32Domains a32Hints 6) j = true := by
  exact segmentRange a32S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32Complete : Complete a32 a32Domains a32Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a32S4 j hj
  · exact a32S5 j hj
  · exact a32S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33S4P0 : segment (checkRow a33 a33Domains a33Hints 4) 0 8 = true := by decide +kernel
theorem a33S4 (j : Nat) (hj : j < 8) : (checkRow a33 a33Domains a33Hints 4) j = true := by
  exact segmentRange a33S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33S5P0 : segment (checkRow a33 a33Domains a33Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33S5P1 : segment (checkRow a33 a33Domains a33Hints 5) 16 8 = true := by decide +kernel
theorem a33S5 (j : Nat) (hj : j < 24) : (checkRow a33 a33Domains a33Hints 5) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a33S5P0 j (by omega) (by omega)
  ·
    exact segmentRange a33S5P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33S6P0 : segment (checkRow a33 a33Domains a33Hints 6) 0 1 = true := by decide +kernel
theorem a33S6 (j : Nat) (hj : j < 1) : (checkRow a33 a33Domains a33Hints 6) j = true := by
  exact segmentRange a33S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33Complete : Complete a33 a33Domains a33Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a33S4 j hj
  · exact a33S5 j hj
  · exact a33S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a34S5P0 : segment (checkRow a34 a34Domains a34Hints 5) 0 1 = true := by decide +kernel
theorem a34S5 (j : Nat) (hj : j < 1) : (checkRow a34 a34Domains a34Hints 5) j = true := by
  exact segmentRange a34S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a34Complete : Complete a34 a34Domains a34Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a34S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a35S5P0 : segment (checkRow a35 a35Domains a35Hints 5) 0 1 = true := by decide +kernel
theorem a35S5 (j : Nat) (hj : j < 1) : (checkRow a35 a35Domains a35Hints 5) j = true := by
  exact segmentRange a35S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a35Complete : Complete a35 a35Domains a35Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a35S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a36S5P0 : segment (checkRow a36 a36Domains a36Hints 5) 0 1 = true := by decide +kernel
theorem a36S5 (j : Nat) (hj : j < 1) : (checkRow a36 a36Domains a36Hints 5) j = true := by
  exact segmentRange a36S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a36Complete : Complete a36 a36Domains a36Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a36S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a37S5P0 : segment (checkRow a37 a37Domains a37Hints 5) 0 1 = true := by decide +kernel
theorem a37S5 (j : Nat) (hj : j < 1) : (checkRow a37 a37Domains a37Hints 5) j = true := by
  exact segmentRange a37S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a37Complete : Complete a37 a37Domains a37Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a37S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a38S5P0 : segment (checkRow a38 a38Domains a38Hints 5) 0 1 = true := by decide +kernel
theorem a38S5 (j : Nat) (hj : j < 1) : (checkRow a38 a38Domains a38Hints 5) j = true := by
  exact segmentRange a38S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a38Complete : Complete a38 a38Domains a38Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a38S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a39S4P0 : segment (checkRow a39 a39Domains a39Hints 4) 0 1 = true := by decide +kernel
theorem a39S4 (j : Nat) (hj : j < 1) : (checkRow a39 a39Domains a39Hints 4) j = true := by
  exact segmentRange a39S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a39Complete : Complete a39 a39Domains a39Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a39S4 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S5P0 : segment (checkRow a40 a40Domains a40Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S5P1 : segment (checkRow a40 a40Domains a40Hints 5) 16 2 = true := by decide +kernel
theorem a40S5 (j : Nat) (hj : j < 18) : (checkRow a40 a40Domains a40Hints 5) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a40S5P0 j (by omega) (by omega)
  ·
    exact segmentRange a40S5P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P0 : segment (checkRow a40 a40Domains a40Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P1 : segment (checkRow a40 a40Domains a40Hints 6) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P2 : segment (checkRow a40 a40Domains a40Hints 6) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P3 : segment (checkRow a40 a40Domains a40Hints 6) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P4 : segment (checkRow a40 a40Domains a40Hints 6) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P5 : segment (checkRow a40 a40Domains a40Hints 6) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P6 : segment (checkRow a40 a40Domains a40Hints 6) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P7 : segment (checkRow a40 a40Domains a40Hints 6) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P8 : segment (checkRow a40 a40Domains a40Hints 6) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P9 : segment (checkRow a40 a40Domains a40Hints 6) 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P10 : segment (checkRow a40 a40Domains a40Hints 6) 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P11 : segment (checkRow a40 a40Domains a40Hints 6) 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S6P12 : segment (checkRow a40 a40Domains a40Hints 6) 192 15 = true := by decide +kernel
theorem a40S6 (j : Nat) (hj : j < 207) : (checkRow a40 a40Domains a40Hints 6) j = true := by
  by_cases bound : j < 96
  ·
    by_cases bound : j < 48
    ·
      by_cases bound : j < 16
      ·
        exact segmentRange a40S6P0 j (by omega) (by omega)
      ·
        by_cases bound : j < 32
        ·
          exact segmentRange a40S6P1 j (by omega) (by omega)
        ·
          exact segmentRange a40S6P2 j (by omega) (by omega)
    ·
      by_cases bound : j < 64
      ·
        exact segmentRange a40S6P3 j (by omega) (by omega)
      ·
        by_cases bound : j < 80
        ·
          exact segmentRange a40S6P4 j (by omega) (by omega)
        ·
          exact segmentRange a40S6P5 j (by omega) (by omega)
  ·
    by_cases bound : j < 144
    ·
      by_cases bound : j < 112
      ·
        exact segmentRange a40S6P6 j (by omega) (by omega)
      ·
        by_cases bound : j < 128
        ·
          exact segmentRange a40S6P7 j (by omega) (by omega)
        ·
          exact segmentRange a40S6P8 j (by omega) (by omega)
    ·
      by_cases bound : j < 176
      ·
        by_cases bound : j < 160
        ·
          exact segmentRange a40S6P9 j (by omega) (by omega)
        ·
          exact segmentRange a40S6P10 j (by omega) (by omega)
      ·
        by_cases bound : j < 192
        ·
          exact segmentRange a40S6P11 j (by omega) (by omega)
        ·
          exact segmentRange a40S6P12 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P0 : segment (checkRow a40 a40Domains a40Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P1 : segment (checkRow a40 a40Domains a40Hints 7) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P2 : segment (checkRow a40 a40Domains a40Hints 7) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P3 : segment (checkRow a40 a40Domains a40Hints 7) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P4 : segment (checkRow a40 a40Domains a40Hints 7) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P5 : segment (checkRow a40 a40Domains a40Hints 7) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P6 : segment (checkRow a40 a40Domains a40Hints 7) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P7 : segment (checkRow a40 a40Domains a40Hints 7) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P8 : segment (checkRow a40 a40Domains a40Hints 7) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P9 : segment (checkRow a40 a40Domains a40Hints 7) 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P10 : segment (checkRow a40 a40Domains a40Hints 7) 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P11 : segment (checkRow a40 a40Domains a40Hints 7) 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P12 : segment (checkRow a40 a40Domains a40Hints 7) 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P13 : segment (checkRow a40 a40Domains a40Hints 7) 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P14 : segment (checkRow a40 a40Domains a40Hints 7) 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P15 : segment (checkRow a40 a40Domains a40Hints 7) 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P16 : segment (checkRow a40 a40Domains a40Hints 7) 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P17 : segment (checkRow a40 a40Domains a40Hints 7) 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P18 : segment (checkRow a40 a40Domains a40Hints 7) 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P19 : segment (checkRow a40 a40Domains a40Hints 7) 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P20 : segment (checkRow a40 a40Domains a40Hints 7) 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P21 : segment (checkRow a40 a40Domains a40Hints 7) 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P22 : segment (checkRow a40 a40Domains a40Hints 7) 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P23 : segment (checkRow a40 a40Domains a40Hints 7) 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P24 : segment (checkRow a40 a40Domains a40Hints 7) 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P25 : segment (checkRow a40 a40Domains a40Hints 7) 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P26 : segment (checkRow a40 a40Domains a40Hints 7) 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P27 : segment (checkRow a40 a40Domains a40Hints 7) 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P28 : segment (checkRow a40 a40Domains a40Hints 7) 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P29 : segment (checkRow a40 a40Domains a40Hints 7) 464 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P30 : segment (checkRow a40 a40Domains a40Hints 7) 480 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P31 : segment (checkRow a40 a40Domains a40Hints 7) 496 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S7P32 : segment (checkRow a40 a40Domains a40Hints 7) 512 7 = true := by decide +kernel
theorem a40S7 (j : Nat) (hj : j < 519) : (checkRow a40 a40Domains a40Hints 7) j = true := by
  by_cases bound : j < 256
  ·
    by_cases bound : j < 128
    ·
      by_cases bound : j < 64
      ·
        by_cases bound : j < 32
        ·
          by_cases bound : j < 16
          ·
            exact segmentRange a40S7P0 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P1 j (by omega) (by omega)
        ·
          by_cases bound : j < 48
          ·
            exact segmentRange a40S7P2 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P3 j (by omega) (by omega)
      ·
        by_cases bound : j < 96
        ·
          by_cases bound : j < 80
          ·
            exact segmentRange a40S7P4 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P5 j (by omega) (by omega)
        ·
          by_cases bound : j < 112
          ·
            exact segmentRange a40S7P6 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P7 j (by omega) (by omega)
    ·
      by_cases bound : j < 192
      ·
        by_cases bound : j < 160
        ·
          by_cases bound : j < 144
          ·
            exact segmentRange a40S7P8 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P9 j (by omega) (by omega)
        ·
          by_cases bound : j < 176
          ·
            exact segmentRange a40S7P10 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P11 j (by omega) (by omega)
      ·
        by_cases bound : j < 224
        ·
          by_cases bound : j < 208
          ·
            exact segmentRange a40S7P12 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P13 j (by omega) (by omega)
        ·
          by_cases bound : j < 240
          ·
            exact segmentRange a40S7P14 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P15 j (by omega) (by omega)
  ·
    by_cases bound : j < 384
    ·
      by_cases bound : j < 320
      ·
        by_cases bound : j < 288
        ·
          by_cases bound : j < 272
          ·
            exact segmentRange a40S7P16 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P17 j (by omega) (by omega)
        ·
          by_cases bound : j < 304
          ·
            exact segmentRange a40S7P18 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P19 j (by omega) (by omega)
      ·
        by_cases bound : j < 352
        ·
          by_cases bound : j < 336
          ·
            exact segmentRange a40S7P20 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P21 j (by omega) (by omega)
        ·
          by_cases bound : j < 368
          ·
            exact segmentRange a40S7P22 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P23 j (by omega) (by omega)
    ·
      by_cases bound : j < 448
      ·
        by_cases bound : j < 416
        ·
          by_cases bound : j < 400
          ·
            exact segmentRange a40S7P24 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P25 j (by omega) (by omega)
        ·
          by_cases bound : j < 432
          ·
            exact segmentRange a40S7P26 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P27 j (by omega) (by omega)
      ·
        by_cases bound : j < 480
        ·
          by_cases bound : j < 464
          ·
            exact segmentRange a40S7P28 j (by omega) (by omega)
          ·
            exact segmentRange a40S7P29 j (by omega) (by omega)
        ·
          by_cases bound : j < 496
          ·
            exact segmentRange a40S7P30 j (by omega) (by omega)
          ·
            by_cases bound : j < 512
            ·
              exact segmentRange a40S7P31 j (by omega) (by omega)
            ·
              exact segmentRange a40S7P32 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P0 : segment (checkRow a40 a40Domains a40Hints 8) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P1 : segment (checkRow a40 a40Domains a40Hints 8) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P2 : segment (checkRow a40 a40Domains a40Hints 8) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P3 : segment (checkRow a40 a40Domains a40Hints 8) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P4 : segment (checkRow a40 a40Domains a40Hints 8) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P5 : segment (checkRow a40 a40Domains a40Hints 8) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P6 : segment (checkRow a40 a40Domains a40Hints 8) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P7 : segment (checkRow a40 a40Domains a40Hints 8) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P8 : segment (checkRow a40 a40Domains a40Hints 8) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P9 : segment (checkRow a40 a40Domains a40Hints 8) 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P10 : segment (checkRow a40 a40Domains a40Hints 8) 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P11 : segment (checkRow a40 a40Domains a40Hints 8) 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P12 : segment (checkRow a40 a40Domains a40Hints 8) 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P13 : segment (checkRow a40 a40Domains a40Hints 8) 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P14 : segment (checkRow a40 a40Domains a40Hints 8) 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P15 : segment (checkRow a40 a40Domains a40Hints 8) 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P16 : segment (checkRow a40 a40Domains a40Hints 8) 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P17 : segment (checkRow a40 a40Domains a40Hints 8) 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S8P18 : segment (checkRow a40 a40Domains a40Hints 8) 288 16 = true := by decide +kernel
theorem a40S8 (j : Nat) (hj : j < 304) : (checkRow a40 a40Domains a40Hints 8) j = true := by
  by_cases bound : j < 144
  ·
    by_cases bound : j < 64
    ·
      by_cases bound : j < 32
      ·
        by_cases bound : j < 16
        ·
          exact segmentRange a40S8P0 j (by omega) (by omega)
        ·
          exact segmentRange a40S8P1 j (by omega) (by omega)
      ·
        by_cases bound : j < 48
        ·
          exact segmentRange a40S8P2 j (by omega) (by omega)
        ·
          exact segmentRange a40S8P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 96
      ·
        by_cases bound : j < 80
        ·
          exact segmentRange a40S8P4 j (by omega) (by omega)
        ·
          exact segmentRange a40S8P5 j (by omega) (by omega)
      ·
        by_cases bound : j < 112
        ·
          exact segmentRange a40S8P6 j (by omega) (by omega)
        ·
          by_cases bound : j < 128
          ·
            exact segmentRange a40S8P7 j (by omega) (by omega)
          ·
            exact segmentRange a40S8P8 j (by omega) (by omega)
  ·
    by_cases bound : j < 224
    ·
      by_cases bound : j < 176
      ·
        by_cases bound : j < 160
        ·
          exact segmentRange a40S8P9 j (by omega) (by omega)
        ·
          exact segmentRange a40S8P10 j (by omega) (by omega)
      ·
        by_cases bound : j < 192
        ·
          exact segmentRange a40S8P11 j (by omega) (by omega)
        ·
          by_cases bound : j < 208
          ·
            exact segmentRange a40S8P12 j (by omega) (by omega)
          ·
            exact segmentRange a40S8P13 j (by omega) (by omega)
    ·
      by_cases bound : j < 256
      ·
        by_cases bound : j < 240
        ·
          exact segmentRange a40S8P14 j (by omega) (by omega)
        ·
          exact segmentRange a40S8P15 j (by omega) (by omega)
      ·
        by_cases bound : j < 272
        ·
          exact segmentRange a40S8P16 j (by omega) (by omega)
        ·
          by_cases bound : j < 288
          ·
            exact segmentRange a40S8P17 j (by omega) (by omega)
          ·
            exact segmentRange a40S8P18 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S9P0 : segment (checkRow a40 a40Domains a40Hints 9) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S9P1 : segment (checkRow a40 a40Domains a40Hints 9) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S9P2 : segment (checkRow a40 a40Domains a40Hints 9) 32 11 = true := by decide +kernel
theorem a40S9 (j : Nat) (hj : j < 43) : (checkRow a40 a40Domains a40Hints 9) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a40S9P0 j (by omega) (by omega)
  ·
    by_cases bound : j < 32
    ·
      exact segmentRange a40S9P1 j (by omega) (by omega)
    ·
      exact segmentRange a40S9P2 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40S10P0 : segment (checkRow a40 a40Domains a40Hints 10) 0 1 = true := by decide +kernel
theorem a40S10 (j : Nat) (hj : j < 1) : (checkRow a40 a40Domains a40Hints 10) j = true := by
  exact segmentRange a40S10P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40Complete : Complete a40 a40Domains a40Hints := by
  intro k hk j hj
  change k ≤ 10 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a40S5 j hj
  · exact a40S6 j hj
  · exact a40S7 j hj
  · exact a40S8 j hj
  · exact a40S9 j hj
  · exact a40S10 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a0Bound : Lower true (roots a0) (target a0) 4 := by
  have ready : Ready a0 a0Domains (asRow a0Pos) (asRow a0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a0
  exact frozen ready a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 0, 4), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Bound : Lower true (roots a1) (target a1) 4 := by
  have ready : Ready a1 a1Domains (asRow a1Pos) (asRow a1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a1
  exact frozen ready a1Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 32, 36), (inputs.getD 3 zero, 32, 40), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Bound : Lower true (roots a2) (target a2) 3 := by
  have ready : Ready a2 a2Domains (asRow a2Pos) (asRow a2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a2
  exact frozen ready a2Complete (by decide +kernel) (by decide) [(inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D0 : Slice true (roots a3) (target a3) (repeatWord 17361641481138401520) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66, flipInput 4] ++ fixRows 0 4)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D1 : Slice true (roots a3) (target a3) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67, flipInput 4] ++ fixRows 0 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D2 : Slice true (roots a3) (target a3) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a1) (G := (target a1)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a1Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D3 : Slice true (roots a3) (target a3) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 84, flipInput 2, flipInput 4] ++ fixRows 0 32)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D4 : Slice true (roots a3) (target a3) (repeatWord 281470681743360) 3 :=
  signedSlice (ms := ([swapRows 50, swapRows 67] ++ fixRows 16 32)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Bound : Lower true (roots a3) (target a3) 7 := by
  have ready : Ready a3 a3Domains (asRow a3Pos) (asRow a3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a3D0 (safeCons a3D1 (safeCons a3D2 (safeCons a3D3 (safeCons a3D4 (safeNil a3)))))
  exact frozen ready a3Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 20, 28), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Bound : Lower true (roots a4) (target a4) 4 := by
  have ready : Ready a4 a4Domains (asRow a4Pos) (asRow a4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a4
  exact frozen ready a4Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 32, 36), (inputs.getD 3 zero, 0, 8), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Bound : Lower true (roots a5) (target a5) 3 := by
  have ready : Ready a5 a5Domains (asRow a5Pos) (asRow a5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a5
  exact frozen ready a5Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D0 : Slice true (roots a6) (target a6) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 84, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 4 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D1 : Slice true (roots a6) (target a6) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67, flipInput 2] ++ fixRows 0 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D2 : Slice true (roots a6) (target a6) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 2, flipInput 3] ++ fixRows 0 32)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D3 : Slice true (roots a6) (target a6) (repeatWord 17298308644996116495) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D4 : Slice true (roots a6) (target a6) (repeatWord 281474976645120) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 4 5 true)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D5 : Slice true (roots a6) (target a6) (repeatWord 4294967295) 3 :=
  signedSlice (ms := ([swapRows 83] ++ fixRows 32 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D6 : Slice true (roots a6) (target a6) (repeatWord 1085102592318504960) 3 :=
  signedSlice (ms := ([] ++ fixRows 4 32)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Bound : Lower true (roots a6) (target a6) 7 := by
  have ready : Ready a6 a6Domains (asRow a6Pos) (asRow a6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a6D0 (safeCons a6D1 (safeCons a6D2 (safeCons a6D3 (safeCons a6D4 (safeCons a6D5 (safeCons a6D6 (safeNil a6)))))))
  exact frozen ready a6Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D0 : Slice true (roots a7) (target a7) (repeatWord 17298308644996116495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D1 : Slice true (roots a7) (target a7) (repeatWord 17361393124654452495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D2 : Slice true (roots a7) (target a7) (repeatWord 17361641477348724495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D3 : Slice true (roots a7) (target a7) (repeatWord 18374687579166474495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D4 : Slice true (roots a7) (target a7) (repeatWord 18374966855153418495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67] ++ fixRows 0 0 ++ identifyRows 3 5 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D5 : Slice true (roots a7) (target a7) (repeatWord 18446462598732906495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Bound : Lower true (roots a7) (target a7) 6 := by
  have ready : Ready a7 a7Domains (asRow a7Pos) (asRow a7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a7D0 (safeCons a7D1 (safeCons a7D2 (safeCons a7D3 (safeCons a7D4 (safeCons a7D5 (safeNil a7))))))
  exact frozen ready a7Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D0 : Slice true (roots a8) (target a8) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 84, flipInput 3] ++ fixRows 0 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D1 : Slice true (roots a8) (target a8) (repeatWord 17361641477348724495) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D2 : Slice true (roots a8) (target a8) (repeatWord 71777214294589695) 3 :=
  signedSlice (ms := ([swapRows 66] ++ fixRows 8 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D3 : Slice true (roots a8) (target a8) (repeatWord 281470681808895) 3 :=
  signedSlice (ms := ([swapRows 66, swapRows 67] ++ fixRows 16 0)) (base := roots a5) (G := (target a5)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a5Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Bound : Lower true (roots a8) (target a8) 6 := by
  have ready : Ready a8 a8Domains (asRow a8Pos) (asRow a8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a8D0 (safeCons a8D1 (safeCons a8D2 (safeCons a8D3 (safeNil a8))))
  exact frozen ready a8Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D0 : Slice true (roots a9) (target a9) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 67] ++ fixRows 4 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Bound : Lower true (roots a9) (target a9) 6 := by
  have ready : Ready a9 a9Domains (asRow a9Pos) (asRow a9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a9D0 (safeNil a9)
  exact frozen ready a9Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D0 : Slice true (roots a10) (target a10) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 67] ++ fixRows 4 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Bound : Lower true (roots a10) (target a10) 5 := by
  have ready : Ready a10 a10Domains (asRow a10Pos) (asRow a10Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a10D0 (safeNil a10)
  exact frozen ready a10Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D0 : Slice true (roots a11) (target a11) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 0 32)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Bound : Lower true (roots a11) (target a11) 5 := by
  have ready : Ready a11 a11Domains (asRow a11Pos) (asRow a11Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a11D0 (safeNil a11)
  exact frozen ready a11Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 36, 38), (inputs.getD 2 zero, 34, 38), (inputs.getD 3 zero, 34, 42), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D0 : Slice true (roots a12) (target a12) (repeatWord 18446744069414584320) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, flipInput 0, flipInput 2] ++ fixRows 0 32)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Bound : Lower true (roots a12) (target a12) 5 := by
  have ready : Ready a12 a12Domains (asRow a12Pos) (asRow a12Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a12D0 (safeNil a12)
  exact frozen ready a12Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 33, 37), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D0 : Slice true (roots a13) (target a13) (repeatWord 14757395258967641292) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 67] ++ fixRows 0 2)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Bound : Lower true (roots a13) (target a13) 5 := by
  have ready : Ready a13 a13Domains (asRow a13Pos) (asRow a13Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a13D0 (safeNil a13)
  exact frozen ready a13Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 16, 18), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Bound : Lower true (roots a14) (target a14) 4 := by
  have ready : Ready a14 a14Domains (asRow a14Pos) (asRow a14Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a14
  exact frozen ready a14Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Bound : Lower true (roots a15) (target a15) 4 := by
  have ready : Ready a15 a15Domains (asRow a15Pos) (asRow a15Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a15
  exact frozen ready a15Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D0 : Slice true (roots a16) (target a16) (repeatWord 4340410370284600380) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D1 : Slice true (roots a16) (target a16) (repeatWord 3689517697150995660) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D2 : Slice true (roots a16) (target a16) (repeatWord 18374966859414961920) 6 :=
  signedSlice (ms := ([swapRows 81, swapRows 83, swapRows 84, flipInput 1] ++ fixRows 0 8)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D3 : Slice true (roots a16) (target a16) (repeatWord 18446744069414584320) 6 :=
  signedSlice (ms := ([swapRows 81, swapRows 50, flipInput 1] ++ fixRows 0 32)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D4 : Slice true (roots a16) (target a16) (repeatWord 17361393124654452495) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 65, swapRows 50, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a9) (G := (neg (target a9))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a9Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D5 : Slice true (roots a16) (target a16) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 84, flipInput 2, flipInput 5] ++ fixRows 2 0)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D6 : Slice true (roots a16) (target a16) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 81, swapRows 66, swapRows 83, flipInput 1, flipInput 3] ++ fixRows 0 4)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D7 : Slice true (roots a16) (target a16) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 50] ++ fixRows 16 0)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D8 : Slice true (roots a16) (target a16) (repeatWord 14714328930390887475) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D9 : Slice true (roots a16) (target a16) (repeatWord 1148435428713435120) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, swapRows 83, swapRows 84] ++ fixRows 0 0 ++ identifyRows 2 3 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D10 : Slice true (roots a16) (target a16) (repeatWord 18446462598732906495) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 65, swapRows 82, swapRows 67, flipInput 1, flipInput 5] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D11 : Slice true (roots a16) (target a16) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 82, swapRows 67, swapRows 84, flipInput 1, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 4 0)) (base := roots a14) (G := (neg (target a14))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a14Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D12 : Slice true (roots a16) (target a16) (repeatWord 4294967295) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, swapRows 83, swapRows 84] ++ fixRows 32 0)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D13 : Slice true (roots a16) (target a16) (repeatWord 3472328296227680304) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66, flipInput 4] ++ fixRows 2 4)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D14 : Slice true (roots a16) (target a16) (repeatWord 3689348813882916864) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 84, flipInput 2] ++ fixRows 2 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D15 : Slice true (roots a16) (target a16) (repeatWord 1085102592318504960) 3 :=
  signedSlice (ms := ([swapRows 33, swapRows 67, swapRows 84, flipInput 1, flipInput 3] ++ fixRows 4 32)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D16 : Slice true (roots a16) (target a16) (repeatWord 281470681743360) 3 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 67, swapRows 84, flipInput 1, flipInput 3] ++ fixRows 16 32)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Bound : Lower true (roots a16) (target a16) 9 := by
  have ready : Ready a16 a16Domains (asRow a16Pos) (asRow a16Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a16D0 (safeCons a16D1 (safeCons a16D2 (safeCons a16D3 (safeCons a16D4 (safeCons a16D5 (safeCons a16D6 (safeCons a16D7 (safeCons a16D8 (safeCons a16D9 (safeCons a16D10 (safeCons a16D11 (safeCons a16D12 (safeCons a16D13 (safeCons a16D14 (safeCons a16D15 (safeCons a16D16 (safeNil a16)))))))))))))))))
  exact frozen ready a16Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D0 : Slice true (roots a17) (target a17) (repeatWord 6172840429334713770) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D1 : Slice true (roots a17) (target a17) (repeatWord 17361641481138401520) 6 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 83, swapRows 84, flipInput 0] ++ fixRows 0 4)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D2 : Slice true (roots a17) (target a17) (repeatWord 6149008514797120170) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, flipInput 2, flipInput 3] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a9) (G := (neg (target a9))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a9Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D3 : Slice true (roots a17) (target a17) (repeatWord 12297829381041378645) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D4 : Slice true (roots a17) (target a17) (repeatWord 18374687579166474495) 6 :=
  signedSlice (ms := ([swapRows 64, flipInput 0, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a9) (G := (neg (target a9))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a9Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D5 : Slice true (roots a17) (target a17) (repeatWord 71777218556133120) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 3 5 true)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D6 : Slice true (roots a17) (target a17) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 83, flipInput 4, flipInput 5] ++ fixRows 1 0)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D7 : Slice true (roots a17) (target a17) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 4 0)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D8 : Slice true (roots a17) (target a17) (repeatWord 18374966859414961920) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 67, swapRows 84, flipInput 0, flipInput 2] ++ fixRows 0 8)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D9 : Slice true (roots a17) (target a17) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D10 : Slice true (roots a17) (target a17) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 67, swapRows 84, flipInput 2, flipInput 4] ++ fixRows 32 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D11 : Slice true (roots a17) (target a17) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 84, flipInput 0, flipInput 3, flipInput 4] ++ fixRows 0 32)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D12 : Slice true (roots a17) (target a17) (repeatWord 6124988953138320640) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67, flipInput 4] ++ fixRows 1 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D13 : Slice true (roots a17) (target a17) (repeatWord 252645135) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 84, flipInput 0, flipInput 3] ++ fixRows 36 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D14 : Slice true (roots a17) (target a17) (repeatWord 281470681743360) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, flipInput 0, flipInput 2] ++ fixRows 16 32)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Bound : Lower true (roots a17) (target a17) 9 := by
  have ready : Ready a17 a17Domains (asRow a17Pos) (asRow a17Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a17D0 (safeCons a17D1 (safeCons a17D2 (safeCons a17D3 (safeCons a17D4 (safeCons a17D5 (safeCons a17D6 (safeCons a17D7 (safeCons a17D8 (safeCons a17D9 (safeCons a17D10 (safeCons a17D11 (safeCons a17D12 (safeCons a17D13 (safeCons a17D14 (safeNil a17)))))))))))))))
  exact frozen ready a17Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D0 : Slice true (roots a18) (target a18) (repeatWord 18446744069414584320) 6 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, flipInput 0] ++ fixRows 0 32)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D1 : Slice true (roots a18) (target a18) (repeatWord 6510615555426900570) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D2 : Slice true (roots a18) (target a18) (repeatWord 6148914692668172970) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D3 : Slice true (roots a18) (target a18) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 1 0)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D4 : Slice true (roots a18) (target a18) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 4, flipInput 5] ++ fixRows 4 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D5 : Slice true (roots a18) (target a18) (repeatWord 18374966859414961920) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 67, swapRows 84, flipInput 0, flipInput 5] ++ fixRows 0 8)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D6 : Slice true (roots a18) (target a18) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 83, flipInput 0, flipInput 5] ++ fixRows 0 16)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D7 : Slice true (roots a18) (target a18) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, swapRows 83, swapRows 84, flipInput 2] ++ fixRows 32 0)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D8 : Slice true (roots a18) (target a18) (repeatWord 17298308644996116495) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 3] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D9 : Slice true (roots a18) (target a18) (repeatWord 17361393124654452495) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 50, swapRows 83, flipInput 0, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D10 : Slice true (roots a18) (target a18) (repeatWord 18374687579166474495) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 84, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D11 : Slice true (roots a18) (target a18) (repeatWord 71777214294589695) 4 :=
  signedSlice (ms := ([swapRows 67] ++ fixRows 8 0)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D12 : Slice true (roots a18) (target a18) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D13 : Slice true (roots a18) (target a18) (repeatWord 6124988953138320640) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67] ++ fixRows 1 8)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D14 : Slice true (roots a18) (target a18) (repeatWord 6148820867675914240) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50] ++ fixRows 1 16)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D15 : Slice true (roots a18) (target a18) (repeatWord 252645135) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 84, flipInput 0, flipInput 3] ++ fixRows 36 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Bound : Lower true (roots a18) (target a18) 9 := by
  have ready : Ready a18 a18Domains (asRow a18Pos) (asRow a18Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a18D0 (safeCons a18D1 (safeCons a18D2 (safeCons a18D3 (safeCons a18D4 (safeCons a18D5 (safeCons a18D6 (safeCons a18D7 (safeCons a18D8 (safeCons a18D9 (safeCons a18D10 (safeCons a18D11 (safeCons a18D12 (safeCons a18D13 (safeCons a18D14 (safeCons a18D15 (safeNil a18))))))))))))))))
  exact frozen ready a18Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D0 : Slice true (roots a19) (target a19) (repeatWord 18374966859414961920) 6 :=
  signedSlice (ms := ([swapRows 81, swapRows 83, swapRows 84, flipInput 1] ++ fixRows 0 8)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D1 : Slice true (roots a19) (target a19) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 16)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D2 : Slice true (roots a19) (target a19) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, flipInput 3] ++ fixRows 0 32)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D3 : Slice true (roots a19) (target a19) (repeatWord 4340410370284600380) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 83, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D4 : Slice true (roots a19) (target a19) (repeatWord 3689517697150995660) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 84, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D5 : Slice true (roots a19) (target a19) (repeatWord 3689348817318890700) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D6 : Slice true (roots a19) (target a19) (repeatWord 17361393124654452495) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, swapRows 84, flipInput 1, flipInput 3, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D7 : Slice true (roots a19) (target a19) (repeatWord 17361641477348724495) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 50, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D8 : Slice true (roots a19) (target a19) (repeatWord 18446462598732840960) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 0 48)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19Bound : Lower true (roots a19) (target a19) 8 := by
  have ready : Ready a19 a19Domains (asRow a19Pos) (asRow a19Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a19D0 (safeCons a19D1 (safeCons a19D2 (safeCons a19D3 (safeCons a19D4 (safeCons a19D5 (safeCons a19D6 (safeCons a19D7 (safeCons a19D8 (safeNil a19)))))))))
  exact frozen ready a19Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 18, 26), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20D0 : Slice true (roots a20) (target a20) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 33, flipInput 1, flipInput 5] ++ fixRows 16 0)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a20Bound : Lower true (roots a20) (target a20) 5 := by
  have ready : Ready a20 a20Domains (asRow a20Pos) (asRow a20Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a20D0 (safeNil a20)
  exact frozen ready a20Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21D0 : Slice true (roots a21) (target a21) (repeatWord 71777214294589695) 4 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 8 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a21Bound : Lower true (roots a21) (target a21) 5 := by
  have ready : Ready a21 a21Domains (asRow a21Pos) (asRow a21Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a21D0 (safeNil a21)
  exact frozen ready a21Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D0 : Slice true (roots a22) (target a22) (repeatWord 4294967295) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, flipInput 2] ++ fixRows 32 0)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D1 : Slice true (roots a22) (target a22) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 65, swapRows 50, swapRows 84, flipInput 3, flipInput 5] ++ fixRows 4 0)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D2 : Slice true (roots a22) (target a22) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 16 0)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D3 : Slice true (roots a22) (target a22) (repeatWord 4340410370284600380) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D4 : Slice true (roots a22) (target a22) (repeatWord 14714328930390887475) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 66, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D5 : Slice true (roots a22) (target a22) (repeatWord 3689348817318890700) 5 :=
  signedSlice (ms := ([swapRows 65, swapRows 82, swapRows 67, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D6 : Slice true (roots a22) (target a22) (repeatWord 1148435428713435120) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 3 true)) (base := roots a20) (G := (target a20)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a20Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D7 : Slice true (roots a22) (target a22) (repeatWord 1085350949055099120) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a21) (G := (target a21)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a21Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D8 : Slice true (roots a22) (target a22) (repeatWord 71777218556133120) 5 :=
  signedSlice (ms := ([swapRows 82, swapRows 67, swapRows 84, flipInput 1, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 3 5 true)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D9 : Slice true (roots a22) (target a22) (repeatWord 71777214294589695) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 65, swapRows 66, swapRows 83] ++ fixRows 8 0)) (base := roots a14) (G := (target a14)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a14Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D10 : Slice true (roots a22) (target a22) (repeatWord 16711935) 3 :=
  signedSlice (ms := ([swapRows 65, swapRows 67, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 40 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22D11 : Slice true (roots a22) (target a22) (repeatWord 65535) 3 :=
  signedSlice (ms := ([swapRows 65, swapRows 83, flipInput 1, flipInput 2] ++ fixRows 48 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a22Bound : Lower true (roots a22) (target a22) 8 := by
  have ready : Ready a22 a22Domains (asRow a22Pos) (asRow a22Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a22D0 (safeCons a22D1 (safeCons a22D2 (safeCons a22D3 (safeCons a22D4 (safeCons a22D5 (safeCons a22D6 (safeCons a22D7 (safeCons a22D8 (safeCons a22D9 (safeCons a22D10 (safeCons a22D11 (safeNil a22))))))))))))
  exact frozen ready a22Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23D0 : Slice true (roots a23) (target a23) (repeatWord 4294967295) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 84, flipInput 4] ++ fixRows 32 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23D1 : Slice true (roots a23) (target a23) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 2, flipInput 3] ++ fixRows 0 32)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23D2 : Slice true (roots a23) (target a23) (repeatWord 17298308644996116495) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23D3 : Slice true (roots a23) (target a23) (repeatWord 18374687579166474495) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 67, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23D4 : Slice true (roots a23) (target a23) (repeatWord 16711935) 3 :=
  signedSlice (ms := ([swapRows 50] ++ fixRows 40 0)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a23Bound : Lower true (roots a23) (target a23) 6 := by
  have ready : Ready a23 a23Domains (asRow a23Pos) (asRow a23Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a23D0 (safeCons a23D1 (safeCons a23D2 (safeCons a23D3 (safeCons a23D4 (safeNil a23)))))
  exact frozen ready a23Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D0 : Slice true (roots a24) (target a24) (repeatWord 6172840429334713770) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D1 : Slice true (roots a24) (target a24) (repeatWord 18446744069414584320) 6 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 50, swapRows 67, flipInput 0] ++ fixRows 0 32)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D2 : Slice true (roots a24) (target a24) (repeatWord 6510615555426900570) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a23) (G := (target a23)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a23Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D3 : Slice true (roots a24) (target a24) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 84, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 1 0)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D4 : Slice true (roots a24) (target a24) (repeatWord 18374966859414961920) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 67, swapRows 84, flipInput 0, flipInput 4] ++ fixRows 0 8)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D5 : Slice true (roots a24) (target a24) (repeatWord 6149008514797120170) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 83, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D6 : Slice true (roots a24) (target a24) (repeatWord 18446462598732906495) 5 :=
  signedSlice (ms := ([swapRows 50, swapRows 83, flipInput 0, flipInput 2, flipInput 3] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D7 : Slice true (roots a24) (target a24) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 4 0)) (base := roots a14) (G := (neg (target a14))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a14Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D8 : Slice true (roots a24) (target a24) (repeatWord 4294967295) 4 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a14) (G := (target a14)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a14Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D9 : Slice true (roots a24) (target a24) (repeatWord 6124988953138320640) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67, flipInput 2] ++ fixRows 1 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D10 : Slice true (roots a24) (target a24) (repeatWord 6148914689804861440) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 84] ++ fixRows 1 32)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D11 : Slice true (roots a24) (target a24) (repeatWord 17361393124654452495) 4 :=
  signedSlice (ms := ([swapRows 66, swapRows 67, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D12 : Slice true (roots a24) (target a24) (repeatWord 71777214294589695) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 82, swapRows 83, flipInput 0, flipInput 4] ++ fixRows 40 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D13 : Slice true (roots a24) (target a24) (repeatWord 1085102592318504960) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, flipInput 0, flipInput 4] ++ fixRows 4 32)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24D14 : Slice true (roots a24) (target a24) (repeatWord 16711935) 3 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 82, swapRows 83, flipInput 0, flipInput 4] ++ fixRows 40 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a24Bound : Lower true (roots a24) (target a24) 8 := by
  have ready : Ready a24 a24Domains (asRow a24Pos) (asRow a24Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a24D0 (safeCons a24D1 (safeCons a24D2 (safeCons a24D3 (safeCons a24D4 (safeCons a24D5 (safeCons a24D6 (safeCons a24D7 (safeCons a24D8 (safeCons a24D9 (safeCons a24D10 (safeCons a24D11 (safeCons a24D12 (safeCons a24D13 (safeCons a24D14 (safeNil a24)))))))))))))))
  exact frozen ready a24Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D0 : Slice true (roots a25) (target a25) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 67, flipInput 5] ++ fixRows 2 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D1 : Slice true (roots a25) (target a25) (repeatWord 14757395258967641292) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, swapRows 83, flipInput 2] ++ fixRows 0 2)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D2 : Slice true (roots a25) (target a25) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 67, flipInput 5] ++ fixRows 4 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D3 : Slice true (roots a25) (target a25) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 81, swapRows 82, swapRows 83, flipInput 1] ++ fixRows 0 4)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D4 : Slice true (roots a25) (target a25) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 84, flipInput 0] ++ fixRows 0 32)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D5 : Slice true (roots a25) (target a25) (repeatWord 6124988953138320640) 4 :=
  signedSlice (ms := ([swapRows 16, flipInput 1, flipInput 2] ++ fixRows 1 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25D6 : Slice true (roots a25) (target a25) (repeatWord 6148914689804861440) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 1 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a25Bound : Lower true (roots a25) (target a25) 8 := by
  have ready : Ready a25 a25Domains (asRow a25Pos) (asRow a25Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a25D0 (safeCons a25D1 (safeCons a25D2 (safeCons a25D3 (safeCons a25D4 (safeCons a25D5 (safeCons a25D6 (safeNil a25)))))))
  exact frozen ready a25Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D0 : Slice true (roots a26) (target a26) (repeatWord 3689517697150995660) 6 :=
  signedSlice (ms := ([swapRows 50, swapRows 67] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D1 : Slice true (roots a26) (target a26) (repeatWord 3689348817318890700) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D2 : Slice true (roots a26) (target a26) (repeatWord 17361641477348724495) 6 :=
  signedSlice (ms := ([swapRows 81, swapRows 82, flipInput 1] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D3 : Slice true (roots a26) (target a26) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 50, swapRows 67, swapRows 84, flipInput 4, flipInput 5] ++ fixRows 2 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D4 : Slice true (roots a26) (target a26) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 81, swapRows 66, swapRows 83, flipInput 1, flipInput 5] ++ fixRows 0 4)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D5 : Slice true (roots a26) (target a26) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 16)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D6 : Slice true (roots a26) (target a26) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, flipInput 3] ++ fixRows 0 32)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D7 : Slice true (roots a26) (target a26) (repeatWord 3732415143318664140) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 65, swapRows 66, swapRows 67, swapRows 84, flipInput 2, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 3 true)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D8 : Slice true (roots a26) (target a26) (repeatWord 18374966855153418495) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, swapRows 67, flipInput 1, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 3 5 false)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D9 : Slice true (roots a26) (target a26) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66, swapRows 84, flipInput 4, flipInput 5] ++ fixRows 4 0)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D10 : Slice true (roots a26) (target a26) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 50] ++ fixRows 16 0)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D11 : Slice true (roots a26) (target a26) (repeatWord 3472328296227680304) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 66] ++ fixRows 2 4)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26D12 : Slice true (roots a26) (target a26) (repeatWord 18446462598732840960) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 0 48)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a26Bound : Lower true (roots a26) (target a26) 8 := by
  have ready : Ready a26 a26Domains (asRow a26Pos) (asRow a26Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a26D0 (safeCons a26D1 (safeCons a26D2 (safeCons a26D3 (safeCons a26D4 (safeCons a26D5 (safeCons a26D6 (safeCons a26D7 (safeCons a26D8 (safeCons a26D9 (safeCons a26D10 (safeCons a26D11 (safeCons a26D12 (safeNil a26)))))))))))))
  exact frozen ready a26Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27D0 : Slice true (roots a27) (target a27) (repeatWord 17361641481138401520) 6 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 83, swapRows 84, flipInput 0] ++ fixRows 0 4)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a27Bound : Lower true (roots a27) (target a27) 7 := by
  have ready : Ready a27 a27Domains (asRow a27Pos) (asRow a27Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a27D0 (safeNil a27)
  exact frozen ready a27Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 33, 37), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28D0 : Slice true (roots a28) (target a28) (repeatWord 6148914691236517205) 6 :=
  signedSlice (ms := ([swapRows 81, swapRows 83, swapRows 84, flipInput 1] ++ fixRows 1 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a28Bound : Lower true (roots a28) (target a28) 7 := by
  have ready : Ready a28 a28Domains (asRow a28Pos) (asRow a28Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a28D0 (safeNil a28)
  exact frozen ready a28Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29D0 : Slice true (roots a29) (target a29) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, flipInput 0] ++ fixRows 2 0)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a29Bound : Lower true (roots a29) (target a29) 7 := by
  have ready : Ready a29 a29Domains (asRow a29Pos) (asRow a29Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a29D0 (safeNil a29)
  exact frozen ready a29Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30D0 : Slice true (roots a30) (target a30) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 82, flipInput 2] ++ fixRows 8 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30D1 : Slice true (roots a30) (target a30) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 83, flipInput 0, flipInput 2, flipInput 4] ++ fixRows 32 0)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30D2 : Slice true (roots a30) (target a30) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 67, swapRows 84, flipInput 4] ++ fixRows 0 32)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30D3 : Slice true (roots a30) (target a30) (repeatWord 11936128518282651045) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 67, swapRows 84, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 2 false)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30D4 : Slice true (roots a30) (target a30) (repeatWord 1085350949055099120) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 4 true)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30D5 : Slice true (roots a30) (target a30) (repeatWord 252645135) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 84, flipInput 0, flipInput 3] ++ fixRows 36 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a30Bound : Lower true (roots a30) (target a30) 7 := by
  have ready : Ready a30 a30Domains (asRow a30Pos) (asRow a30Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a30D0 (safeCons a30D1 (safeCons a30D2 (safeCons a30D3 (safeCons a30D4 (safeCons a30D5 (safeNil a30))))))
  exact frozen ready a30Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 16, 20), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a31D0 : Slice true (roots a31) (target a31) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 84, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 2 0)) (base := roots a10) (G := (neg (target a10))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a10Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a31D1 : Slice true (roots a31) (target a31) (repeatWord 17361641481138401520) 5 :=
  signedSlice (ms := ([swapRows 81, swapRows 66, swapRows 83, flipInput 1, flipInput 4] ++ fixRows 0 4)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a31D2 : Slice true (roots a31) (target a31) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 16)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a31D3 : Slice true (roots a31) (target a31) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 83, flipInput 3, flipInput 4] ++ fixRows 0 32)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a31Bound : Lower true (roots a31) (target a31) 7 := by
  have ready : Ready a31 a31Domains (asRow a31Pos) (asRow a31Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a31D0 (safeCons a31D1 (safeCons a31D2 (safeCons a31D3 (safeNil a31))))
  exact frozen ready a31Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32D0 : Slice true (roots a32) (target a32) (repeatWord 14757395258967641292) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, swapRows 67, swapRows 84, flipInput 2, flipInput 5] ++ fixRows 0 2)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32D1 : Slice true (roots a32) (target a32) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32D2 : Slice true (roots a32) (target a32) (repeatWord 7378697629483820646) 5 :=
  signedSlice (ms := ([swapRows 82, swapRows 67, swapRows 84, flipInput 1, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32D3 : Slice true (roots a32) (target a32) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 49, flipInput 0, flipInput 1, flipInput 2, flipInput 5] ++ fixRows 16 0)) (base := roots a15) (G := (neg (target a15))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a15Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32D4 : Slice true (roots a32) (target a32) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 49, swapRows 84, flipInput 0, flipInput 1, flipInput 2] ++ fixRows 0 32)) (base := roots a15) (G := (neg (target a15))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a15Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a32Bound : Lower true (roots a32) (target a32) 7 := by
  have ready : Ready a32 a32Domains (asRow a32Pos) (asRow a32Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a32D0 (safeCons a32D1 (safeCons a32D2 (safeCons a32D3 (safeCons a32D4 (safeNil a32)))))
  exact frozen ready a32Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33D0 : Slice true (roots a33) (target a33) (repeatWord 11936128518282651045) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 84, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 2 false)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33D1 : Slice true (roots a33) (target a33) (repeatWord 14714328930390887475) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33D2 : Slice true (roots a33) (target a33) (repeatWord 7378697629483820646) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, flipInput 2, flipInput 3, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33D3 : Slice true (roots a33) (target a33) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 50] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33D4 : Slice true (roots a33) (target a33) (repeatWord 4340410370284600380) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33D5 : Slice true (roots a33) (target a33) (repeatWord 1148435428713435120) 5 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 0 0 ++ identifyRows 2 3 true)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a33Bound : Lower true (roots a33) (target a33) 7 := by
  have ready : Ready a33 a33Domains (asRow a33Pos) (asRow a33Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a33D0 (safeCons a33D1 (safeCons a33D2 (safeCons a33D3 (safeCons a33D4 (safeCons a33D5 (safeNil a33))))))
  exact frozen ready a33Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a34D0 : Slice true (roots a34) (target a34) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 4 0)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a34Bound : Lower true (roots a34) (target a34) 6 := by
  have ready : Ready a34 a34Domains (asRow a34Pos) (asRow a34Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a34D0 (safeNil a34)
  exact frozen ready a34Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a35D0 : Slice true (roots a35) (target a35) (repeatWord 14757395258967641292) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 0 2)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a35Bound : Lower true (roots a35) (target a35) 6 := by
  have ready : Ready a35 a35Domains (asRow a35Pos) (asRow a35Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a35D0 (safeNil a35)
  exact frozen ready a35Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 24, 26), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a36D0 : Slice true (roots a36) (target a36) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 1 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a36Bound : Lower true (roots a36) (target a36) 6 := by
  have ready : Ready a36 a36Domains (asRow a36Pos) (asRow a36Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a36D0 (safeNil a36)
  exact frozen ready a36Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a37D0 : Slice true (roots a37) (target a37) (repeatWord 7378697629483820646) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, flipInput 2] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a37Bound : Lower true (roots a37) (target a37) 6 := by
  have ready : Ready a37 a37Domains (asRow a37Pos) (asRow a37Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a37D0 (safeNil a37)
  exact frozen ready a37Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a38D0 : Slice true (roots a38) (target a38) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 16 0)) (base := roots a12) (G := (neg (target a12))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a12Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a38Bound : Lower true (roots a38) (target a38) 6 := by
  have ready : Ready a38 a38Domains (asRow a38Pos) (asRow a38Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a38D0 (safeNil a38)
  exact frozen ready a38Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a39Bound : Lower true (roots a39) (target a39) 5 := by
  have ready : Ready a39 a39Domains (asRow a39Pos) (asRow a39Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeNil a39
  exact frozen ready a39Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D0 : Slice true (roots a40) (target a40) (repeatWord 6172840429334713770) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a16) (G := (target a16)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a16Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D1 : Slice true (roots a40) (target a40) (repeatWord 4340410370284600380) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 2 true)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D2 : Slice true (roots a40) (target a40) (repeatWord 3689348817318890700) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a18) (G := (target a18)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a18Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D3 : Slice true (roots a40) (target a40) (repeatWord 17361641477348724495) 9 :=
  signedSlice (ms := ([swapRows 81, swapRows 82, flipInput 1] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a18) (G := (target a18)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a18Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D4 : Slice true (roots a40) (target a40) (repeatWord 6148914691236517205) 8 :=
  signedSlice (ms := ([] ++ fixRows 1 0)) (base := roots a19) (G := (target a19)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a19Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D5 : Slice true (roots a40) (target a40) (repeatWord 7378697629483820646) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a22) (G := (target a22)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a22Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D6 : Slice true (roots a40) (target a40) (repeatWord 14714328930390887475) 8 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 67, flipInput 0, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a19) (G := (neg (target a19))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a19Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D7 : Slice true (roots a40) (target a40) (repeatWord 3689517697150995660) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a24) (G := (target a24)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a24Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D8 : Slice true (roots a40) (target a40) (repeatWord 18446462598732906495) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a25) (G := (target a25)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a25Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D9 : Slice true (roots a40) (target a40) (repeatWord 6148914692668172970) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a26) (G := (target a26)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a26Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D10 : Slice true (roots a40) (target a40) (repeatWord 18374966855153418495) 8 :=
  signedSlice (ms := ([swapRows 16, swapRows 81, swapRows 66, swapRows 83, flipInput 1] ++ fixRows 0 0 ++ identifyRows 3 5 false)) (base := roots a26) (G := (target a26)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a26Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D11 : Slice true (roots a40) (target a40) (repeatWord 3689348814741910323) 7 :=
  signedSlice (ms := ([] ++ fixRows 2 0)) (base := roots a27) (G := (target a27)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a27Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D12 : Slice true (roots a40) (target a40) (repeatWord 17361641481138401520) 7 :=
  signedSlice (ms := ([swapRows 16, swapRows 50] ++ fixRows 0 4)) (base := roots a28) (G := (target a28)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a28Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D13 : Slice true (roots a40) (target a40) (repeatWord 18374966859414961920) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 8)) (base := roots a28) (G := (target a28)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a28Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D14 : Slice true (roots a40) (target a40) (repeatWord 18446744069414584320) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 32)) (base := roots a29) (G := (target a29)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a29Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D15 : Slice true (roots a40) (target a40) (repeatWord 11936128518282651045) 7 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, swapRows 50, swapRows 67, flipInput 1, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 2 false)) (base := roots a27) (G := (neg (target a27))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a27Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D16 : Slice true (roots a40) (target a40) (repeatWord 14757226376558555955) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 1 4 false)) (base := roots a30) (G := (target a30)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a30Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D17 : Slice true (roots a40) (target a40) (repeatWord 6149008514797120170) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a31) (G := (target a31)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a31Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D18 : Slice true (roots a40) (target a40) (repeatWord 12297829381041378645) 7 :=
  signedSlice (ms := ([swapRows 48, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a32) (G := (target a32)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a32Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D19 : Slice true (roots a40) (target a40) (repeatWord 17361393124654452495) 7 :=
  signedSlice (ms := ([swapRows 16, swapRows 65, swapRows 66, swapRows 67, flipInput 1] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a31) (G := (target a31)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a31Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D20 : Slice true (roots a40) (target a40) (repeatWord 18374687579166474495) 7 :=
  signedSlice (ms := ([swapRows 64, swapRows 67, flipInput 0] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a31) (G := (target a31)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a31Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D21 : Slice true (roots a40) (target a40) (repeatWord 71777218556133120) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 3 5 true)) (base := roots a32) (G := (target a32)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a32Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D22 : Slice true (roots a40) (target a40) (repeatWord 281470681808895) 7 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a33) (G := (target a33)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a33Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D23 : Slice true (roots a40) (target a40) (repeatWord 14757395258967641292) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 2)) (base := roots a34) (G := (target a34)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a34Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D24 : Slice true (roots a40) (target a40) (repeatWord 1085102592571150095) 6 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a35) (G := (target a35)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a35Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D25 : Slice true (roots a40) (target a40) (repeatWord 18446462603027742720) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 16)) (base := roots a36) (G := (target a36)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a36Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D26 : Slice true (roots a40) (target a40) (repeatWord 4294967295) 6 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a37) (G := (target a37)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a37Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D27 : Slice true (roots a40) (target a40) (repeatWord 6124988953138320640) 6 :=
  signedSlice (ms := ([swapRows 81, swapRows 83, swapRows 84, flipInput 1] ++ fixRows 1 8)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D28 : Slice true (roots a40) (target a40) (repeatWord 3472328296227680304) 6 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, swapRows 82, swapRows 83, swapRows 84, flipInput 0] ++ fixRows 2 4)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D29 : Slice true (roots a40) (target a40) (repeatWord 3689348813882916864) 6 :=
  signedSlice (ms := ([swapRows 80, swapRows 81, flipInput 0] ++ fixRows 2 32)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D30 : Slice true (roots a40) (target a40) (repeatWord 1148435428713435120) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 3 true)) (base := roots a38) (G := (target a38)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a38Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D31 : Slice true (roots a40) (target a40) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([] ++ fixRows 8 0)) (base := roots a39) (G := (target a39)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a39Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D32 : Slice true (roots a40) (target a40) (repeatWord 6148820867675914240) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 1 16)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D33 : Slice true (roots a40) (target a40) (repeatWord 6148914689804861440) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 66, swapRows 83, flipInput 3] ++ fixRows 1 32)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D34 : Slice true (roots a40) (target a40) (repeatWord 868082074056920076) 5 :=
  signedSlice (ms := ([swapRows 64, swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 3, flipInput 5] ++ fixRows 4 2)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D35 : Slice true (roots a40) (target a40) (repeatWord 3435973836) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 82, swapRows 83, swapRows 84, flipInput 2] ++ fixRows 32 2)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D36 : Slice true (roots a40) (target a40) (repeatWord 252645135) 5 :=
  signedSlice (ms := ([swapRows 67, swapRows 84, flipInput 4] ++ fixRows 36 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D37 : Slice true (roots a40) (target a40) (repeatWord 18446462598732840960) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 84, flipInput 0] ++ fixRows 0 48)) (base := roots a11) (G := (neg (target a11))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a11Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D38 : Slice true (roots a40) (target a40) (repeatWord 1085102592318504960) 4 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, swapRows 84, flipInput 0, flipInput 1, flipInput 3] ++ fixRows 4 32)) (base := roots a15) (G := (neg (target a15))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a15Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D39 : Slice true (roots a40) (target a40) (repeatWord 71777214277877760) 4 :=
  signedSlice (ms := ([swapRows 49, swapRows 84, flipInput 0, flipInput 1, flipInput 2] ++ fixRows 8 32)) (base := roots a15) (G := (neg (target a15))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a15Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D40 : Slice true (roots a40) (target a40) (repeatWord 6148820866244280320) 4 :=
  signedSlice (ms := ([swapRows 16, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 1 48)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40D41 : Slice true (roots a40) (target a40) (repeatWord 202116108) 4 :=
  signedSlice (ms := ([swapRows 50, swapRows 84, flipInput 0, flipInput 3] ++ fixRows 36 2)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a40Bound : Lower true (roots a40) (target a40) 11 := by
  have ready : Ready a40 a40Domains (asRow a40Pos) (asRow a40Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a40D0 (safeCons a40D1 (safeCons a40D2 (safeCons a40D3 (safeCons a40D4 (safeCons a40D5 (safeCons a40D6 (safeCons a40D7 (safeCons a40D8 (safeCons a40D9 (safeCons a40D10 (safeCons a40D11 (safeCons a40D12 (safeCons a40D13 (safeCons a40D14 (safeCons a40D15 (safeCons a40D16 (safeCons a40D17 (safeCons a40D18 (safeCons a40D19 (safeCons a40D20 (safeCons a40D21 (safeCons a40D22 (safeCons a40D23 (safeCons a40D24 (safeCons a40D25 (safeCons a40D26 (safeCons a40D27 (safeCons a40D28 (safeCons a40D29 (safeCons a40D30 (safeCons a40D31 (safeCons a40D32 (safeCons a40D33 (safeCons a40D34 (safeCons a40D35 (safeCons a40D36 (safeCons a40D37 (safeCons a40D38 (safeCons a40D39 (safeCons a40D40 (safeCons a40D41 (safeNil a40))))))))))))))))))))))))))))))))))))))))))
  exact frozen ready a40Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots := roots a40
def fullWord := target a40
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809440 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38899.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩, ⟨.and,[0,6]⟩, ⟨.and,[3,4]⟩, ⟨.or,[0,8]⟩, ⟨.and,[5,9]⟩, ⟨.and,[2,10]⟩, ⟨.or,[7,11]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,13]⟩, ⟨.or,[2,14]⟩, ⟨.and,[1,15]⟩, ⟨.or,[12,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38899
open PEqualNP.Outside.L_meta_38899 in
theorem PEqualNP.Outside.L_meta_38899 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := solve a40Bound

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38979.Model
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

end PEqualNP.Outside.L_meta_38979.Model

namespace PEqualNP.Outside.L_meta_38979
open PEqualNP.Outside.L_meta_38979.Model
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

def page0 : List Nat := [0xd221e818e61887, 0x825a4a1a6213905, 0x9ac49884dc57344, 0x621c7320c6218f, 0xf2ccb30483c4429, 0x290c84444412164, 0x7a49887b10e2109, 0x617e6910fd98241, 0x92417e68906f996, 0xe20a41e86388779, 0x8dea0063f661885, 0x9995e824437a481, 0x863985e1a2417a0, 0x17c49885f8a665b, 0x661de6510df9a62, 0x18c43f241885f8a, 0x5e1a4437a49987a, 0x18f710a41786988, 0xba000785b81be64, 0x80012004001880c, 0x8004b98ab800048, 0xd69398841081c80, 0xa5083ded6b5ad6a, 0xcc63a39ac5ed6a4]
def page1 : List Nat := [0xc43fcca523a774d, 0x863fc43f987d20f, 0xe4070000091000f, 0x6c64a7629062080, 0xe21c90727c6f24e, 0xc65fc83e10fd21f, 0xc63f0c3f107e10f, 0xac1fcc7f997d30f, 0x2c6200800002601, 0x11ecc1ac8db6910, 0xa7a7a7d8d11858d, 0x9318f6eca80a090, 0x492e83c390f42d4, 0x345b424c78721a6, 0x2c87b0a65a0e964, 0x4317dd9350d521d, 0xcaa0a1fbb28a22a, 0x1690d10d790f514, 0x1219fd8115ccaf5, 0xcd81214437b5094, 0x2590fea2548110f, 0x27e16416439fd81, 0x6d0931bdd854244, 0x329f8990590ef51]
def page2 : List Nat := [0x41b5150a7e16417, 0x5487f361481109f, 0xf7614cb41cf5144, 0x89510dbd0b524c6, 0xfad81214836d42, 0x1a43442f516cc91, 0xd0a7f6149630be4, 0x731d4520af45a43, 0x4121cf90d15d0b7, 0x9fd8525102be465, 0xb424c67d2645440, 0x27e26456439fd5, 0x41d4520db485251, 0x1429fd5b3148375, 0xe41a434827d16d4, 0x31483e52148110b, 0x27f654cb41bb49b, 0x14121bb49a4348, 0x43b74d845487795, 0xd852590e7f60456, 0x58c33f45915219f, 0x7f6548440dd4851, 0x90d20dbcca25442, 0x1b74d8504867f56]
def page3 : List Nat := [0x5a43442dc365412, 0x4867d06d49419fd, 0xf6049731d7cd635, 0x56309f195414827, 0x9fd5a434867e264, 0x1214827d2645630, 0x83e12148110fa18, 0x6548630f9d45214, 0xd219f195424427f, 0x790d32d06f51690, 0x35486bf4614121e, 0x67d5690d21afd1a, 0x149630d74d43548, 0x41af49a43d076d2, 0x49a434c67d26d41, 0x24c79e43d0931b7, 0xdc6351521d790f5, 0x90d32dd48515102, 0xdb4c925d06dd16, 0xd25d06ef625052, 0x486ed2690d21cf9, 0xe2645440af51b35, 0xc910f9895214427, 0xfc181214427f56c]
def page4 : List Nat := [0x1ec027e2641731, 0x8100000000001fc, 0xcdc8c01c400001, 0x294001008001002, 0x80010559c00a40, 0xc0254fc0000e400, 0x8000801d504f4e, 0x64c01cc08440000, 0x1c9cac001935e, 0x1566c002400010c, 0x1d6c0001261c000, 0xd58c0002354401, 0x8000000005e7c0, 0x20000000, 0x1000000006, 0x60000000280, 0x200000000e000, 0xc0000000480000, 0xc0000001a000000, 0x4408200004040, 0x120406000901030, 0x90188a24280835, 0x4109008820714c5, 0x1a6406480d20110]
def page5 : List Nat := [0x9a8212034d40810, 0xa66480d45121404, 0x902038d44850128, 0x480f35121405228, 0x3d1408101e8448, 0x353121405a29192, 0x14285080c183020, 0x82c5080e1c3870c, 0x2a50992243c70d1, 0xc386cd193264b16, 0xa54a912224484f9, 0x52a52a14274e992, 0xd9315cb56ac58a9, 0xf9f3d78edd3972d, 0xd1624385060c07e, 0x9b3264b95264478, 0x5104a349913e7ce, 0x22c6a0102215e0, 0x55914308ce60e8e, 0xbcbea0272c93006, 0x39c8ad7112807c7, 0x838c63a7ba72108, 0x1919819c222122, 0x482fa4a207e8811]
def page6 : List Nat := [0x9510ff21a21ff31, 0xe434c6fa4b21df4, 0x5fd4532ee99663d, 0x217d25cc7ea4288, 0xb995fd4121fc902, 0x1aa217d25842fa0, 0xfea2907f4cb41fe, 0x1dfa1283fd20443, 0x502fa2b105f4173, 0x4121be8ae85fd21, 0xd25d06fea2907f5, 0x5fd4931ff992217, 0x43fd21cc37c87a1, 0x498df89510ffa1a, 0x8ae65bd42d07be6, 0xfea4a0ff4d521be, 0x1fe908817d258c2, 0x8c2fea2a17fd093, 0x5643ff22a217d15, 0xf50487da42905f4, 0xff90d21fea0a41f, 0x43fe45483fe8a90, 0x6997f0d521fe22a, 0xa2a43fe50487bc8]
def page7 : List Nat := [0xf241087fcd521fe, 0x1fe282437d0590f, 0x8c3fc86907f9152, 0x4142fe1aa41fd21, 0xf50506fa2a205fd, 0x7f50910df21e837, 0x19fe35487fc4a88, 0x8021973200000, 0xe3047400, 0x169000289000080, 0x4c200ca00, 0x1780e200000ae0, 0x2014ef9a0080200, 0xbe8000fc05bb, 0x13ed8ffee00335, 0x100000000000, 0x400000000c0000, 0x14000000, 0x1c00000006, 0x240000000800, 0x2c0000000a0000, 0x40000000c000000, 0xe00000003, 0x81010000204000]
def page8 : List Nat := [0x100000020410000, 0x300004040400010, 0x624080001010, 0x6440c000191020, 0x41000020103000, 0x100002110300008, 0x881070002204, 0x90103000220420, 0x10800024041c00, 0x10002424000009, 0x242408000909, 0x26041000098103, 0x624100009890200, 0x408000989090002, 0x400099103000264, 0xa010300026442, 0xa11030002824100, 0x101000420400000, 0x42041000108, 0x4404040011010, 0x46040c001101030, 0x440c00118104000, 0xc0012110300046, 0x1219040004864]
def page9 : List Nat := [0x190103000620410, 0x890200066040c00, 0x20006624100019, 0x66440c001991, 0x680410001a0103, 0x82418001a090400, 0x418001a11030006, 0x4001a1903000684, 0x90882016a224080, 0x88200a2a240801a, 0x84c1a0802002928, 0x7a36188ac4a220d, 0xe2d150a44f24104, 0x1f0ec73381a4c65, 0x449f4e259228b41, 0xe63b0d78b65829d, 0x3a5cee36e359a4c, 0x170982bf9f2f578, 0x791c7a33158943e, 0xd12853e9c4d65f2, 0xcd62af566ad4fa5, 0x4c020e2c98c342e, 0x86051628182161, 0x674405020048910]
def page10 : List Nat := [0x22c45021015cb37, 0xa7a0c10516e138b, 0x234a4a3d0ef85a, 0xf11622948d386c2, 0x4091763059a3b2d, 0x20282022dd09101, 0xe1828b3a305a412, 0x121019d50941820, 0x3042060a120c21d, 0x8a10141811719e8, 0x60c563041a182d1, 0x50a012ce2947a19, 0xb8730101449d607, 0xb0cabf0cb462f1e, 0x7e1e00b120c10b0, 0xd782c2b98c31315, 0x880a28d47441c30, 0x1820a2c93222c59, 0x623f060840c4efc, 0x1a04a80b87094c3, 0x2b093215146be52, 0x100cb876a0830c9, 0x986354250608386, 0x3406186485abc78]
def page11 : List Nat := [0x70e120c40570206, 0xc483767cf040675, 0xdc05140c10c104, 0x8b22875a884070c, 0x6c582996e883881, 0x88a699843ae550b, 0xa680882a986b510, 0x182101459018745, 0xd0a0080dd8a1230, 0x2018c0a2ccb7104, 0x3028b0a0da0614, 0x61c5c212202820, 0xc82284050600617, 0x1a120c10c10e220, 0xe436c5910612101, 0x30ff32fd32ff42f, 0x1fd21ff31fd42ff, 0xfd40fd10fe20fd3, 0xe10ff43fd20fc40, 0x28fd41fe30ff41f, 0xaed0213c002, 0xa00004000018, 0x8000038000180, 0x58000280001200]
def page12 : List Nat := [0x380001a0000c000, 0x20104100818000, 0x440822204051020, 0x4040d2020290100, 0x120490901484802, 0x1034c881a624112, 0x81a8241140208a0, 0xe3020918103508, 0x99810390c824864, 0xcc881e624133020, 0x8640f42207a0904, 0x162230380d0c826, 0x3427cdd9ae487cd, 0xa1c4c97edd6a536, 0xa1673022cb02180, 0xc4a528230664c08, 0x131374b08c8e228, 0x71851030813e428, 0x228660c04a5d654, 0xc1c42112c12812c, 0xb08a38d18a6da2c, 0xaa40a0c28710950, 0x52c598c04b08b04, 0xd11f41c2c131f78]
def page13 : List Nat := [0x204fa7d3e888e88, 0x5c42fa2b107b487, 0xc5720bea80437c2, 0x7c50486fe4b885f, 0x87d08610be92c21, 0xe21ec21882fc4b0, 0x5cab99eaffa90, 0xc00004000000000, 0x80000380000, 0x408080002800012, 0x40420200081040, 0x204901004408222, 0x28408242040e10, 0x1e2040a20207101, 0xf2020588104c408, 0xba4690384064040, 0xa3050f44d2470b8, 0xa6200c4105749c8, 0x5188288c0c4039, 0x344bd4f7b2d528c, 0xfc41fe21fe41f84, 0x4dfa43fc21, 0xc0000400001, 0xc00005000020]
def page14 : List Nat := [0x90000400001c0, 0x824204040001400, 0x131020310100840, 0x58f200c80806204, 0x5d0520c5012c91d, 0x9031040f5206200, 0xc4103127188017a, 0xd6d49cc50118938, 0x111ac7c54c3a087, 0x40be22a41bf42d0, 0x2482fa0ba15f497, 0x3000000017a1ef4, 0xa01a12000000000, 0xd88924320342400, 0x105ff42fd20ff40, 0xe00006000028000, 0x48081a404040000, 0x844053220498102, 0x207a0100c80802, 0x4e0d0881e844074, 0x421953310a62bab, 0x358d11f8c3027d1, 0x306d12a2188563e, 0xd46cd925043072]
def page15 : List Nat := [0xe216b9b482886e, 0x36930a0a0dae6d2, 0x24a0847c8c8a861, 0x86588d12a2197a3, 0x4c8a861a71b44a8, 0xa211ea360b98cdc, 0x69360b98e5c8d12, 0x4a0847a8d9ac213, 0x69a6c92821a79b2, 0xc282832e31a8b08, 0x21371322b204be6, 0xa30638856a8c18a, 0xa8865a8c928215a, 0xb86c8ac81a61b44, 0xa0000000001013c, 0x600802e02200a12, 0x25442fea0a09001, 0xfc5640fd884216e, 0x1f731442fe6a085, 0x987d50510fa18a2, 0x8a817f05cc6fa2b, 0x862185f45430bfa, 0xbea2e21f710843b, 0x42fa8a085f41641]
def page16 : List Nat := [0x430be1ac217f358, 0x159027c8a885fc5, 0xd0c710af9ac837d, 0x13d45cc2da4a087, 0xa05f916109ea282, 0x80633d450c6f8a2, 0xa8b0857cd410bea, 0xfb20a217d05cc6f, 0x2fca018dfc1641, 0x730fb98e21be419, 0x35442f86a8877cc, 0x714d40faa0e215c, 0x17c50506fc8a885, 0x985fcd710fb20e2, 0x5901bd41502fe2b, 0x6865e119802aac0, 0xc100000015b009e, 0xc016c6030863e3, 0xb3a0000096, 0x4080000001f860, 0x126a80, 0x40000000100, 0x8100000000c000, 0x2000a09010000c]
def page17 : List Nat := [0x662408002402, 0x98a02000d444100, 0x62801450104002, 0x8200514cc10028a, 0x803350104012288, 0x2082000066a482, 0x9c71a5904082061, 0x2eb2aa2282081e7, 0x43040fbae36d34c, 0xd34d144f3cb2c71, 0x642042278df75d6, 0x63e621a46686640, 0x6c624427c766758, 0xfe60a664642130e, 0x821f861fe63f863, 0x21fc83fa83fa21f, 0x5fe21fa81fc81fc, 0x2001c1528880784, 0x18000080000, 0x180000a00004, 0x20000008000038, 0x1000c4800604001, 0x802824014020088, 0x24120120100840]
def page18 : List Nat := [0x198900cc0806204, 0x32c2f34a1c50c18, 0x2ccea29e433e565, 0x13a21020421a4e2, 0x818e2334ee8840b, 0x8b087111e70804e, 0x9510a203e418402, 0x3f441eda4a085b8, 0x503f843fc43f04, 0x8d11d94a11a2080, 0x4fa5950fa28c688, 0x64c5104fa7d3e9f, 0x110a91299524a03, 0x97029d9110d3248, 0x21d290d93148110, 0x5c4348520440c70, 0xba6c30a42905786, 0x94dc7148110a73c, 0x9b66230a415b04, 0x1701c1260c65af3, 0x6649bc4c8843ee6, 0x2057010d10d4624, 0xc3ac0302435e129, 0x370dd068871b073]
def page19 : List Nat := [0x919b2c090c37e61, 0xe12745a30c4f1be, 0x8871022189c488, 0x74dd214c27c724c, 0xd988c290437e246, 0x9524c110a6bcba6, 0xa6fb0a4183c4721, 0x49c364425af1398, 0x8be648851b25952, 0x6118520af094900, 0x869924187459e1d, 0xc5260c279722c00, 0xb46c88639e61711, 0x64c11092ecc0872, 0x8b6650be9811d2, 0x1204421f730b80e, 0xa40886e8121214c, 0x98520de11327038, 0xb00874d43961f61, 0x260c31cae2940e2, 0xc290719d5d711c5, 0x8110c6a1cf0eb08, 0x3665bc1380e1214, 0x68c21ef308b82e8]
def page20 : List Nat := [0x90e2b1238249d1, 0x830a4fa4f0c9b8c, 0x61cc4395c47149, 0x4861ef30b88e293, 0x9961e9678758060, 0x10c74b82503822d, 0x619708795931481, 0x430bcb11c24e8b4, 0x8578de731485204, 0x1a73cba31b14429, 0x18da39e1d601812, 0x2cd6d32c44c9022, 0xe7821e264c52044, 0xa6cc808c9b8c090, 0x66519cca5689910, 0xd8b221b26430a41, 0x7421f374c520442, 0x6fc4c6ebb243186, 0xe7891c521498308, 0xc11290a60902212, 0x8a6043485204427, 0xc886e99240884f, 0x3498e12148110be, 0xf309b86f132217a]
def page21 : List Nat := [0x25d8010d214421b, 0xb96919b2c090c7c, 0x984dc37d8121c57, 0x309b8ec90e610df, 0x61370dd26c421bf, 0x4ed118a4088437e, 0x84dc37d85209f11, 0x992c230a410df9, 0x536185214835887, 0x2e238a4c185a912, 0xe1d6118520e33a9, 0x9ba62902218d639, 0x8049f314827a713, 0xe238ac021d78464, 0x438851087bcc2, 0xb262902213e3926, 0x8cc5214c2f82521, 0x49bc4c8863319d2, 0xc7048510967c4e6, 0x2e221a215b349cd, 0x8c520442bc25240, 0xb3c42886f00dd28, 0x528d910a729486d, 0x429022125f8910d]
def page22 : List Nat := [0xdd21c42f46939c2, 0xc090d35e59370, 0x58443c5d24f0eb, 0x2930618e9704a07, 0x9204425cf30b88e, 0x24d98d9ada45889, 0x89910c78b823038, 0x30a416c99010f32, 0x324825c930992c2, 0xc2904b32598110d, 0x8031d621b25018e, 0xb46146d29162275, 0x24c319871c124e8, 0x29043de611705f6, 0x510a6bc8ad19b8c, 0xa4165496548364c, 0xcc65ab131b063b0, 0x9061d55f815c126, 0x21b63c926d988c2, 0x6187859e1d60181, 0x421ef30b88e2934, 0x5b8a5843485204, 0x9724b30221a429, 0x14d59110c764c91]
def page23 : List Nat := [0x75a06cc0063b0a4, 0x62e127875806048, 0x9f0cc08690a4088, 0x8b649e1d6118520, 0xcced22c44c90a21, 0x1b4a45889d168c2, 0x7dcc2e0382c221d, 0xcc67e0931485308, 0xbb131b66fb0a418, 0xc627371c1214421, 0xbc8a6da38c29047, 0x3924dc7148110a5, 0xa532c44e8b4615e, 0x9223849d168c28d, 0xc888c9b8c290627, 0x47cca264c110a6a, 0xa49406c98a21c8c, 0xdd321c52044368a, 0x4a6e90a40887700, 0x110d3248110bd02, 0xb80e0936637c19, 0x787584614821f73, 0xa6290a408862d12, 0x6044345a20af04b]
def page24 : List Nat := [0xc0a4e8b4612e792, 0x43485204431a871, 0xb11324288578a5c, 0xe16118520b33b4c, 0x1e6513221ac5920, 0x74c520442d8b222, 0xe90a408865c5648, 0x443481109f1c486, 0x8e2930611f09760, 0x885260c398c72b8, 0x98a40884b966371, 0x324c110ce84386c, 0x210180d89c47da3, 0x439b2041a1de7f, 0x201ec72e20028f6, 0x4a210140c2874d, 0x8040196000434e8, 0x2e1e180c210, 0xf03c040808333a, 0x1c00018e002c040, 0x2400181c08ee04, 0x174e14040045420, 0x26000000000000, 0x2800000000000]
def page25 : List Nat := [0x3c0000000000, 0x3e000000000, 0x4322600000000, 0x15223c0000000, 0x25123c000000, 0x3612142600000, 0x461304160000, 0x46132426000, 0x6113041600, 0x1201104360, 0xe00000131031416, 0x160000013215242, 0x428000001610304, 0x242800000346232, 0x304160000034633, 0x130438000003611, 0x103061600000362, 0x1011061c0003716, 0x36110616001270, 0x135603061600131, 0x710302316160016, 0x171036120808001, 0x820618618408132, 0xa28820820820820]
def page26 : List Nat := [0xe38e38a28a28a28, 0x659659451451040, 0x71c71a69a61861, 0xebacb2a9a68a28a, 0x2cb2c2ebaebaeba, 0x8e38e36db6d34d3, 0xaebaebaebaebae3, 0xcf3cf3cf3cf3cf3, 0x1040fbefbef3cf3, 0x104104104104104, 0x92491c71c70c104, 0xf3cf34b2c924924, 0x21b7495d554853c, 0x418f584797b267a, 0x258100231b11e91, 0xe3424d810c04cc5, 0xf2371c520442b7c, 0x437a1db7048520d, 0x8110bf1810dd204, 0x1a364837c0dc714, 0x57010d10adf381, 0xf1371c5204437ce, 0x86afd233698121d, 0x85209df874d8364]
def page27 : List Nat := [0xc560486fae01374, 0x430d910dd437d, 0xf518d0b614c2f66, 0x43378df4658121a, 0x8510add8210d360, 0xde26442fcda0704, 0x43cc910ecf32c, 0xeb8049e31482f66, 0x42f3604364c920d, 0x81109f58710d214, 0x5f624c2ee121304, 0x213741a21c7e574, 0xcf824c5214c2af1, 0xc3b30d93258520b, 0x8443cdf62cdc414, 0x9c31482bbe09705, 0x1f3188110deb804, 0xed2859e210c27e6, 0x82fa6084348210c, 0x9830ed731d87304, 0xc461483395c4714, 0xd93218520ed536c, 0xe771885260c3b30, 0x423fda12710530e]
def page28 : List Nat := [0x5b32bf3688c5204, 0xf614cb3edc2704, 0xc52148110bd5811, 0xf980c5f624c3f84, 0x42afd233658121a, 0x8520a7f68cca564, 0xe20442be60043d, 0xdd32481109f9871, 0xf98710d20443f20, 0x82bb8a17045b329, 0x8210ee532584614, 0xd268c2f60e1714, 0xca5648110aed821, 0xe528cc461483da4, 0x427dde2214c110b, 0x5910aed8210d264, 0xd843c42dd463321, 0xa332cc3108ff825, 0xdd78ccb614c2b75, 0x42b721932cc510c, 0x82109f528d9e314, 0xd068867e61c434, 0x623618520af5811, 0x798010d52442bd4]
def page29 : List Nat := [0x82be5a33748210b, 0xd32dd8365c0314, 0x992044277e05701, 0x1d5245840f68588, 0xe361dc1214829f2, 0x6bd0e16118520f, 0x5a308fc874c906d, 0xc7614833be09274, 0x217149a10af5870, 0x777295931442af1, 0x42edd233748510d, 0x8110be58210d214, 0xd32483f889a314, 0xca264c510bc9801, 0xdf38d0a36443f1c, 0x42be6004149a30a, 0xc930bd58110f324, 0xc520442f660317c, 0x92745830fe1321, 0x6f57485260c33be, 0xc33719f3148530e, 0xd10cef6249f414, 0x9d168c31f962761, 0xe1214c110cef428]
def page30 : List Nat := [0xd9325c0414c27d1, 0x431f15d17d8930d, 0xda10fe121cc1204, 0xdd210c31f963724, 0xe1214c310bd9800, 0xe471485260c27dd, 0xc7378db3789910e, 0x9b31cfb709c126c, 0xc7614833e5c0704, 0xdb31d8520ed4360, 0x6e58dc930483b54, 0x3b9d186148520d, 0x8121aef824c526d, 0xd9604876711e375, 0x17110e21cbc474, 0xd718ccb614c27de, 0x42afd2337d8121e, 0x8121be98210d204, 0x8b314c2be423369, 0xca26cc510e5c58d, 0xe08748520443b3c, 0x437a4df7048520f, 0x5a30a7f68d48364, 0xc9604871f95d274]
def page31 : List Nat := [0xa331d8520dcc37d, 0xe2261c121442f94, 0x439b1636288530f, 0x1b32fe037485204, 0xd8438833dc5e174, 0xe347498108ff815, 0xf5711c5268c2bbc, 0x429fda25789910c, 0x8110adf3811a364, 0xd26c43f8119214, 0xc47149830aed821, 0xf3805c4434433d5, 0x433719f3748530d, 0x81318fd8710e264, 0xc92044337de332d, 0x1d6118520be8864, 0xdf378df614823de, 0x42fa4a33148210c, 0x8121cbc47499304, 0xdd214c36791e375, 0x843d8931adf68c, 0xf237dc121442bb6, 0x82be4231741b32d, 0x8510cde36cdc614]
def page32 : List Nat := [0xd26c43d9962264, 0x6127cc5308fe871, 0xd4385846148357d, 0x433d85f1641b32a, 0x8510bf3788c5204, 0xc9261077c0dc704, 0x1c4348510aef804, 0xf446dc5364827da, 0x433e5c07058443c, 0xc120bd768cc9314, 0xc336d06b7da331c, 0x63714cb308fe285, 0xe121d0120443575, 0xc2f44e07148110f, 0x8043ed438485168, 0xc1214833ddc6715, 0xa33718520dea37d, 0xdd8610f32843375, 0x436d11d214c110a, 0x9831bd58110d324, 0xe214433edc2704, 0x17110d10bf1801, 0xdf78cc9368437c2, 0xc3b94636288530c]
def page33 : List Nat := [0x5a30aed280c5268, 0xc121443b989d214, 0x93748510df137d, 0xf5188df61482f9e, 0x7b9dc57149830a, 0x81108fe2841f361, 0xc0438433b0de264, 0xe331481109fb825, 0xd6360c7614827ed, 0xc63f5e226cc510e, 0x81108fd8710d268, 0xd841483dc158714, 0xe17049b108fd788, 0x645889921442b70, 0xc37a8a17010520f, 0xdb10e7457885168, 0x5268c33b49d20c, 0x532185208fd781, 0xfa8610e20442f9e, 0x4337cde3749b10a, 0x8520c7e578de264, 0xd16883b30d9329, 0xe171498308fe871, 0xeb8048526843b38]
def page34 : List Nat := [0x43730dd3258520e, 0xc520fe331485204, 0xdd260437a20127c, 0x1c4341a21ecc43c, 0xf3471c1214423fa, 0xc2be42237d8121d, 0x8730af518d9d214, 0xd26043374dc764, 0xdd3148110aed821, 0xff78105268c3f4c, 0x867d61c43885108, 0xc5308ff788d9604, 0x85304433bd89270, 0xa23148110de7728, 0x7c585da218c2f84, 0xcb3711f724d810c, 0x8121af581118614, 0xdf42c433bdc8465, 0xe342899108fd86c, 0x7e5841f624c6bbc, 0xcbf8d052148110c, 0x8121c7e5785d06c, 0xd96148337cd9379, 0x5e7149830cdc378]
def page35 : List Nat := [0xf908d1a604879bd, 0x433b89d2145830a, 0x8530f6a58899204, 0x4a364433719d314, 0xdf7158121a7c865, 0xdd68ccb31843758, 0xc3f84cb7148110a, 0x8121c7c5889d168, 0xca26443370d937d, 0x5e17d8930ee718c, 0xff6849c314c33dc, 0xc27de017110d218, 0x9910e6d57dc5260, 0x5f428c2f9463328, 0xdc3749b108ff864, 0xdf36d9f31483374, 0xc31f5637149b30c, 0xc9208fd78d88414, 0xdd21c42f3604434, 0x1f6098121af568c, 0x3f57d1e364873e6, 0x43f80d92148110d, 0x8121af98010e264, 0xc521482be42037d]
def page36 : List Nat := [0x84349a31aef864, 0xe37148520442bb6, 0xc23f5e34618520f, 0x8530ee527885160, 0xdd604873719d374, 0xa03688510d9e470, 0xf90811f60486f94, 0xcb754dc3748510a, 0x8520c7c5785d06c, 0x8521482bb4a331d, 0xa25745a30ee4461, 0xf58110d168829f4, 0x425fe057010d52a, 0x8110f6256485204, 0xdf60487f8d1d214, 0xe12148110abf488, 0xcc38485260c3f80, 0x42f9e053648520e, 0x8520adf68ccb304, 0x9f314c3b98d8614, 0x843d85208fd28d, 0xdd32d9c414c2bb6, 0xc3b3cca264c510c, 0x8110ee771485268]
def page37 : List Nat := [0xc520443f8cdd214, 0x5d1741b32fe2261, 0xf78148336c431f1, 0x436711f324c310a, 0x8121e6f3295e264, 0x1f36106bb60843d, 0x6037d8520cdd324, 0xcf3289930442bd4, 0x83f811d2148110e, 0x5a30abc484df614, 0xd8434431f161274, 0x97010d108fd289, 0xcc37cc9260427ee, 0x427be097110d21e, 0x8730db447885304, 0xc521cc2bde05764, 0xa03648110bcd28c, 0x7c5889d600c6fa4, 0x42f50e2264c510c, 0xcb10db44748530c, 0xe36442b7618434, 0x1843ccb10bd5811, 0xde3849d168c2b76, 0xc39bd0a5789910c]
def page38 : List Nat := [0x59108fd28d9c314, 0xe21442dd463329, 0x592148110af6861, 0xff874d861483d99, 0x433b4a367485308, 0xdb408fd8710d260, 0xc116cca3f5e221c, 0xe0414da20cf9701, 0xef825d843486b7c, 0x43b58e12145830c, 0x620df208dc9314, 0xdd260423f61b37d, 0x1c4349810ecf380, 0xed68cc521482bba, 0xc337d193718121a, 0xc510a7d2815d168, 0xdf4284379dca264, 0x1c4349a108fd86c, 0xfd8710d068863f6, 0x433dcc77149a308, 0x630aed28d0e264, 0x1f614ca3f8a1761, 0x890788530c7d574, 0xdf378dd068873bd]
def page39 : List Nat := [0x42b7da3324c110c, 0xc6109f7825c4434, 0xc9204427e8a107c, 0xa04789910fc8434, 0xfb8758060486bb4, 0x86bb46342899109, 0xc9108fd78cd8604, 0x18614837c20117c, 0x1f6198520af5811, 0x7c87549304433d6, 0xc277e017110f329, 0x8121cf78149d160, 0xd52442afd2336d, 0x5c1741b32a7e861, 0xed8210f624c33d4, 0x835796107cc931a, 0x9910cdf464dc614, 0xd324839bcc8578, 0x213049b10bce861, 0xe58210d21c42af1, 0xc3ba8987048510b, 0x9910c7e5849d168, 0xc5204423fa1c438, 0xe2360c520f72564]
def page40 : List Nat := [0xf58110d26442775, 0x431f15e17d8930a, 0x8520add68cc930c, 0x9f36d06bde05361, 0x5c47581218ff804, 0xed28d85214c34f1, 0x8337de332d8530a, 0xc521dcf72cc5304, 0xd06887738db724, 0x1c7148110af9801, 0xdc385c5268437c1, 0x435d15f7158121a, 0x9830fe137485204, 0xc1214439bd49714, 0x5d7149830f70561, 0xb447dc5604879b5, 0xc3b30d932d8520d, 0x8121e6f57885260, 0x9c3644379dcb715, 0xf3289910d6d524, 0xd736cc461483b3d, 0x42bb6184348520e, 0x5a30de62649e314, 0xc120443b58e1214]
def page41 : List Nat := [0xe12148110fe1214, 0xcf3289b30443f84, 0xcabb4a047d8931e, 0x4910cf517c5b06c, 0xc5260c2dd604435, 0x217148210e6d525, 0xe7825c443486ee1, 0xc2bee011741b32d, 0x8532ee5711c5260, 0xd214831f55e07d, 0xd86148520aee861, 0xe58110d21483b9c, 0x43738d9270c520b, 0x8930ecc43cca264, 0xd9218c2afd2317d, 0x43cca10cde375, 0xed280de26442f66, 0xc337cd9178d920a, 0xcb10e7657485168, 0xe56442f560443c, 0x1f7158121b79801, 0xf51811f614836d9, 0x833edc27058443a, 0x520ed7314df614]
def page42 : List Nat := [0xc5268c33b4cb671, 0x1d3210530aed28c, 0xef6249f314c277e, 0x82bbce04749810c, 0xd920cee3649c414, 0x85204433d118714, 0xdb6788510fe0484, 0x6d2815e264433d0, 0x42afd223749b10a, 0x85209f978cc5208, 0xc121c42bd604361, 0x1d3148110bd4385, 0xed3289d16d027e2, 0x429fa184395910c, 0xd20fc932cc5204, 0xdd214437ae09701, 0x5d7149830bb7488, 0xd7814d8364871f5, 0x82bb4a337d8121e, 0x9309ef825c4438, 0xc1260c63f1a117d, 0xa3714c310cf9701, 0xea26dc1214427d4, 0x82bd5a34748710e]
def page43 : List Nat := [0x9810fc532cc7614, 0x9d168c23fa1c434, 0xa33710530c7c574, 0xf98610d20842774, 0xc31f560764c520a, 0x8520cfb625c0414, 0xd26843b90d8614, 0xca2745a308fe871, 0xf98010d268433bc, 0x8337de3324db10a, 0x8520dcc3649c314, 0x1e36486bd46343d, 0xe17149830d3d575, 0xec3789921443b30, 0x423fda337d0520c, 0xd841afa8610d204, 0x89314c2b7e0132c, 0x233289910e5e58d, 0xdd38d9f31482bb4, 0x87734cb3718520c, 0x81108fd089d8434, 0xd836486fc21d314, 0xe03658520cdf874, 0xde3849d160c23fd]
def page44 : List Nat := [0x433710c764c910c, 0x8443e6c58899214, 0xc041482bb4a0705, 0x5f7049b31cfa365, 0xfd8711a614831f5, 0xc3370d937181218, 0xc5208fd28d9c414, 0xd861483371db364, 0x877048520aef824, 0x5e578dd60487f81, 0xc3378dc4658520d, 0x9830ee627485160, 0x9d168c31fd5d714, 0xcb3118520cbc484, 0x685648520443f14, 0x43378dc4658121f, 0xc10e6f3295a264, 0xdb604863fe09761, 0xa331cc120abf488, 0xcd32d9f31482f34, 0x831f55d7049b31d, 0x8510be908d1d214, 0x9f32442f94a3374, 0x443d8121cdf43d]
def page45 : List Nat := [0xdf378df60486bd6, 0xcb2f8db4718520c, 0x9b109df805c4434, 0x9c31482b78e1704, 0x5d2145a30de8804, 0xdc464dc604879d1, 0x869fda05789910c, 0x9830d3e5791d604, 0x9f31487b9dc6714, 0xa117d0d209ef804, 0xdf78cc9360423f1, 0x83378dc3658121c, 0xc510af98010d168, 0xde264433b49927c, 0xdc7148110c7e574, 0xdc4359f320437cc, 0x871f95d1741b32c, 0x59109ef825c0438, 0x85204429fda3439, 0xe12745a30fe3434, 0x7f78d49600c7370, 0x436b11d3258520a, 0x85309fb78cc5208, 0xca26443b546332d]
def page46 : List Nat := [0xe12148110aed18c, 0xdf37dd921cc3f8c, 0x433710f67cc910c, 0xc520beb814c9204, 0xd2148277de3364, 0xa127cc530be9801, 0xff8049f361063fd, 0xcb7ccdc70485108, 0x8520afb8045b06c, 0xf61482f9463364, 0x2337487108fd871, 0xcf324de26442edd, 0x433d5c47158043e, 0x8520df0815c0434, 0x8520443f8d84704, 0x1b37d0810fe2384, 0xd98010d324423f6, 0x42be5a34748210b, 0x81109f68710d21c, 0x49168c27c21d314, 0xdc3789910a7c875, 0x4d580d932483374, 0x867b1e1214c120f, 0x81108ff805d8438]
def page47 : List Nat := [0xf60487f810d214, 0xa3678c5108fd871, 0xea285c0314827d8, 0x879b1622648110d, 0x9910cef72d19604, 0xdc414829b4a2578, 0xa07148110dcd32c, 0xdc4349e36442fcd, 0x43b5cc7614c120c, 0x8520fd0364c5204, 0xc16110f2f4db471, 0xd9278c5208fd28d, 0x7f68cc856443730, 0x42f3ce3464c920a, 0x81218fd68dc930c, 0xc960486be600461, 0x1b3710620dac47d, 0xed28cc5268423f6, 0xc63ee1d6018121a, 0x5b43a7d2815d600, 0x59304423f422274, 0xa331d8121d3c479, 0xf58610d21c42bb4, 0xc3d91592148110a]
def page48 : List Nat := [0x8930c7f57dc5260, 0xc5260c31f96117d, 0x97158043e6f529, 0xf5800c761482bbe, 0x423f4627610d20a, 0x9910aef38d09260, 0xc5304823fa1c434, 0xe33149a10adf68c, 0xe348485204423fd, 0x423fda33710520f, 0x8110c7e5859f328, 0xd214439b962264, 0xa37045b43af6861, 0xff8748736d023f4, 0x82bb4a03741a218, 0x8520ed4318df614, 0xc1214433bdc8465, 0x1c4348210df0471, 0xbc46dc1214c27ea, 0x31f15e2745a30c, 0x9910cef8249d161, 0xdd61482bb4a2378, 0x532d8520dcd820, 0xef7289931442f9e]
def page49 : List Nat := [0x86eb1217048520c, 0x5830cef72cd9604, 0x1f424c7b989d274, 0xdc37d81218fc684, 0xcd28cdc61483374, 0x439bd637149830d, 0x8520bd6385c121c, 0x9c414c23fa1c43d, 0x233748520dcd324, 0xdc464dc61482fa4, 0x83374dc37d8520c, 0x8043d78585c0314, 0xdf424423f4a3715, 0xdc37487108fe86c, 0xea08dc532483754, 0x42be6004349910d, 0xc110beb824dd204, 0xc5260c34f11d524, 0x1f324c110e6f575, 0x7c864ca56443671, 0x833d0c77149a30a, 0xc110bf1800c7614, 0xc9604876711c364, 0xdf7258121dae47d]
def page50 : List Nat := [0x7f78d49168c3738, 0x42af1212745a30a, 0x9830a7f68d4b314, 0x9d214c39b54b714, 0x1d3258041cf518d, 0xdd370dd068863f2, 0x33dd873798520c, 0xc110cee27485161, 0x9360429f21952c, 0xa33718520adf78d, 0x5c578dd6048737d, 0xc75795c3758121d, 0x9830c7d58dc126c, 0xdd21c43b9dc5214, 0x1c4349b10af7864, 0xbf481c5268c23f6, 0xc2af1213618520a, 0x8630cf7719c5268, 0xc041482bde05764, 0x6047d8532de9325, 0xd5280d931442bd4, 0x8379dcb714d921b, 0xc520aef68cc5214, 0x9930443760d9078]
def page51 : List Nat := [0x6127cc521cbc478, 0xdd688dd210c35bd, 0x43378df3658121a, 0x9b10cef72899304, 0x9f314c2bd604434, 0x48364c510d5d584, 0x6d58dc532483d55, 0x82bb2193148520d, 0x5a308fc865c4434, 0xc930c433b89d214, 0x93741a21bd518c, 0xff865c043486bbe, 0x2b7ce0468d9218, 0x5a308fc874c916d, 0xd214433de05274, 0x5d7049b31bf1801, 0xdf815c043ccb1fd, 0xc29fda342959109, 0x8121c7e5785f624, 0xc4434cb37e19371, 0x1e36585209ef825, 0xd736cc7614832f1, 0x83b642332d8131e, 0x8520dcd370dd214]
def page52 : List Nat := [0x5b06ccbb91db614, 0xe12149a30af980c, 0xed18dc930483b30, 0x42ee12137481109, 0xdb40c7e5649e364, 0xd214833b88527c, 0x197010d219ee871, 0x7c5749d600c63f2, 0xc7b91c52149a30c, 0xe10af5181c126c, 0xcb314423fe09761, 0x3618121adf68c, 0x6f521c5260c2be6, 0x423fa1c43d8121e, 0xd921bf18110e204, 0x5f4354bb3e09360, 0x127cc52097f804, 0x7e5789d168c37ae, 0xc23f4637258043c, 0x8110bcd28cc5214, 0x1d360437cd1c714, 0xe12149a30add821, 0xee2748516cc3b38, 0x423fe1d3258041c]
def page53 : List Nat := [0x9910bd58110d32c, 0xde2644337cde378, 0xa117d0d21abc484, 0x6f3215a264427b8, 0xe3f423764c841e, 0xc5108fd08dc9611, 0x5268c2dd4a2564, 0xd92148110aed281, 0xd63849d160c3f88, 0x82bd6044389910e, 0xd52bcc385c1214, 0x5d06cca5fe01711, 0x5e2758031aed280, 0x5c4395a364431f1, 0x8357563714c930e, 0xf10be518d19214, 0xc121c427de09711, 0xd86148520bb4485, 0xce385c121483b94, 0x439b15a2648110b, 0x9b10bd98010e364, 0x536882afd23374, 0xa337d0520af9801, 0xde36cdf414827b4]
def page54 : List Nat := [0x42af1217149a30c, 0x5b40f72561c1214, 0xc530c433b89d214, 0x6362cc530dd732d, 0x6f571c5260c3979, 0x43b310f3249810e, 0xd20b7486549314, 0x48464427ee05701, 0xa33148110a7c865, 0xe5280c761482fa4, 0x832f1190788530b, 0x8110de628dc5364, 0x9f31842bb4a0364, 0x19520d9108ff864, 0xf38045f324429f2, 0x86edd223748710d, 0xe20abf488d9604, 0xde614823fe19711, 0xcb4718520dcd32c, 0xdf78cd9314836b4, 0x865fde043549108, 0xc120dce3649f314, 0xc126cc72f11f614, 0x5a2648510af7815]
def page55 : List Nat := [0x5c4354a364439b1, 0x876711c3758121e, 0xd810d6c57dc9604, 0xc0364873710f724, 0x633289910cdd365, 0xe62748516103b94, 0x86dd6044395910e, 0x9a10cbc478d9604, 0xc5260c2bb608434, 0xc67149830c7d57d, 0xed281c56010f3dd, 0x825f61c4395910a, 0x520dda365c0314, 0xc9314427be1d321, 0x5f7049b31adf68c, 0xf51705f624c31fd, 0x43f8e012148110c, 0x8520fe237485204, 0x5a36442af12136d, 0xa07045b32a7d289, 0x605648520442bb4, 0x867b61c4348520f, 0x8520abf48cd8604, 0x5e364827be1d321]
def page56 : List Nat := [0xe12149830c7e584, 0xcd28cc530483b38, 0x831fd637149830b, 0x8110ced3259c414, 0xc520443f40de314, 0xe03648520fe2264, 0x7d58dc5260c27bd, 0x86fc6044348110c, 0x520dcc36dc9314, 0xc4434ca7b4a3371, 0x57648430dcf825, 0x6d58dc5260c2bde, 0x827b423724c521e, 0x9910baf488dd214, 0xc0438879bd0a568, 0x6332cc1108ff865, 0xef7848530482f54, 0xc27d1e1214c3109, 0x9910e6f52dc5260, 0xc126cc6bb423428, 0xe0414da20c7f58d, 0xde36cdf614823fd, 0x439bd5f7149830c, 0x5a30e6e56899204]
def page57 : List Nat := [0x9d168c31f962274, 0x1c4349810cbe484, 0xfa8710d20442bb6, 0x82bde053245b409, 0xa31dac47485304, 0x4b314423fe1907d, 0x5d214983097d78d, 0x7c86549304439b5, 0x42ebd233748520a, 0x5a20add8610f320, 0xd9214823f61c434, 0x5f7158121bac484, 0x6d5849f314835d9, 0xc3378db37d8121d, 0xe20c7c5845f624, 0x9d214c27ee05701, 0x217049b10cdd381, 0xcf824c521cc2af1, 0x43d5cca564c510b, 0x8710ddb3241f318, 0xde264427d61c434, 0x6127cc5208ff680, 0x5c570dd604875bd, 0x8040000180207bd]
def page58 : List Nat := [0xef800b2e06965, 0x5dc000006620, 0xfb9bb8615c00000, 0x30000019548, 0x200006800000000, 0x91b10050c47680, 0x8bc000b90013ac, 0x7b0000180000000, 0xdec800000000015, 0x40034ed0b0014a, 0x2aaa0002f8040, 0xa40000044600000, 0x1ce0028c8000009, 0xc00000000000000, 0x128e8000000000, 0x20286340332f00c, 0x6780a0080200000, 0x89400006000001, 0x5880000, 0x8030, 0xb20000000200000, 0xbb3000000e28003, 0x200000800192650, 0xcf34006e70000]
def page59 : List Nat := [0x2000000d6400000, 0x80040200, 0x5ec38ded000, 0x400a0040000000, 0x60000000c0014c4, 0x51000f7c318006a, 0xaf98040000030ba, 0x1c2c3700001, 0x80026a003068000, 0x246e1b00001b63, 0xbbece7488d50040, 0xa000000005ff, 0x1338000000380, 0x29388b61e, 0xd0a5f0000380000, 0x1e88007e6a2e, 0x1e0000000000000, 0x300079e57e278, 0xb60000002800000, 0x2962e04000006, 0x3e80000000000, 0x8180052e0, 0x296b0ce00132e5b, 0x1500081a0002]
def page60 : List Nat := [0xf69e00358810ace, 0x112, 0x60000000a000000, 0xc860000000017, 0x4013d7bc2028000, 0x8980809257, 0x413000000022590, 0x6a980083600004, 0xe1317400000004a, 0x380000800000000, 0x500000054c2, 0xf66a0017ea89000, 0xa5cd16f20000042, 0x80025c80074e002, 0xed0000037480000, 0xe8180e53ab4d27c, 0x28598008e231, 0x10001dc8000, 0x6002, 0xc002008030000, 0x34d50000013d800, 0x166800009bcc0, 0x3443000, 0x6d1baa0000000]
def page61 : List Nat := [0xc002dda1f000000, 0x1c0301700000, 0x402000000001538, 0xdaa4004ad009a3, 0x800004000000020, 0xc000000040087f, 0x2748003a66, 0x61d086008000c3, 0x78c000007d663c0, 0xbb255c00000001, 0x4a8000180200000, 0x5000000002, 0x0, 0x23300096c000, 0x50000025e200, 0x3d0000011c8040, 0x200008d00000000, 0xffce19e90000, 0x3800000000006e5, 0x18000000000005, 0x41600000000000, 0x4008000a680, 0x200002002000000, 0x500200030]
def page62 : List Nat := [0x400002000000000, 0xa01a358000009f, 0x1c9000000000003, 0xc40000000000000, 0xd32000010006bb3, 0xed38920020e800, 0x15a800a0a0009, 0x41f000, 0x2ab0000180100, 0x137c004e5004000, 0xc30100700056d00, 0x2d0a010006, 0x6af940200000000, 0x40e6524000d9b, 0x562da010000640b, 0xfb99b0018, 0x780a0003c6c0a0d, 0x5726b1101028ec, 0x14cc0042b001, 0x42800b7a6fc0100, 0xf58c000c1000000, 0xb7c0000046, 0x477800b7f894000, 0x10002f300177]
def page63 : List Nat := [0x0, 0xbc0100000000000, 0x30000008cf2, 0x11502400095806, 0x6a40700000164c0, 0x4004b16bb800b8b, 0x1a800d3e0000d00, 0x7580066e000, 0xbd000000022af00, 0x26d80800c01a619, 0x320000000c40600, 0x14b00c0000011d4, 0x1000c7600001, 0xf576c8000000, 0x35f0015d4004b5, 0xcb5d18000000100, 0x1edad74800816, 0x0, 0x9fe774, 0x41e0000002500, 0x273fb7c000, 0x520000000000000, 0x1034f16802a, 0x35b80200000000]
def page64 : List Nat := [0xc20003c8160000, 0x78000019dc00461, 0x300d69af777, 0x27d98b000, 0x99ba90040000000, 0x12000030, 0x3d5820000000600, 0x4002dd742000031, 0x10001ab00881, 0xb2a03a64cfd0, 0x1200003f34c00, 0xc504000060000, 0x11d500000800000, 0x75fd0180000, 0xf00048ef5800696, 0x537000001db90, 0x200000006000594, 0x6ff2ee4880078, 0x4cb00065c000, 0x30be814b9600, 0x2738020, 0x400000, 0x100000, 0x14000]
def page65 : List Nat := [0x1800, 0x1c0, 0x400000000000020, 0x280000000000002, 0x2c000000000000, 0x3000000000000, 0x340000000000, 0x38000000000, 0x3c00000000, 0x400000000, 0x44000000, 0x4c00000, 0x500000, 0x54000, 0x5800, 0x5c0, 0x400000000000060, 0x680000000000006, 0x6c000000000000, 0x7000000000000, 0x780000000000, 0x7c000000000, 0x8000000000, 0x840000000]
def page66 : List Nat := [0x88000000, 0x8c00000, 0x940000, 0xa0000, 0xa400, 0xa80, 0xac, 0xb4000000000000b, 0xb8000000000000, 0xc000000000000, 0xd40000000000, 0x2042c000000000, 0x4045c00000000, 0x4244c0000000, 0x6042c000000, 0x6240400000, 0x6242c0000, 0x64420000, 0x6445000, 0x804000, 0xc00000000080418, 0x680000000008042, 0x4a0000000000804, 0x244c00000000080]
def page67 : List Nat := [0x8444c0000000008, 0x84450000000000, 0x8642c00000000, 0x8644c0000000, 0xa0450000000, 0xa046800000, 0xa244c0000, 0xa2478000, 0x22042c00, 0x22043c0, 0x24043c, 0x6c0000000024045, 0x470000000002404, 0x244c00000000240, 0x6042c0000000024, 0x26242c000000002, 0x26244c00000000, 0x26444c0000000, 0x264450000000, 0x26445400000, 0x26445c0000, 0x2a4434000, 0x2a443c00, 0x2a444c0]
def page68 : List Nat := [0x4000000002a4450, 0x5c000000002a445, 0x464000000002a44, 0x4478000000002a4, 0x20400000000002a, 0x420418000000004, 0x42042c00000000, 0x4204340000000, 0x440400000000, 0x44041800000, 0x4404340000, 0x440450000, 0x44240400, 0x44243c0, 0x44244c, 0x180000000046040, 0x42c000000004604, 0x244c00000000460, 0x6444c0000000046, 0x464450000000004, 0x4a045000000000, 0x4a244c0000000, 0x4a246c000000, 0x4a247800000]
def page69 : List Nat := [0x6204000000, 0x620404000, 0x62042c00, 0x62043c0, 0x400000000640420, 0x200000000064046, 0x44c000000006424, 0x42c00000000642, 0x604700000000066, 0x66242c000000006, 0x66244c00000000, 0x66444c0000000, 0x664450000000, 0x66445400000, 0x66445c0000, 0x68042c000, 0x68444c00, 0x6844500, 0xc0000000068642c, 0x340000000068644, 0x43c000000006a44, 0x444c000000006a4, 0xa445c000000006a, 0x6a4464000000006]
def page70 : List Nat := [0x6a446c00000000, 0x6a44780000000, 0x2022082c000000, 0x6046282c00000, 0x6202082c0000, 0x6206082c000, 0x6266282c00, 0x646648200, 0xc0000006466485c, 0x380000006c22082, 0x8500000006c2208, 0x284c0000006c240, 0xa284c0000006c24, 0x66484c000000864, 0x666485c00000086, 0x8c22082c0000008, 0x8c22083c000000, 0x8c24085000000, 0x8c2408640000, 0x8c24284c000, 0x8c26080000, 0x8c2608040, 0xc0000008c260818, 0x500000008c26082]
def page71 : List Nat := [0x8700000008c2608, 0x484c0000008c260, 0x2082c0000008c26, 0x220834000000ac2, 0xc22083c000000ac, 0xac440850000000a, 0xac44284c000000, 0xc224081000000, 0xc224083c0000, 0xc226082c000, 0xc22a484c00, 0xc42608500, 0xc000000c62a484c, 0x340000022002082, 0x838000002200208, 0x83c00000220020, 0x6282c0000022002, 0x2a483c000002202, 0x42082c00000220, 0x204428140000022, 0x22046282c000002, 0x22062082c00000, 0x22062083c0000, 0x2206a483c000]
def page72 : List Nat := [0x22c06080000, 0x22c06082c0, 0x22c460814, 0x340000024004080, 0x86c000002400408, 0x85c00000240220, 0x408200000024044, 0x64283c000002406, 0x204280000000240, 0x420428040000024, 0x242042810000002, 0x24204282000000, 0x2420428340000, 0x24204283c000, 0x24204284c00, 0x2422208340, 0x242442804, 0x100000024264282, 0x8140000024c0208, 0x8300000024c020, 0x208380000024c02, 0x2083c0000024c0, 0xc0208480000024c, 0x4c0208540000024]
def page73 : List Nat := [0x24c060804000002, 0x24c06081400000, 0x24c06081c0000, 0x24c060850000, 0x24c06087000, 0x24c4a284c0, 0xc0000024c662820, 0x2c0000026206282, 0x810000002622208, 0x484c00000264064, 0x648500000026406, 0x240854000002640, 0x424085c00000264, 0x6c0208100000026, 0x26c020814000002, 0x26c02082000000, 0x26c02082c0000, 0x26c240810000, 0x26c6a485000, 0x2a408684c0, 0x4000002a4220834, 0x5c000002a424283, 0x834000002a42648, 0x2834000002a4620]
def page74 : List Nat := [0x42834000002a464, 0x64820000002ac6, 0x242810000002c0, 0xc206082c000002c, 0x2c408283c000002, 0x2c408685c00000, 0x2c602082c0000, 0x420220834000, 0x42066282c00, 0x4206a48340, 0xc0000042c26082c, 0x340000044024085, 0x83c000004406408, 0x82000000442642, 0x2083c0000044c22, 0x2208480000044c2, 0xc2208540000044c, 0x602648480000044, 0x46222082c000004, 0x46c22082c00000, 0x46c2408500000, 0x46c242810000, 0x48c22080c00, 0x4ac2208100]
def page75 : List Nat := [0x4000004ac22082c, 0x3c000004ac22083, 0x854000004ac2208, 0x850000004ac220, 0x4284c000004ac44, 0x8685c000004ac4, 0x440834000004c4, 0x6242082c0000064, 0x66c04284c000006, 0x66c08485c00000, 0x66c2428100000, 0x66c68485c000, 0x68c46282c00, 0x68c4648500, 0xc0000068c464870, 0x2c0000068c64283, 0x8500000068c6628, 0x8340000068c664, 0x2083c000006a422, 0x6082c000006a44, 0xc642834000006ac, 0xc224083c000006a, 0x6c226082c000006, 0x6c226484c00000]
def page76 : List Nat := [0x6c408685c0000, 0x6c4220838000, 0x6c426085000, 0x6c42608700, 0x4000006c62a4810, 0x34000008ac64083, 0x85c000008ac6428, 0x83400000aca086, 0x4283400000cac64, 0x62c2c00000cac6, 0xc060c2c000602c0, 0x8c220c2c0006222, 0x4ac220c2c0006c4, 0xe220020c2c0006c, 0x6e220420c2c0006, 0x6e242042c4c000, 0x8c06c220c2c00, 0x8c46c220c2c0, 0x8e22c460c2c, 0x40008e260440c0, 0xc000008e260442c, 0x4c040008e260664, 0x40c040008e26066, 0x240c300008e26c2]
def page77 : List Nat := [0x242c080008e26c, 0xc0242c140008e2c, 0x6c220c2c0008e2, 0xc08c220c2c000ac, 0xac42c260c2c000a, 0xac46c220c2c000, 0xae22c460c1000, 0xae22c460c2c0, 0xc000ae2c0062c10, 0x2c000ae2c0062c2, 0xc2c000e0262220c, 0x2c2c000e2260262, 0x20c10000e226066, 0x220c34000ec2a42, 0x242c00000ec2a4, 0xc0242c04002200c, 0xc0242c08002200, 0xc0242c0c00220, 0x200c0242c100022, 0x2200c0242c14002, 0x2200c2240c0000, 0x2200c2240c080, 0x2200c2240c0c, 0x30002200c2240c1]
def page78 : List Nat := [0xc2c002200c2240c, 0xc000022e060462, 0x42c040024004044, 0x60c00002402202, 0x2264c080024024c, 0x42440c000024204, 0xc2240c00002420, 0x20c2240c0800242, 0x420c2240c0c0024, 0x2420c2240c10002, 0x2420c2240c3000, 0x242240220c000, 0x800242240220c04, 0xc00242240220c0, 0xc1000242240220c, 0xc1400242240220, 0x20c300024224022, 0x620c00002422402, 0x220c3400242240, 0x20264c080024264, 0x60264c080024e0, 0xe0606a4c100024e, 0x4e062664c080024, 0x24e06c220c30002]
def page79 : List Nat := [0x26006c220c5800, 0x26202c660c2c0, 0xc0026206c220c2c, 0x2c002620c2260c2, 0xc00002622c0062c, 0xc040026406c240, 0x40c100026406c24, 0x240c300026406c2, 0x240c100026406c, 0x6c240c100026426, 0x20062c2c00264e, 0xe020220c2c0026e, 0x6e020264c080026, 0x26e020662c2c002, 0x26e0c0242c0400, 0x26e0c0242c080, 0x26e0c0242c0c, 0x140026e0c0242c1, 0xc000026e0c0242c, 0xc0c0026e0c2240, 0x60c2c0026e0c224, 0x220c100026e0c22, 0xc020c0c0026e4ac, 0x6c020c0c0028424]
def page80 : List Nat := [0x28c462c2c002842, 0xc2c2060c2c002ac, 0xc26ac060c2c002a, 0x2e0062020c2c002, 0x2e0062060c2c00, 0x2e006c242c100, 0xc002e206c240c10, 0x2c002ec020662c2, 0xc00002ec060462c, 0xc000040e44c220, 0x60c2c0040e6c426, 0x220c2c0042c4ac2, 0xc220c2c0046c48c, 0x4c220c100046c4a, 0x2c0242c040046e2, 0xe2c0242c080046e, 0x6e2c0242c0c0046, 0x46e2c0242c10004, 0x46e2c0242c1400, 0x48c4ac220c2c0, 0xc004ae22c460c10, 0x10004ae22c460c2, 0xc00004ae44c220c, 0xc080066e0c2240]
def page81 : List Nat := [0x40c100066e0c224, 0x240c000066e0c22, 0x2240c080068e0c2, 0x6c242c000068e0c, 0x46c242c040068e4, 0xe66c242c000068e, 0x8e66c242c040068, 0x68e66c242c14006, 0x6ac68c462c2c00, 0x6ac68c642c3c0, 0xc006ae24c060c10, 0x4006ce4ac220c2, 0xc10006e226c240c, 0xc30006e226c240, 0x20c2c006e226c24, 0x440c00006ec2200, 0x462c2c006ec220, 0x60662c2c006ec22, 0x262062c2c006ec2, 0xc2a4086c5c006ec, 0xe2240221010006e, 0x401001000002700, 0x1e03c0500901201, 0x1602a04c088100]
def page82 : List Nat := [0x680d01a0340600b, 0x460800f01c0360, 0x48280500a014023, 0xb41682a0540a81, 0x606c0d81a833066, 0x208410800ec1d03, 0xc11022044086108, 0x4b0921202404708, 0xc2704d098130260, 0xa41482885009e13, 0x8580ac154298530, 0x802f85f0bc1742c, 0xce19c310620c21, 0x586a0d01a033867, 0x1cc390710e01b83, 0xd0f81ec3c8760ec, 0x418831062083f07, 0x62284488610a210, 0x8d11a2344688d11, 0xc4909211c238468, 0x3826c4c89912e24, 0x8a3146288510a21, 0xac550a814e29452, 0x16e2d45a0b315c2]
def page83 : List Nat := [0xf8be17a2f05c0b7, 0x30c610c01802fc5, 0x9192320638c7188, 0x650ca194328650c, 0x83506a0d0198330, 0xdc1b83686c8d41a, 0x6f8de1ba3746e0, 0xcc394720e11c238, 0xea1d43a4748e81, 0xd4798f31e63c878, 0x1f23dc7b0f51ea3, 0xe8fc1f43e87c8f9, 0x420831051fe3f47, 0x221c4348610b214, 0x8d91a22844c8991, 0x4809011f23c46c, 0x232464889012024, 0x49212324648c919, 0x5049c9392624c49, 0x92a2544a4949292, 0xb09612c2584b095, 0x2624c49812f25a4, 0xf13d2764e89c935, 0x520a39452885049]
def page84 : List Nat := [0xc29652ca5949290, 0xad95529e53ca714, 0x4584b095e2ba56c, 0x6a2d25a4b41672c, 0xb99732e45c0b71, 0xf05d8bb1752e85d, 0x183302600be1782, 0x28c498730c614c2, 0x31a634c618b3146, 0x9991322640c798e, 0x674ce99d334664c, 0x6348684d019f33c, 0xd81af35a6b4d59a, 0x66ecdd1b93686cc, 0xbe37a6f0de1bc37, 0xce09c13806fcdf1, 0x9672ce41c838e71, 0x9cf39c738e61cc3, 0x50e99d33a4744e7, 0x3b6768ec9d73a87, 0x29e43c8778ef1dc, 0x7a0f39e73cc798f, 0x63ea7ccf59ea3d2, 0xfe9fb3f47e8fc9f]
def page85 : List Nat := [0x480900a003fe7fc, 0xe41c83506a0940, 0xd0aa1442684d082, 0x3a86d0d21943085, 0x22143e87d0fa1d4, 0x9912a2444688d11, 0x4528a113a2644c8, 0x7a2e4568ad15a2a, 0x8d91aa304608c11, 0xf47a8f51e23a472, 0x2324448690920a3, 0xc9212424748e919, 0x564ac95129a5249, 0x92ea5c4b69692d2, 0xc298530a604be97, 0xa644c498930a614, 0xc13726b4d49a532, 0x4e89cd39a724e29, 0x27e4f89ed3c277, 0xa2142a83502a054, 0x2524a354628a510, 0x4b294526a4d49a9, 0xa614ba9752ea5d, 0xa2542a754d29953]
def page86 : List Nat := [0x552aa5548a8d512, 0x5eab5562ab54ea9, 0xab4566ac9582b05, 0xf15e2b556aad55a, 0x582afd5f2be578a, 0x4ac858eb1562ac1, 0xb45662cb592b256, 0x65aab49692d25a4, 0x6f2d95b2b5d6bad, 0x2b816fade5bcb79, 0xe65cab95722e25c, 0x576aec5d6bad75a, 0xf4be57baf45e4bc, 0xb05608c0d7fafd5, 0x318630b616c2583, 0x62cc558a311620c, 0xeb1d638c6d8d319, 0xc9591322644c818, 0xa652ca193b2564a, 0x98b3065ecb595b2, 0xce19bb3666acd5, 0x3e676ced9d33967, 0x1a0b4067ecf99f3, 0xa0d41a734968ed1]
def page87 : List Nat := [0xb566aad51a9b516, 0x8db135d6b8d69ac, 0x6c8d91b23646c6d, 0x4b696d0d9db3365, 0xdc5b8b706e0da5b, 0xa6ecdd9bab736e4, 0xc0b81700df5be37, 0xae2dc2b83704e09, 0x90720e3dc7b8d71, 0x1c9b92724e45c8b, 0x34e65ccb99730e5, 0xb9e73ce79cf39c7, 0xadd3ba1742e81cf, 0x760eb9d73ae758e, 0xc3b8770edddb3b5, 0xf09e03bd77aee9d, 0x7788f0de1bc3784, 0xe83cf798f25e43c, 0x4f69ec3d67a8f45, 0xdf7baf75eebdb7b, 0x1f43e77caf81efb, 0xd2fa5f4be87d0fa, 0xbf17d8fadf5bea7, 0xd9fabf47e8fd1f9]
def page88 : List Nat := [0x809005ff3fc7f4f, 0x7c0e81b03203405, 0x620bc1782d0460, 0xf83b0720dc19833, 0x13c268450820fc1, 0x50ca1842b8530a6, 0x3986d0d21a43386, 0xe2043f8730e61cc, 0x9b12e2544988f11, 0xc5189f13e2744e8, 0x562a4538a514628, 0x8b51662c4578ad1, 0x24618c11822f45c, 0x1aa33c668cb1923, 0x38e11c237c6e8db, 0x4147d8f71ea3b47, 0xf21e42c8590920e, 0x889112224448890, 0x432c8c915226444, 0x53c581a77918341, 0xa34fa712822aea9, 0x6b623d1c2b7bece, 0x40885dd7e16f20, 0x3e2711016441a4f]
def page89 : List Nat := [0xf565cee5718609d, 0xb44e4477b1daae, 0xb5b10500ee973b9, 0x50681a42bd7b925, 0x445a1182e9b4a1, 0xe006561a80d2e48, 0x17985f636e3c8f9, 0x850125e52a85205, 0x380037028060296, 0x9bab78341f8b1aa, 0x79722c5e97dbe0, 0x40303514208642, 0xa75a0002c854040, 0x878331dc5214e61, 0xf79006c70f4c516, 0x74c8526206add64, 0x1c5155af1810ee, 0x905d470af370612, 0x6b25808c2d0d202, 0x8192a3729eae236, 0x545a20415ad677, 0x5143e1f8300500c, 0x26d340b4b4375e4, 0x6109828440db2c9]
def page90 : List Nat := [0x188425f2d482c4, 0x586bc7b1316cb41, 0x3c2708de36a4514, 0xc08a747693d067f, 0x3dd8e1a04b1a44d, 0x4ac8616cb4c500, 0xa01978240b0480c, 0x4340c2d52284500, 0x222d67828079360, 0xbb057dee763ab69, 0x800fa0a01a51961, 0x3584b3bc40d6d60, 0x1180b81a0301040, 0x38014ff228a2d5b, 0x16f853043b2700, 0x301b5012f62f2f6, 0xea2281804b7c140, 0x5efd5a2388c1ad4, 0x2561c964007b8a9, 0x4ae8b6f6295cac0, 0x1b9c5d0d1b29100, 0x3af594d46734414, 0xc6c35e3e1edee4, 0x4637bc7854885a]
def page91 : List Nat := [0x6049c4160a0300c, 0xd38c07739bdc86c, 0x691c0494c172400, 0x30108c4413008e0, 0xb051adc0882c140, 0x3a5b23354dcc11d, 0x83402f3a2206825, 0x95cac110580a0a6, 0x1278828071d38, 0xd6e02806020d4a8, 0x8aa16d166b31968, 0x1403012c0bd407b, 0xb0a02c080200018, 0xbe9be10049a40c0, 0x1a6f360400602d7, 0x52e556ea0cb2b, 0x8441283c0e00002, 0x26a0500c4a2401, 0xc8f474b33d74036, 0x1a42c19e6bb5ba, 0x94475f10d832e1c, 0xc44212cd62b0578, 0x5100c46b154a83, 0x201108836d6e920]
def page92 : List Nat := [0x6b1582bcbd5f11c, 0x1409e005ebdc964, 0xacef00025ac882a, 0x980a29ee7308801, 0x99f3901470843c1, 0x1e00260002e0061, 0xf0b8888363b08e6, 0xa40352dc631d4ee, 0x241a6d40c06c6a1, 0xa01850e0d9c3952, 0xc01403010263a0, 0xfd3f5108c1f0b68, 0xdad31c5a032a869, 0x6180c907c068175, 0x4008710822f544, 0x23082f661a05810, 0x215826d4c1a6, 0x140305ddc663203, 0x9c9d64da5923868, 0x904602c4211700, 0x602836672e3e1e, 0x763bdc171f06828, 0xdf4214017824f4f, 0x139ad82ccbc83bf]
def page93 : List Nat := [0x312021b00d63044, 0x524e057906b3a5, 0xf04613968167f3f, 0xa86d8ac15f6d3dc, 0x52a92780500deed, 0x5c3b8b049ee2aa6, 0x2b1d8ac0bd33161, 0x404e5e3050c50e, 0xa961b03dc763a55, 0xe801835e176480a, 0x28745a1531c4236, 0x56bf2d9681609bb, 0xf7a02c140301310, 0xd808002d8a285a, 0x423e049b925064d, 0x200c82500340005, 0x82807948882c060, 0x60e7b9f48c0908, 0x638028060204e3c, 0xbc03a6d2c72d, 0x2a975802e1a1600, 0xe0502406025c82d, 0x8f022f70fc01a50, 0x8e1a76869b3421e]
def page94 : List Nat := [0xd4321268e6752f8, 0xcb0d5369aa61269, 0x46038030c6c28c4, 0xc8ed59a82299090, 0x3044e100500c2c0, 0xb22704b14012c9f, 0x60ce26ea04eb90, 0xa60b82a7c922dc0, 0x2d95c755d033499, 0xd220a8d4b705e63, 0xb04200a0480c040, 0xa220023244227d, 0x86ddeafd7cbde46, 0xe4d3a2a0a37522f, 0x221005024060c06, 0xc0d98e822307a8c, 0xb51042d14e2d6c1, 0x25e01b64200bb4, 0x570d429c7c0a00c, 0x3044e2411401838, 0x280400010000b51, 0x306af600640335c, 0x968328e483f4bf5, 0xb24708a55ee2a2d]
def page95 : List Nat := [0x70b2ee0101ae56a, 0x351051a14c61826, 0x16896d2a528cbd5, 0x50b2fa3c9c4d0d4, 0xaa542532f02406d, 0x4715810c0311256, 0x1108a04e2d04e93, 0x88917b491948402, 0xe09171b06602b60, 0xa9cbb8610734026, 0x8859c11270140d3, 0x132980e0e4d0801, 0x15e98cca465a810, 0x842bf651f8f07ca, 0x4fa58bc5a206e37, 0x68d805788a8300f, 0xb04120b7600d7a1, 0x42ad04c12260969, 0x2025a1a4a8082fa, 0x818066b69028060, 0xc1178b35982509, 0x52a065cb190da78, 0x3822f47a314ce85, 0x40140900c04014a]
def page96 : List Nat := [0xb04e0a4a0127b09, 0x7f9ba0d10cec561, 0x1b243bfd9f32443, 0x7f521d01109fae0, 0x861483fa21a4388, 0x9faec20c41bf0d, 0x3882905ff378991, 0x41b30d932482ffb, 0x524c5109facf98a, 0x4c36e9966c20f75, 0xec598a61bf81f62, 0xd995fd3711921db, 0xfcdc46486ffb822, 0x9b10dfeec90e817, 0x7fbb242206fd374, 0x93081f7cc730443, 0x6fd67ccb10cdaa4, 0x4438877e9326088, 0xdf2c0302437d5c, 0x3e64885f97010e2, 0x83fdcdd21c42ffb, 0x27580419fae19b6, 0xc2f693e62904fe, 0xa64b00839dd4916]
def page97 : List Nat := [0x8877f4395910df, 0x848520443fb10e6, 0x9b109fa4f9b083f, 0x7eb3e64886ed204, 0x934619fd5d26cc7, 0x5f97010630dfe62, 0x2604867f3b08690, 0xee8ad10a21fed8, 0xb243a04fd270d91, 0x21f78db314437eb, 0x324c510dbe649b0, 0x8c3fda0c40887d7, 0xc4e8b681bfd1d26, 0x887f637485109f, 0xd15921443f838a4, 0xdb109faed98c41d, 0xfa8be65886df324, 0x9b441d754931cc3, 0x6ff428d910dfe82, 0xd601076e21a6c08, 0x1bfa2fa3241bf49, 0x1e64886fc46d893, 0x21fb8d921483ee2, 0x6210530ff662902]
def page98 : List Nat := [0xccafeb8886886ff, 0xa0fa1263bfc5b06, 0x38877d524c110bf, 0x749f31cc3fa1ba4, 0x9830df88db0a657, 0x3eaba4d98e7f574, 0x18a417f9d843487, 0xeff46d81219fecf, 0x906cc6ffb826c90, 0x1ff443984619fd4, 0xb264885fd7210e3, 0x65bfd1860486fe3, 0x7049b10cfaafb0a, 0x487ef99660886fd, 0xe849b021fddc536, 0x7187dc364c110df, 0xf49c46442feb908, 0x85109fa4e8b4617, 0xbea946c887f4364, 0x8b6617f45f06ccb, 0x6fd214db40cfaa4, 0x952442fe1bac290, 0xbfee2996815f1d, 0xb242906fd67cc81]
def page99 : List Nat := [0x21bfd1f60487f63, 0x42899109fa4f9b6, 0x437e93662887ef, 0x88fb0a61b7d0936, 0x290efe1741b32df, 0xfdc931d03ef1b66, 0x9a30dfae0936637, 0x7e93a2c186fd714, 0x902217f0de26443, 0x7f521d0310ff68e, 0x4434cbbe994ac88, 0xdfc6fb02437f5c, 0x8ac021fdc368c52, 0x219fd5d268c67fb, 0x360c520dfe8f132, 0xd0b6f9920d98fde, 0xe6e30a413f5c336, 0x887e76148520bb, 0xf15d168c3bc2b24, 0x4930fdec290a419, 0x779ba4c0847f67d, 0x93021fecc520843, 0x5f57110f10dd86e, 0xd60106fe83e6488]
def page100 : List Nat := [0xdfa6c1b243bf4d, 0xe6da05ff670c52, 0x41bf8db414837e9, 0x61d01209f8ec98a, 0x4427fb3e64886ff, 0x8ce90a61fdcc521, 0xd184fd67ccb109f, 0xfd0d264437e20a4, 0xd21dfa6293681b, 0xfa93c62885ff67d, 0x20a41bf0df61482, 0x7ef7258121bda4e, 0xf314c37fa0ec290, 0xbfa4fa1a213fd9, 0x82428867c57d893, 0x837f9d843443fc3, 0x36d8520cfaa4836, 0x443f898a40886fe, 0x86e93421fdd0931, 0x29077c5789910df, 0x710f328437e9bec, 0xc930bba6e30a41f, 0x7e1bc4c8869c46c, 0xb0a616f11d36483]
def page101 : List Nat := [0x6fd2745840dfe8f, 0xd218c37ebb24398, 0xfd88c90a41f78d, 0x3886a96fc46d852, 0x217fcdc604863fb, 0x724c120efcac902, 0x4c3be2b242885ef, 0x887996213f45f62, 0xc90dff37d0a10fb, 0xf11b524c36e9b06, 0x8510dbe6d1b2418, 0xfcb8063107f6368, 0xb0243ef91d60486, 0x7dc434cb10dfe63, 0xa61482fe1ba4088, 0xdf88d30243bf11, 0xb086085fd07d0b1, 0x213f49f614c27eb, 0x714c930ff46c902, 0x443ee99662885df, 0x8aeb0063fe10d20, 0x29057f67d4910cf, 0xf95e26443fb98ec, 0xf10df88fb12639]
def page102 : List Nat := [0x7fb3882905fd701, 0x98a613fd9f31482, 0x5f4714d920fbe82, 0xb30443efa186c88, 0xfbe6498a21bf89, 0x16c2987df314c12, 0x21bdd86614837fa, 0x4789910dde65132, 0xcc37f98a4d086fc, 0xe6d98a41bf48516, 0x4986ff468d920fb, 0xe4dd204437e21ec, 0x8510dfc6da0a43f, 0xfe8be84887f0704, 0xb0243f50d931442, 0xddd07ccb31df88f, 0x5268437f13ac020, 0xcfaa5b0a61bf5c, 0xb2608867d574983, 0x21fd11a21443bf2, 0x21cc3109fa4f1b2, 0x843fc1b240887f5, 0xa2f996217f45f32, 0xc885ed270c520be]
def page103 : List Nat := [0xf11d16883bea906, 0x8520fd24290221b, 0xfe9be8c90efe365, 0xb0243bd0c761482, 0xe7f5749810feee2, 0x761483dfa3c6c90, 0xfca4290221fd0c, 0xa2d187ef314852, 0x41fb485204437e9, 0x17d8930fd6e090a, 0x8c23e3b2a4986ff, 0x86db0a41bfd1d16, 0xc187dc4318532df, 0x7ccb314433ba962, 0x110fee8518a21f, 0xf230a42907f621d, 0x90a217b5c843483, 0xfed3210520bf86e, 0x936843efb3e6498, 0x1efea598a219f54, 0xb682886ff4741a2, 0x217f41f424c37f1, 0x71498309f8ec992, 0x107f7a0a42906ee]
def page104 : List Nat := [0xee08b665bf8dd60, 0x887f837482109f, 0x70dd218c3f51324, 0xd21bfae221c617, 0x7e8bc6c905f5711, 0x1b221bfdc56010e, 0x6ed2149840db887, 0x132d077638a4c18, 0x9fcec21a437fdc, 0x3a41087f8468811, 0x417f45f424c7fc2, 0x27cc530dfe8e8b4, 0x4c37e83ec2995fd, 0xee49b621bfd1f62, 0x885fd710d9209f, 0xfcdb61483fa38a4, 0x8530fb86d98241b, 0xee9ba43986ef628, 0x18a41fecdd20443, 0x5fd270d910db86d, 0x5324437e8bec498, 0xdfc4da02217fdc, 0x1ec2997ed321852, 0x835f5c04354b7e2]
def page105 : List Nat := [0x464d921dda64930, 0x4833fa96c2986fc, 0xae18b665bf8df61, 0x2907de3748430bf, 0xf8dd26c42ffb3e8, 0x49309faec20c61b, 0x3eb3ea40863c465, 0x21a437fd9f43482, 0x67d52d8131bfae2, 0x56010f7fb3a4298, 0xcfea48b461bf9c, 0x3e86885fd17d0d2, 0x21fb89921442ffb, 0x26cc110df88d1b2, 0xccb7fa0a4d186fd, 0x86c98241bfdc116, 0xc186ff3245a30fb, 0xcdc12144377b8a4, 0x8121bfa0fa3243f, 0xfcb8a41086fc365, 0x992215f41f4354b, 0xff5214c110fea2f, 0xf624c6ffb8a65a0, 0xbfa4f98a21bf41]
def page106 : List Nat := [0x32c090ddc375852, 0x837fcdf418837fa, 0x7048710dfeec990, 0x443fdb8a40887f5, 0xc6eb0243fed0120, 0x2985fd7610d21fb, 0xf11861483afa966, 0x5a30bfa0fa0a41b, 0x3fbb2a5a06f6214, 0xa1a437ed9e20442, 0x67e5745a20bfa0f, 0xf418c3779924c08, 0xdfec3982417f49, 0x3ec498fef364852, 0x617fd9f424437fa, 0x5745840dbec498a, 0xd03fa23a438867e, 0xe65b0263bf48516, 0x518efe26d0510db, 0xbcca26442fe83e8, 0xc920bfae01b243f, 0x3f2ba2d187cc364, 0x83443fb5c121483, 0x7dd32d0530dfa6e]
def page107 : List Nat := [0x260487fa1ba4288, 0xdf8868b461bed8, 0xb660886fc369852, 0x433f89d160c3ee1, 0x36d0521bfe6fa32, 0x107f690e80906fd, 0xee49b0217fdc132, 0x90efc3618121db, 0xf41e21cc2ff9bec, 0x9810dfce2930617, 0xffb3c62906fc434, 0x90221f7cc5214c2, 0x6fc4349a30ff08e, 0xd60487f9b8a4088, 0xbbae221e65df15, 0xb062906fc468d92, 0x617fdc9304436f1, 0x3758121df887b0a, 0xd0bfba1c42885fc, 0xea5a30213fdc116, 0x21efd37d8121c7, 0xf487368437eb8ac, 0x85209fee29b441b, 0x7e90e6c207ed32d]
def page108 : List Nat := [0x98621af119214c3, 0xeff42d8131fbe65, 0x961482ff9bcc090, 0xfd26490221bf0d, 0x8c40886fd67cca1, 0x659b549260c3fd9, 0x264c510df82e836, 0xccaffb8a6c906fd, 0xa2d83665bf45d06, 0x48877e5758121df, 0xbd5d26043efa1e6, 0xc120fee8e90a219, 0x7fa3a4d18fed21c, 0x23221bfcc761483, 0x6ff4145a30bfe6e, 0x8464436e9966d88, 0x1dfc4c98a21df54, 0x30c2995fd078d92, 0x21bfd88314c37e2, 0x7149a30ff260902, 0x482fe83e62904ff, 0x86c98a43bfd0f61, 0xc887df3748530fb, 0xf10e564433e2bc4]
def page109 : List Nat := [0x8520bfecf98a41d, 0xfd9ba41087ec364, 0x99683bfd0526843, 0xefe2741b31dfeec, 0x5214837f9bec090, 0x1efe652b221fb4c, 0xb086884fd7610d2, 0x21dfd5c364827f3, 0x3258520feee090a, 0xccb7b98ec2907ed, 0xee090a61bfc5d06, 0xc8867f5258031bf, 0xfdc9314437e1b44, 0xd10dfa6cb02437, 0x7ebb242205f9701, 0x83685fe10d20843, 0xeff37899109fc2e, 0xd21483f7b926290, 0xbfee090e81fb11, 0x824d18efd36d852, 0x617f45f434427fb, 0x4349b10ddc42930, 0x8c37e9920da0efc, 0xeafb0a65bf11d16]
def page110 : List Nat := [0xc086fe7058443cf, 0xf54b460c37f9ba4, 0xd910fbe6c98a418, 0xfc83c62907f5710, 0x98c21bf19d214c2, 0x4ff7049b31fbe65, 0x926043fc2324088, 0xbba0f992639bd4, 0x8a6c904fd678844, 0x21d7549314c2fbb, 0x7010530fe86d10a, 0x487ee21e64085f9, 0x88699221bfd1a36, 0x298ddf704cb31fb, 0xf49f36d03ee9968, 0x5a20df86fb02433, 0x7fb92c221eff314, 0x8b6877f49e36442, 0xfdd32105309fee0, 0xc31482fe83e6c90, 0xfea6290a213f59, 0xbec4985bc474c31, 0x431f5db528c77f0, 0x478c520bfc6eb02]
def page111 : List Nat := [0x442feb3e8690dbf, 0xcae83665fd11a31, 0x2905df724c730cf, 0x7cc5368827eb388, 0x8510dfc4e8b061b, 0x7fa3ec2907f7414, 0xb0087fdcc461483, 0xcfd678c5209fee4, 0xa264437e236c090, 0x1d7a43a3061bf11, 0x9262986fd7149b3, 0x217edc121842efb, 0x7049831dfa60936, 0x4c27f13a2da1efe, 0xe6fb0a41b7ccb61, 0x221efc3698121df, 0xfd8b314c37fb92c, 0x4b31fba2f99261b, 0xfd982408847f765, 0x18c41bfd07614c3, 0x5dd27cc5309faec, 0xf614c2feb888c99, 0x1dfe8db0a41bf49, 0xba2d105df67cc93]
def page112 : List Nat := [0x21bf10f614833e2, 0x7610e20cbea49b0, 0xcc2be93cac884fd, 0xe6f30a4177dc532, 0xd984fd2745830bf, 0xd11d214436f98a4, 0x5830cf8ae83443f, 0xfa232628867d524, 0xa0a61fe8dd20443, 0x6ff1641b32bfa4f, 0x16110f7fbb24218, 0xdfe6e93621bfdc, 0x66d886fd214584, 0x637fdc5304837e9, 0x214c310dfa4eb00, 0xc37fa30c2907f5, 0xa2fa1aa51f59f52, 0x90eff7258043af, 0xf5c96010f7fa0ec, 0x8121bfa0f10a61b, 0xfeb9087886ff369, 0x9b243fc8c520442, 0x5fd27cc630fbc6c, 0x931443fa90e6088]
def page113 : List Nat := [0xdbe6c98a41f70d, 0x3264907f717cc91, 0x41fedc121443f7a, 0x52cd810bfe6e20c, 0x4837f9b2c090e5f, 0xa6e90e216f11d61, 0x2185f97010620fe, 0xfcdf420427fbb24, 0x5a20df88fb0a657, 0x7eb3e64086fc374, 0x9b421775c043cca, 0x6fc47d8930dfe82, 0x1260c77e9b0c290, 0xceaa48b0613fdc, 0xb662886fd764863, 0x617f5c043487be2, 0x7010e21bfee090e, 0xc42feb908c98dfd, 0x2e021a417fdc930, 0x7085f7714c310bf, 0xb49e31482feb888, 0x8510dfe84834637, 0x7e382c221efe364, 0x90a217d5c443443]
def page114 : List Nat := [0xefd31d8121ddc4c, 0xd214c27f13a0da0, 0x9fae19b4433fd9, 0xb660887f7424c71, 0x43bf0dd26c43bf2, 0x3049b10b7e8e302, 0x4867eb3c42186ff, 0xc6c30a41f70dd60, 0x2886fc4749a31df, 0xf11d60487fb1b24, 0xc920fee8690a216, 0x7f0ba0d997ec464, 0x90a417f5c8434c6, 0x7df368d921fde8e, 0x960486fe9388298, 0x9faec21c43bf11, 0xbe8c906ff4749b1, 0x21f310d32482ff9, 0x6058121dfa429b4, 0x842ef1bac090ffb, 0xae221aa53fdc936, 0x2986fc414da20af, 0xf54906cc67fb386, 0x5830df88cb0a419]
def page115 : List Nat := [0x7e98a2da06f6274, 0x30a41bd885160c3, 0xfef4648520dfc6d, 0xd214423eb3ea598, 0xdfc4d98a21fd10, 0xbe65986ff764873, 0x219b55d260c2ee8, 0x4348520bfe6fa12, 0x4c23e3b2a4887ec, 0xc62936817f41f41, 0x21ded27cc521df, 0xf89d161037e38ac, 0x9810dfce093663b, 0xbfa14ac886fc374, 0xa1621bf1d921cc3, 0x6fd214d840bfe6f, 0xc364433e2b44c88, 0xfb887b0a65f710, 0xb0869067e568991, 0x61d754b314c2ff3, 0x17d0d32dfa428b0, 0x482feb8082905dd, 0xe8e934217fcdc41, 0x5086bc4688530df]
def page116 : List Nat := [0xfd1c614827eb3e6, 0x9830efaa5982216, 0xfeb8086906fd714, 0x90421bfd8b404c2, 0x6fc464d920fd242, 0x5304835f10e8c18, 0x2fba6290e61fb48, 0x3862906fc7045b3, 0x617f5c8430427fb, 0x3748110dfa4e8b4, 0x486fbb9262885ff, 0xc4e8b661bfd0f60, 0xd1877d578d9219f, 0xbd0a264437e18a4, 0xdb41bfa0fa1221b, 0xfe9bcc090cfd27c, 0x9b081f7cc930442, 0x5fd17d0d21dfc42, 0x8604876e23a6c08, 0xdfa0fb0a61bfcd, 0x9261886fd26d011, 0x437f41f43887ef9, 0x17cc930df86db02, 0xccbbf2bc4c885dd]
def page117 : List Nat := [0xa648b681bf5c116, 0x3a07f6264c510df, 0xf11d60486fe93c6, 0x1a219feec90881e, 0x6e996c2986fe374, 0x20a617f5c443483, 0x7df17cc930bbe6e, 0x906ccb7f3822d99, 0xfda6c90a41bf45, 0xb0c2907fb474821, 0x21bb485260c37f9, 0x3749a10ddc4c902, 0x486feb808c90eff, 0xa6e90a417bdc931, 0x2906fe264c110fd, 0xfdc131486ff9bec, 0x8930dde8e930217, 0xe6996629067e57d, 0xb0243bfd0d06887, 0xeff4145a20bfa6f, 0x9260c27e83ec498, 0xfbe6e90e619bd4, 0x1ec090efe21cdb4, 0x657f5c4434c37e2]
def page118 : List Nat := [0x2149a30bbae221a, 0x443ee1ba42186ed, 0xee290621dfd4836, 0xc186ef4249810be, 0xf49d06cc77a93a2, 0x8931dfa63b0a41b, 0x7f1b44c886fc43d, 0x30243b7cc936843, 0x5dc3758121bbe6e, 0xd268437e21a4c88, 0xbfa2fa1461bf11, 0x3ac018ff8374811, 0x21fed0d204427f1, 0x3648110fea6e90a, 0x4c37f38a4d186fc, 0xc6db0243f7d0931, 0x2987765648510df, 0xfd1e364877fb168, 0x8532bf2e018a416, 0xfbb3c62886fe07d, 0x982417f45f32442, 0xffb4148210dfec2, 0xc604877f9b6c090, 0xbbc6eb0a417f4d]
def page119 : List Nat := [0x922c207f6214c11, 0x61bfccb614c33ea, 0x7010530bfae421a, 0x103ee21c6c885fd, 0xe8f9b243bd48516, 0x907ef724d921b7, 0xf45f328c2de23a6, 0x1a21dfe87132217, 0xfc90e61186fc374, 0xa92217f49c314c3, 0xcfd2745840efe86, 0x1268c77eb92c221, 0xdfc6f13221bfdc, 0x3242887dd314853, 0x417f45f42843fa2, 0x7148310fdae41b2, 0x443f7a1a42907f7, 0xee293461fe10e20, 0xc907ef7048520df, 0xfcc856442fe8be6, 0xc610bfa2fa1261d, 0x7e83ec2995fd27c, 0x20a41f948520c42, 0x6ff7049831dfc6c]
def page120 : List Nat := [0xd268c37fb0a4298, 0xdfe83b0263bf11, 0x38829847f765483, 0x61bfcdd168827fb, 0x4618121cdeae930, 0xd02fa8be64886fc, 0xc4c90221bf88536, 0x29067c5741b32fd, 0xb5c5260c3f69968, 0x8710bfe6fa0a41b, 0xbd2b440887f7474, 0x8b061775c0434cb, 0x7dd07cc931dea42, 0xe214c3bd2b24088, 0x9fee2936613fd9, 0xb8c090dff371852, 0x417dd9e21442ee9, 0x57d8532fd0e090a, 0xc42fe8bc6c9077d, 0x26290221bfd0936, 0x3085ff3711920ff, 0x74dd214c3fdb824, 0xc610dfc4fb0a61f, 0x7fa122d185f907c]
def page121 : List Nat := [0x102217b5c843487, 0x5bc474c110ff06d, 0xa218c2fe83e6588, 0xbfa4e18c613f5d, 0xba42885fd17cc93, 0x21bf89d600c7fb9, 0x7058443dfe86936, 0x8437f13a2d186fd, 0xe8e930213f5d843, 0x4906fe21cd840df, 0xf1c1260c6f7b8a6, 0xc5218fecfa9221b, 0x7ebb086907de364, 0xa02617f85d06cca, 0x5fd7210d10dfec3, 0x9364873f2b46c88, 0xdd88693021bfd1, 0x8a4d185fd078874, 0x618fd4b460c37e3, 0x36cc520df82fb12, 0x43bfabc6c90fdd, 0xad10221bf11d26, 0x58857d2715910ef, 0xfcdd20c43efa1e6]
def page122 : List Nat := [0x9a31bfa4e20c617, 0x7ebb242186fc434, 0x21c41bfd8b414c7, 0x7f6268c510bfae2, 0x906cc6ef9bc4298, 0x19feec99621b74c, 0x3a2c206fe07d893, 0x21fb4ca614827f1, 0x4698121feee2902, 0x4c27fb82c221eff, 0xeec99083a711932, 0xc906fc4741a219f, 0x70d831482feb888, 0x8110bf86e90c21f, 0x7e23ec29077c564, 0x9b421fd10e21443, 0x6ff670d921dfe84, 0x126c433ea922d18, 0x1dfee093663bfd0, 0x1a0d10e3f52d1a3, 0x219fd49160c37e2, 0x4148110dfa6f132, 0xc37b10a2c207fb, 0x88693421bfdc526]
def page123 : List Nat := [0xd986fe3658121df, 0xf49b414436f9922, 0xc520df88d1b243b, 0xfba1a43884ff764, 0x9b083bf4db60487, 0x7df31cc1209fa0f, 0xd218c2fe1ba4188, 0x9fee49b021f70d, 0xb262885fd700c52, 0x61fe58060487bb2, 0x2741b31dea428b4, 0x4837fa3ec2994fe, 0x88e930217f1d931, 0x2884ff7149830dd, 0xd8dd21c43fba0a6, 0x8520bf2e021c21f, 0xfbb9263887ec374, 0x93621bf5c1268c6, 0xefd7049831df88e, 0x434437e3824d98, 0x9feec90c617f5c, 0x1c4c887d7324c71, 0x21bf0d9214437e2, 0x7149830bfa4fa1e]
def page124 : List Nat := [0x8c3ee9b06c90efc, 0x8868b4413f89d16, 0x3187ef3748520df, 0xb485268437fbb24, 0xf10cfaa51b221b, 0xffb3e8498cfd761, 0x1b241df10d52442, 0x5fd07cc521efaae, 0x41483ef98a4398, 0xfdc6e90a417e5c, 0x3242886f5611852, 0x21ef51e36487f31, 0x6413000bfae421c, 0x801202205c00002, 0xc0045ed2af00, 0xa0000041db00208, 0xd2d55cd00400000, 0x32900015f5a, 0x501005001c01000, 0xf03600052f53129, 0xc2c705a00648, 0xe00000600001600, 0x64701600a00c00, 0xb700400406c00]
def page125 : List Nat := [0x238700200000401, 0xb0226ad01e00004, 0x73d63700000005, 0x1200401432100, 0x2b00407500a00, 0x300000000000800, 0x400200000000083, 0x600000200400, 0x900000800001000, 0xc0000000106c328, 0x400000022501d01, 0x20000027af00e07, 0xb00400405a02000, 0x273f3fd33b06344, 0x272700014b00, 0xb0080b42cf00000, 0x400000002a00020, 0x64f01200a00a04, 0x368100000000c00, 0x90267fb00800a11, 0x80000000000102e, 0x200001877d01, 0xa00052700000, 0xa0007576e300000]
def page126 : List Nat := [0x70520000080db00, 0xc00418300200a07, 0x602813300082d02, 0x201600001c51b00, 0x47f301020104, 0xd0000160243ab00, 0x819d0180000a254, 0x800000243900e00, 0x11a500a00459b03, 0x37390000402f314, 0x27c300c0160496f, 0x3808100600000, 0xf00000e00002000, 0x702207801a0245a, 0x428b63d00801403, 0x600c62701, 0x600265900200000, 0xc00000034300, 0x600000200e46d00, 0xf00200000081700, 0x500000a0060000a, 0xa0040044ad53b6b, 0x20002bb5e300006, 0xe00a00200203003]
def page127 : List Nat := [0x50000100e14d903, 0x800001a0020020c, 0x402602e4710f500, 0xa48d01400200, 0x400258b01248100, 0x66543100, 0x200229d05a00, 0x70100400000c00, 0xf01a00001200a00, 0x200036500819b78, 0x1000000000001, 0x5d40565100, 0xe00000610500, 0x505400008000000, 0x400601e00000269, 0x501204000200000, 0xa05e05868, 0xe02000000200, 0x50000020b100000, 0xd01c0161ed0026c, 0x6c700200000043, 0xa00800200, 0x20083d117f02800, 0x20005a102600200]
def page128 : List Nat := [0x401852100000001, 0x600a00000c56504, 0xe01c00a00415b01, 0x200e00244300400, 0x30000c600201000, 0x406201800003, 0x6bb0000280000a, 0x703e01201400400, 0x1e7b900400014, 0xa2e138b00000, 0xe00200600200000, 0x1609101000002, 0xd0000040d600600, 0x20000000040022f, 0xa01600a4f103a00, 0x428101401400400, 0x200000004, 0x20e200000007b00, 0xc08400000800001, 0x1400000871700, 0xf00638300e00000, 0x4b500023d0f, 0x20000000, 0x800000000010000]
def page129 : List Nat := [0x600000000002, 0x100000000, 0x2c000, 0xd00000000006, 0x1c0000000, 0x3c000, 0x1200000000008, 0x260000000, 0x800000000050000, 0x170000000000a, 0x300000000, 0x64000, 0x1b0000000000d, 0x380000000, 0x74000, 0x1f0000000000f, 0x400000000, 0x84000, 0x2300000000011, 0x480000000, 0x94000, 0x2700000000013, 0x500000000, 0x8000000000a4000]
def page130 : List Nat := [0x2d00000000015, 0x5c0000000, 0xbc000, 0x3100000000018, 0x640000000, 0xcc000, 0x350000000001a, 0x6c0000000, 0x800000020400000, 0x810400000004080, 0x102160000000, 0x20434000, 0x810f00000004087, 0x1022a0000000, 0x20458000, 0x10400000008080, 0x2020c0000001, 0x800000040420000, 0x10e00000008086, 0x202280000001, 0x4045c000, 0x9010000000808e, 0x212080000001, 0x800000042420000]
def page131 : List Nat := [0x90f00000008486, 0x212260000001, 0x800000060410000, 0x810e0000000c085, 0x302280000001, 0x60458000, 0x89040000000c08e, 0x3120a0000001, 0x80000006242c000, 0x91020000000c489, 0x322080000001, 0x64420000, 0x91170000000c88a, 0x322380000001, 0x80000008042c000, 0x11400000010086, 0x402340000002, 0x80470000, 0x90500000010094, 0x412160000002, 0x80000008243c000, 0x111300000010489, 0x422280000002, 0x80000008445c000]
def page132 : List Nat := [0x111c0000001088c, 0x432000000002, 0x800000086404000, 0x190600000010c82, 0x432160000002, 0x8644c000, 0x191700000010c8a, 0x432380000002, 0x8000000a0450000, 0x891b00000014489, 0x5123c0000002, 0x800000220400000, 0x810200000044080, 0x1102080000008, 0x220414000, 0x810a00000044083, 0x1102160000008, 0x800000220430000, 0x810e00000044086, 0x11021e0000008, 0x220454000, 0x811b0000004408b, 0x1202000000008, 0x240404000]
def page133 : List Nat := [0x10500000048082, 0x12020c0000009, 0x240420000, 0x10c00000048085, 0x12021a0000009, 0x800000240438000, 0x11000000048087, 0x1202280000009, 0x800000240454000, 0x1190000004808b, 0x1202360000009, 0x240470000, 0x90100000048480, 0x1212080000009, 0x242414000, 0x90800000048483, 0x1212140000009, 0x800000242430000, 0x90e00000048486, 0x12121e0000009, 0x800000242448000, 0x91500000048489, 0x12122c0000009, 0x242464000]
def page134 : List Nat := [0x81010000004c080, 0x1302080000009, 0x260414000, 0x81080000004c083, 0x1302160000009, 0x260438000, 0x81140000004c089, 0x13022a0000009, 0x260458000, 0x89000000004c08e, 0x1312020000009, 0x800000262410000, 0x89080000004c482, 0x1312160000009, 0x800000262448000, 0x91000000004c489, 0x1322040000009, 0x800000264410000, 0x910a0000004c882, 0x13221c0000009, 0x264440000, 0x91130000004c889, 0x1322280000009, 0x800000264454000]
def page135 : List Nat := [0x911c0000004c88b, 0x1402160000009, 0x280434000, 0x11c0000005008a, 0x141216000000a, 0x800000282434000, 0x91300000050487, 0x14221a000000a, 0x80000028443c000, 0x111400000050889, 0x14222e000000a, 0x8000002a4410000, 0x910e00000054886, 0x15221e000000a, 0x2a444c000, 0x91150000005488a, 0x15222e000000a, 0x2a4464000, 0x911b0000005488d, 0x15223c000000a, 0x2a449c000, 0x810100000084080, 0x2102080000010, 0x800000420414000]
def page136 : List Nat := [0x810d00000084085, 0x21021c0000010, 0x80000042043c000, 0x1000000008408a, 0x2202080000011, 0x440418000, 0x10d00000088084, 0x22021c0000011, 0x44043c000, 0x11400000088088, 0x22022a0000011, 0x80000044045c000, 0x11c0000008808c, 0x2212020000011, 0x800000442410000, 0x90800000088482, 0x22121a0000011, 0x44243c000, 0x91300000088488, 0x22122a0000011, 0x800000460404000, 0x810b0000008c082, 0x23021c0000011, 0x460448000]
def page137 : List Nat := [0x81170000008c08a, 0x2302380000011, 0x800000462410000, 0x89130000008c485, 0x23122c0000011, 0x464408000, 0x910a0000008c884, 0x2322260000011, 0x464450000, 0x10d0000008c88e, 0x24121e0000012, 0x80000048642c000, 0x811400000090c8b, 0x2512260000012, 0x4a246c000, 0x81000000009448f, 0x3102020000018, 0x620410000, 0x810a000000c4083, 0x3102160000018, 0x620434000, 0x810f000000c4087, 0x31022a0000018, 0x62046c000]
def page138 : List Nat := [0x108000000c8082, 0x32021a0000019, 0x800000640438000, 0x114000000c8087, 0x32022e0000019, 0x800000640464000, 0x11c000000c808d, 0x3212080000019, 0x800000642420000, 0x90f000000c8486, 0x3212260000019, 0x800000660400000, 0x8104000000cc080, 0x33020c0000019, 0x800000660420000, 0x810e000000cc085, 0x3302280000019, 0x660470000, 0x8901000000cc480, 0x3312080000019, 0x662414000, 0x890b000000cc484, 0x3312260000019, 0x662458000]
def page139 : List Nat := [0x9101000000cc880, 0x3322040000019, 0x800000664410000, 0x9108000000cc882, 0x3322180000019, 0x664438000, 0x9113000000cc889, 0x3322280000019, 0x800000664454000, 0x911c000000cc88b, 0x3402000000019, 0x800000680404000, 0x106000000d0082, 0x340216000001a, 0x800000680434000, 0x114000000d0087, 0x340236000001a, 0x680470000, 0x901000000d0480, 0x34120a000001a, 0x80000068242c000, 0x90f000000d0486, 0x341226000001a, 0x682468000]
def page140 : List Nat := [0x1105000000d0880, 0x34221e000001a, 0x68444c000, 0x1117000000d088a, 0x342232000001a, 0x684470000, 0x1901000000d0c80, 0x34320c000001a, 0x80000068642c000, 0x1914000000d0c89, 0x34322e000001a, 0x8000006a4410000, 0x910e000000d4886, 0x35221e000001a, 0x6a444c000, 0x9115000000d488a, 0x35222e000001a, 0x6a4464000, 0x911b000000d488d, 0x35223c000001a, 0x2022082c000, 0x820b0000404c901, 0x103104160000810, 0x80002066282c000]
def page141 : List Nat := [0x820b0000584c105, 0x2122141e0000b19, 0x80006006282c000, 0x8a0b0000c04c105, 0x310104160001811, 0x80006206082c000, 0x2000000c484105, 0x312304160001891, 0x80006246282c000, 0x92020000c4cc505, 0x313414020001899, 0x80006c220814000, 0x820c0000d844105, 0x3611042a0001b08, 0x6c220858000, 0x2010000d848100, 0x361204080001b09, 0x6c240830000, 0xa000000d84810a, 0x361214020001b09, 0x6c242808000, 0xa050000d848502, 0x361214260001b09, 0x82440800000]
def page142 : List Nat := [0x9202000104cc100, 0x431214020002099, 0x800086440800000, 0x820000010c88500, 0x433324000002198, 0x86664804000, 0x921300010ccc901, 0x4333242e0002199, 0x80008c220814000, 0x820c00011844105, 0x461204000002308, 0x8c240804000, 0x20c00011848101, 0x461204280002309, 0x80008c242800000, 0xa0200011848500, 0x4612140a0002309, 0x8c24284c000, 0x82010001184c100, 0x4613040a0002309, 0x8c26082c000, 0x82140001184c106, 0x461304380002309, 0x80008c26282c000]
def page143 : List Nat := [0x92050001184c900, 0x561104160002309, 0x8000ac22083c000, 0x820b00015848509, 0x562204280002b09, 0x8000ac44284c000, 0xa0200018048500, 0x601214060003009, 0x8000c0242810000, 0x8a0b00018048502, 0x611204000003009, 0x8000c2240808000, 0x20400018448101, 0x611204180003089, 0x8000c224083c000, 0x92030001844c105, 0x611324080003089, 0xc2264814000, 0x8a0b0001884c10a, 0x60414160008301, 0x20c26282c001, 0xa0200041888500, 0x62214060008311, 0x20c442810001]
def page144 : List Nat := [0xa0d00041888506, 0x622142c0008311, 0x80020c46282c001, 0x8a0b000418c8507, 0x633142c0008319, 0x80020c664800001, 0x9204000418cc900, 0x63324180008319, 0x20c682800001, 0xa0b000418d0501, 0x6342400000831a, 0x20c684804001, 0x1a0b000418d0901, 0x6343418000831a, 0x80022002082c001, 0x20400044004107, 0x101314160008809, 0x800220264808001, 0x820b00044054907, 0x102204000008810, 0x220440804001, 0x20300044088101, 0x102214000008811, 0x800220442808001]
def page145 : List Nat := [0xa0400044088501, 0x1022141a0008811, 0x220442858001, 0x82160004408c100, 0x1023140a0008811, 0x22046282c001, 0x820b0004408c506, 0x103324040008818, 0x8002206a483c001, 0x82040004580c100, 0x1603040a0008b01, 0x22c06082c001, 0x82150004580c106, 0x1603042c0008b01, 0x80022c080814001, 0x20f00045810105, 0x161304160008b09, 0x22c440804001, 0x20300045888101, 0x162204080008b11, 0x80022c440814001, 0x21600045888107, 0x162304020008b11, 0x80022c460808001]
def page146 : List Nat := [0x82040004588c101, 0x1623040a0008b11, 0x22c46082c001, 0x82160004588c106, 0x163304160008b11, 0x80022c664800001, 0x9202000458cc900, 0x163324080008b19, 0x80022c664830001, 0x1200000458d0105, 0x163424020008b1a, 0x22c684808001, 0x1a01000458d0d00, 0x163434160008b1a, 0x22c686830001, 0x82000004800c500, 0x201104020009008, 0x800240220808001, 0x820400048044101, 0x201104180009008, 0x240242804001, 0x820100048084100, 0x202104040009010, 0x24042080c001]
def page147 : List Nat := [0x820c00048084102, 0x202304000009010, 0x800240620800001, 0xa0f000480c4106, 0x203314000009019, 0x80024204284c001, 0x82000004840c500, 0x211104020009088, 0x800242220808001, 0x820400048444101, 0x2111040a0009088, 0x242220834001, 0x2000004844410b, 0x211204020009089, 0x800242240808001, 0x20400048448101, 0x2112040a0009089, 0x800242240830001, 0x20f00048448106, 0x212304000009089, 0x242460804001, 0x8201000484c4100, 0x213104040009098, 0x24262080c001]
def page148 : List Nat := [0x8205000484c4102, 0x2132041a0009098, 0x242660800001, 0x820800049804102, 0x260104180009300, 0x24c020854001, 0x82010004980410b, 0x260304080009301, 0x24c060814001, 0x82140004980c106, 0x2603042a0009301, 0x24c060858001, 0x8a040004980c10e, 0x260314180009301, 0x24c080804001, 0xa0000049810106, 0x260414040009302, 0x24c082834001, 0x820100049844100, 0x261104040009308, 0x24c22080c001, 0x820500049844102, 0x261104180009308, 0x24c220834001]
def page149 : List Nat := [0x82000004984410b, 0x262104020009310, 0x80024c420808001, 0x820400049884101, 0x2621040a0009310, 0x80024c420830001, 0x820100049884107, 0x262304040009311, 0x24c46080c001, 0x82050004988c102, 0x262304180009311, 0x24c462800001, 0x8a030004988c501, 0x2623142c0009311, 0x24c486850001, 0x8201000498c4100, 0x263104040009318, 0x24c62080c001, 0x8205000498c4102, 0x263104180009318, 0x80024c620834001, 0x8a00000498c4107, 0x263314020009319, 0x24c662808001]
def page150 : List Nat := [0x8a0c000498cc502, 0x2633142a0009319, 0x24c680804001, 0xa00000498d0101, 0x26341404000931a, 0x80024c686800001, 0x1a17000498d0d00, 0x30110408000931a, 0x260220858001, 0xa010004c048102, 0x301214240009809, 0x26026282c001, 0x82160004c04c901, 0x302204000009810, 0x800260440810001, 0xa120004c088500, 0x303314080009811, 0x800260662814001, 0x8a160004c0cc505, 0x303324000009819, 0x260664804001, 0x920c0004c0cc902, 0x310314160009819, 0x262220800001]
def page151 : List Nat := [0x82050004c444102, 0x311104160009888, 0x262220830001, 0xa040004c44410b, 0x311304000009889, 0x800262260814001, 0x92020004c44c105, 0x312204000009889, 0x262442804001, 0x8a0b0004c488502, 0x313104080009891, 0x26262082c001, 0x82040004c4c410b, 0x313304160009899, 0x800262664800001, 0x92020004c4cc900, 0x313324080009899, 0x262664830001, 0x1a000004c80c90a, 0x320434020009902, 0x800264086814001, 0x2000004c810d0b, 0x321204020009909, 0x26424080c001]
def page152 : List Nat := [0x20c0004c848102, 0x3212042a0009909, 0x80026424085c001, 0x82030004c84c100, 0x321304080009909, 0x264262800001, 0x82020004c84c502, 0x323314000009911, 0x264662804001, 0x82020004c8cc502, 0x360104060009b00, 0x80026c020810001, 0x820b0004d804102, 0x360104180009b00, 0x26c020854001, 0x2140004d80410b, 0x360404160009b01, 0x80026c08282c001, 0x2040004d848100, 0x361204180009b09, 0x80026c242800001, 0xa030004d848500, 0x361214080009b09, 0x80026c242814001]
def page153 : List Nat := [0x820b0004d848506, 0x362104180009b10, 0x80026c420858001, 0x2030004d888100, 0x362204080009b11, 0x80026c442810001, 0x82160004d8c4105, 0x363404160009b18, 0x26c68282c001, 0x82030004d8d490a, 0x42110406000a100, 0x80028426080c001, 0x82030005084c501, 0x42230406000a110, 0x80028446280c001, 0x8a0b000508c4101, 0x4632141e000a311, 0x8002a408684c001, 0x820400054810d0b, 0x5211041a000a908, 0x2a422083c001, 0x8a0400054848102, 0x5221041e000a909, 0x2a4620834001]
def page154 : List Nat := [0x1a17000548cc102, 0x56030416000a91a, 0x8002ac264850001, 0x20d0005588c505, 0x5632141e000ab19, 0x2ac66282c001, 0x8a0400058008504, 0x6003140a000b001, 0x2c006282c001, 0x8a160005800c506, 0x60032410000b001, 0x2c0064858001, 0xa0200058010500, 0x60041416000b002, 0x2c0082834001, 0x1a0100058010d00, 0x60043416000b002, 0x8002c0086830001, 0xa0200058048500, 0x60121406000b009, 0x8002c0242810001, 0x1a0b00058048502, 0x60331416000b012, 0x2c206082c001]
def page155 : List Nat := [0x92080005840c107, 0x61043400000b081, 0x2c2086804001, 0x1a0500058410d01, 0x61043416000b082, 0x2c2240808001, 0x20c00058448102, 0x61132408000b089, 0x8002c2640834001, 0x1a00000584d0106, 0x62043402000b102, 0x8002c4086808001, 0x20d00058810d0b, 0x63010416000b11a, 0x8002c622082c001, 0x820b00058c84105, 0x65010416000b198, 0x8002ca06082c001, 0x20d0008400c505, 0x101324040010809, 0x80042062082c002, 0x820b000840cc505, 0x161404160010b09, 0x44024085c002]
def page156 : List Nat := [0x82000008808c500, 0x203434000011018, 0x800442220804002, 0x82010008844c100, 0x212304020011090, 0x442660800002, 0x820100089844100, 0x261104040011308, 0x44c22080c002, 0x820500089844102, 0x261104100011308, 0x80044c220830002, 0x820f00089844106, 0x2611042a0011308, 0x44c220858002, 0x92020008984c10a, 0x302314160011809, 0x46222082c002, 0x820b0008c44c901, 0x313104160011891, 0x46266282c002, 0x82050008d844102, 0x361104160011b08, 0x46c220830002]
def page157 : List Nat := [0x82150008d844109, 0x3611042c0011b08, 0x80046c240800002, 0x2030008d848100, 0x361204080011b09, 0x46c240830002, 0xa000008d84810a, 0x361214020011b09, 0x46c24280c002, 0xa050008d848502, 0x3612141a0011b09, 0x80046c24284c002, 0x820b00091844101, 0x461214260012308, 0x4ac220810002, 0x820b00095844104, 0x5611042a0012b08, 0x4ac26082c002, 0xa130009588810a, 0x600434160012b11, 0x4c0242804002, 0xa0300098048501, 0x601214080013009, 0x8004c0242814002]
def page158 : List Nat := [0x1a0b0009840c105, 0x611204040013082, 0x8004c2240830002, 0xa0b000c180c505, 0x62314160018302, 0x60c66282c003, 0x920c000c18cc902, 0x63524280018319, 0x80062022082c003, 0x9202000c404c505, 0x102104160018809, 0x620440800003, 0x8200000c4088500, 0x102314160018811, 0x800620664808003, 0x8216000c580c105, 0x160404160018b01, 0x80062c24083c003, 0x820b000c588c105, 0x163324180018b19, 0x80062c68082c003, 0x820d000c58d0d05, 0x260304280019008, 0x66026282c003]
def page159 : List Nat := [0xa01000cc088100, 0x302304160019811, 0x800660662800003, 0x8a04000cc0cc500, 0x3033140a0019819, 0x66066282c003, 0x9201000cc0cc900, 0x310104160019819, 0x80066226082c003, 0x200000cc484105, 0x312214020019891, 0x66246282c003, 0x820b000cc4c4100, 0x313324000019899, 0x662664804003, 0x1a02000cc4cc901, 0x323104000019902, 0x664680808003, 0x1a01000cc8d0d00, 0x3234342e001991a, 0x66c02082c003, 0x214000cd80410b, 0x360214260019b01, 0x80066c08082c003]
def page160 : List Nat := [0xa0d000cd810505, 0x361104160019b02, 0x66c220858003, 0x201000cd848100, 0x361204080019b09, 0x66c240830003, 0xa01000cd848500, 0x361214080019b09, 0x80066c242814003, 0x820b000cd848506, 0x3622141a0019b10, 0x66c62082c003, 0x20b000cd8c8104, 0x363414160019b1a, 0x80066c684800003, 0x1217000cd8d0900, 0x401214020019b1a, 0x800680440800003, 0x9202000d0088500, 0x41220400001a019, 0x682442804003, 0x8200000d04c4100, 0x41332404001a099, 0x684620800003]
def page161 : List Nat := [0xa01000d08cc100, 0x4601040a001a191, 0x68c02082c003, 0xa13000d180810a, 0x46030402001a301, 0x80068c060814003, 0x820c000d180c105, 0x46030428001a301, 0x68c240804003, 0xa00000d1848106, 0x46121402001a309, 0x80068c242808003, 0x8a00000d1848502, 0x4623140a001a311, 0x68c46282c003, 0x8a13000d188c506, 0x46232428001a311, 0x80068c64283c003, 0x9214000d18cc505, 0x5211041a001a319, 0x8006a442083c003, 0x8a0b000d580c105, 0x5632141e001ab11, 0x8006ac66282c003]
def page162 : List Nat := [0xa00000d800c505, 0x60121402001b009, 0x8006c0242808003, 0xa04000d8048501, 0x6012140a001b009, 0x8006c0242830003, 0x8a0b000d8048507, 0x6013142c001b009, 0x8006c0264804003, 0xa0b000d804c901, 0x60331416001b00a, 0x6c206082c003, 0x201000d8448100, 0x61120404001b089, 0x6c224080c003, 0x205000d8448102, 0x61120418001b089, 0x8006c2240834003, 0x8200000d8448107, 0x61130404001b089, 0x6c226080c003, 0x8205000d844c102, 0x61130416001b089, 0x6c2260858003]
def page163 : List Nat := [0x9201000d844c900, 0x61132404001b089, 0x6c226480c003, 0x9205000d844c902, 0x6113242c001b089, 0x8006c246082c003, 0x820f000d84cc105, 0x62130400001b108, 0x6c4260804003, 0x8203000d884c101, 0x62130408001b109, 0x6c4260814003, 0x8214000d884c106, 0x6213042c001b109, 0x6c4260870003, 0x8a01000d884c500, 0x62131404001b109, 0x6c426280c003, 0x8a05000d884c502, 0x62131418001b109, 0x8006c426284c003, 0x9204000d8c44105, 0x65110416001b18a, 0x800a2c240834003]
def page164 : List Nat := [0xa0400149844106, 0x631214080029b09, 0xc2c640810005, 0x204001898cc50b, 0x601214080039b09, 0xec2240810007, 0x8216001d884410b, 0x60321408003b188, 0x16c066285800b, 0xb050dc58048582, 0x601216181b8b009, 0x86e2c2240c10371, 0x30c0dc58448182, 0x3612060a1b8b089, 0x88e26c240c30471, 0xb0c11c58048582, 0x6112060a238b009, 0x88e2c2240c30471, 0x8b0b15c4588c185, 0x361206082b8b001, 0xe226c240c14711, 0x83041c44d848186, 0x601216083b0a908, 0x2200c0242c15100]
def page165 : List Nat := [0x30444018048586, 0x6012160a8803089, 0xa420c2240c11200, 0x30c48418448182, 0x201106009083089, 0xa42240220c11211, 0x830c48448044182, 0x561106089089008, 0xa6206c220c11272, 0x3014c40d844185, 0x361206089901b09, 0x26406c240c15320, 0x83014c80d848186, 0x4613060a9902309, 0x26408c260c31320, 0xb054dc18048582, 0x601216189b83009, 0xa6e0c2240c11370, 0x30c4dc18448182, 0x263316089b83089, 0x2ae6c2264c11571, 0x830b5c00c4d4982, 0x601216091b12b08, 0x46e2c0242c16371]
def page166 : List Nat := [0x3048dc58048586, 0x6112060b1b8b089, 0x46e2c2240c32371, 0x30495c418cc982, 0x162306092b88b11, 0x4ae22c460c2e571, 0x830495c89844182, 0x601216092b9b109, 0x66e0c0242c17370, 0x304cdc18048586, 0x6112060b9b83089, 0xe6e0c2240c33370, 0xb0cd1c18048582, 0x6112060ba383009, 0xe8e0c2240c33470, 0xb0cd1c8d848582, 0x3612160ba391b09, 0x68e66c242c33473, 0x305dc44d848182, 0x36120619b889b09, 0x6ec220462c2f711, 0x9003800e004000, 0x401880a40420170, 0x4e024010c07203]
def page167 : List Nat := [0xc805e02d81600a4, 0x40e606c034819c0, 0x23411208403d81e, 0x9829013a09804a0, 0x6283041780b805, 0xe7071837c1a00c6, 0x40ff07c03c81d80, 0x22e113089041c20, 0xc42561260928484, 0x853028613d09b04, 0xaf85702b01550a9, 0xd0ba05b82d01650, 0x1930c586102fe17, 0x561a40d10668330, 0x83861bf0dc86c83, 0x75c3ac1d10e6872, 0xa07b83d01e10ef0, 0x10208043fa1fa0f, 0x1f10d885c41a209, 0xe23311708ac44a2, 0x48e24512008f846, 0x9c4c825c129093c, 0x9d04e226c13489, 0x458a1c50227c13d]
def page168 : List Nat := [0x214d0a6052628f1, 0x2b21568aa854c2a, 0x9c2c71610b00572, 0x85ba2d81698b405, 0xbd85e82f01740b8, 0x78c2860630017c8, 0x1990ca463e31818, 0x461a18d0467a338, 0xc3571aa8d486983, 0x6e436c1b40d8c6b, 0x1070037f1bd8ddc, 0xe647263901c48e, 0xd70eb07503a21ce, 0xd1dc0ed47683b01, 0x3cd1e40f147803b, 0xc83e11ee8f6c7b0, 0x87ea3f01f58fa47, 0x388124071fe0fe, 0x5109c84a4182091, 0x22010ec86c43021, 0x592289134892442, 0xe46f235918c8c44, 0x91048524111f48e, 0x749324972489238]
def page169 : List Nat := [0x92d89624a925012, 0x6a93409984c725f, 0x327593949be4d82, 0x50928214089e84f, 0x3e51d28c1448a18, 0xca685302949490a, 0x52ca8854229e14d, 0x29570ab45562a81, 0x2bc15d0adc56a2b, 0x8e2c3160cb0657c, 0x45a02ce9660b245, 0xb7a5b72da16c0b5, 0x60b9c5cc2e59710, 0x9790bc45df2ed97, 0x17e8be85f12f4, 0x13089840c126073, 0x6233109870c3061, 0x8263d31c18c4c4c, 0xc98648322990cc, 0x9a8cc665a32b994, 0x41a0ccfe6793381, 0x34a1a44d1c68c34, 0xad3549a88d3a698, 0xc6bb35c1accd606]
def page170 : List Nat := [0xda66d03669b1cd7, 0x94dc66df36e9b5c, 0x9bf4df06f43759b, 0x8e9c54e2270b381, 0xd39b9cbce4a7213, 0x74c3a49d08e7e73, 0xc475b3aa9d50ea0, 0x8ede76c3b49d90e, 0xe1cf047803bd1dc, 0xd1e50f1e78c3c51, 0x3d41e8cf3e79d3c, 0xc73e01ee4f5e7ad, 0x67d83eb1f50f9c7, 0xfee7ee3f49f90fb, 0x3900a8003fe1fe8, 0x209d04681f40b20, 0x1e20d5068831417, 0x1426a12908c8414, 0x864431a1810b485, 0xfe87c43a21c90da, 0x512a88d44522190, 0x2a914c89e44da26, 0x122f116e8b24572, 0x46c234d19c8c846]
def page171 : List Nat := [0xed474a39d1c68de, 0x48ff47d23d91e48, 0x230914487242120, 0xd9266930495a489, 0x253529294149ca4, 0xada5652ac9534a9, 0x64b825a52c89624, 0x9874c125f12f297, 0x529a14cda64d31c, 0xd37c9ba4db26c53, 0x7613a89d04e7271, 0xe27d93de9e64f02, 0x5042819404a004f, 0x1d50d2855426a0d, 0x6a2e516a891442a, 0x492a4651f28e146, 0x8d4b8a57527a931, 0x29d54e6a6c534a9, 0x4daa5151ca8753e, 0x655a2ac1552aa05, 0xaca5632af9574ab, 0xc4ade569ab41594, 0xd5dcaeb573ab915, 0xc61620b0b5832be]
def page172 : List Nat := [0x5aca1642b1f58e2, 0x59d2ce166ab3059, 0x495a3ad11684b3c, 0x4b595ab2d41696b, 0x6deb695b1ad7d6b, 0x25706b815bd2dcd, 0xae81734b975c9ae, 0xd92ea974cba45d1, 0xc5e2aefd772bb55, 0xbe75efaf697a6bc, 0xf8bf85faafc97d8, 0x9826c10605b0117, 0x9183ec1c60d305, 0xbb0cd862c2d613b, 0x6293135894c4261, 0x72635b1a18cac5d, 0x4c8963fb1f18eec, 0x956ca464e325592, 0x1197ccb865a32b5, 0x333d99acca663b3, 0x75b39d9c4cdd66a, 0x968334199fecf56, 0xd1f68bb44da16d0, 0x74d3169734ada46]
def page173 : List Nat := [0x9a9ed4969fb4f1a, 0x5adacad5e6aab54, 0x1b601aeed736b73, 0x6d1b66db2ad8b6c, 0xc16df36d9b62daa, 0x6dd46e83729b92d, 0xbeadf06f5b78dbb, 0x3dc12e04700b7f1, 0x3889c3ae1b709b8, 0x1d38c9c5ae2a713, 0x6729b92dc8ee417, 0xe67731397dcb8e5, 0x14e8373d39c9cda, 0xdd3ae96748ba35d, 0xae5d6ceb07543a8, 0xfbb61da2ec875fb, 0x77a3bb9dccee476, 0xf783bbf9df0ef6, 0xf27790bc71e2cf, 0xe7ef3c79cbcc5e6, 0x61ea6f4e7a4bd0d, 0x3dc5ed2f647af3d, 0xc43e09ef8f777ba, 0x57ce3e65f24f8a7]
def page174 : List Nat := [0xfbc7dbbed5f5efa, 0xb0fd37e7bf11f80, 0xdfdcfea7f33f79f, 0x22008fff7fbbfc, 0x240820350148074, 0x819c0b605302781, 0x50825c11208103b, 0xd074834417a0ad0, 0x11d08c84141ee0e, 0x9613d09d84dc24a, 0xc2f216f0b0855c2, 0x68c3421910c285f, 0x387643921b90d88, 0x10a88344061ef0f, 0x4512088cc45e21f, 0xe26512d895c49e2, 0x51228313e89e44d, 0xcc5562a114a8a44, 0x8b2c58a2bf15a8a, 0x888bf45e22e116a, 0x71998cbc65231d1, 0x3571a68d1467a33, 0xa37f1bd8dcc6c2, 0xc7563a51c98e3c7]
def page175 : List Nat := [0xf7c7aa3c31dc8eb, 0xd90348063f71f38, 0x22090d485a42320, 0x6322d914c89a445, 0xe47d23a91b48ce4, 0x9564a724c92348f, 0x7499e4cb26192d4, 0x93fc9f64f127293, 0x9b9484a36513283, 0xb2b19564a8e53d2, 0x59b2c79604aea56, 0x925bf2db96acb4e, 0xcbd65e32ed975cb, 0x85cc1e60730097e, 0x498dcc666293109, 0x335996ccaa64f32, 0x993499a1cd02677, 0xe6b73559a9cd3a6, 0xdea6e936f9b34d7, 0xace5271b3899bfc, 0x9d74e9673f39b9c, 0xca9e4cefe7713b2, 0xf3dc9eb4f4a7993, 0x7f13f59f8cfa67b]
def page176 : List Nat := [0x5e82340ea064ff2, 0x50ca857426a10d0, 0x2350fe877437a1a, 0xea3251828ad44da, 0x480a3e51d28e346, 0x4349ea4dd256917, 0xa9734b0a57d2aa9, 0x34a99b4c7a61d2f, 0x353929c14daa6bd, 0x522f9df2742b01, 0x10401f59702c0fa, 0x2615504838cd082, 0x49848e86901c93d, 0x4508e66c128174c, 0xcea99a332748cc0, 0x2601c01a1d66a17, 0x7d042f94778140, 0x182a0ac0f01d013, 0x92005c1004201a0, 0x70083d005a49c92, 0x49c028040040000, 0x758c358fc8dd11e, 0x750be22204c0e0d, 0xc61c130ec042f91]
def page177 : List Nat := [0xd45961ee2a44c79, 0xca68895f40940a3, 0x222d44c1487da11, 0x14d77d1a4503e32, 0x803d83a01cee40a, 0x3eef1de314116e4, 0xf8dd0589dc6b01c, 0x28c3ea8201cd618, 0xf4fa9ec540a5148, 0x6788f0881ada4a7, 0x21a8c017e13e0f9, 0xf20783195b0f167, 0x860a0a1f4034a78, 0x6008531a614c060, 0x8e102c2b40307d6, 0xdc7401202cdbd9a, 0xf20e4750f60820, 0xd1de3b01d8e3, 0x5d90a8b554a048a, 0xf026cd476175424, 0xb582102045d9b05, 0xb23245c8a0f205c, 0xe13e05db108d01, 0x4850167c6a8c098]
def page178 : List Nat := [0x804305e0f60822e, 0x91d17c3b01d8b52, 0x10a1b5602c24446, 0x303561102c1125, 0x60440284015d822, 0x120099050bea354, 0x7006e25cea0855a, 0xc020c1521180700, 0x61c4371c511eec4, 0x13a64c1002176, 0x14f12811a4bc239, 0x44028829040389c, 0x2f05e83e8a60140, 0x9ca70445ecbd579, 0x19e069bd14d58a0, 0x7828520a3d47005, 0x5c7d04400a0511, 0xe1249452824e20e, 0xfe04502e0364217, 0xe1bc370711e4714, 0x7006009a09414b, 0xc0a0b723c3b8078, 0x9c110928fa112c2, 0xbc2274374a68132]
def page179 : List Nat := [0x75c24002ba06807, 0xd4bdc36af60280, 0xb33502c4997a014, 0x8fc1201011e0c40, 0xc8b42d40a00f5b2, 0xa78690ea518a745, 0x2434d69aa35218c, 0x3a47223d6280e12, 0x2271a2298050212, 0x1a1ac080e68a069, 0x2c68cd145900f0, 0x900ebac75639007, 0x56e3586c8d71ba3, 0x63b5312c898e20d, 0xaec7603b042f501, 0x6386304214475aa, 0xbb27283e7122444, 0x80b0be97a03634c, 0xa06552741081918, 0x84681771e039d20, 0x22ea40780700600, 0x11d02e3c8920950, 0xe4ba1723d009e16, 0x6a241c5b0691f25]
def page180 : List Nat := [0x98c304ec59a937b, 0x59caf095012094c, 0x365445c62413820, 0x4c2971e127a2402, 0xe530a7a0c762a6d, 0x1416af31e592a26, 0xd7901403abd9e90, 0x144003482102009, 0x8235063458ab781, 0x140180200227cd7, 0x262138a02260100, 0xa8dd41464c4f817, 0x1f40b9407043646, 0x54524e9ec84e28e, 0x128141b2360690d, 0x604080016024c34, 0xf900054e28d932, 0xa218c12a6548120, 0x3e3f018b5502f11, 0x2c0130a11f2541, 0xc84592708e40062, 0x14dd8031688c6f, 0xc93f27a4f09d87b, 0x5997b3cf4fa9f03]
def page181 : List Nat := [0x35e20517a1675e4, 0x800e87e03c652f, 0xa4901218f5a0f48, 0xcd02c3ba2d45716, 0x54828f5182247e3, 0x4c084a7a1226063, 0x82811e2350507b0, 0x7caa8244768e0aa, 0x7302e0619174c49, 0x800c4c00989d, 0xde40b42884d0909, 0x227a13003010884, 0x6a97704e39c7203, 0xcdb811b716eca54, 0x893d004dc598602, 0x9a033204253ca50, 0x1af783e8e615a03, 0xcb29632c1f08251, 0xb84782738a23471, 0x4421c11406f48c1, 0x38e311a1349f47b, 0x99ca802715c07c1, 0x2e039e794f4d4, 0x352670aa09d20a4]
def page182 : List Nat := [0x20d006ad30da151, 0x7202e040072c324, 0x161eb3d42a43b8, 0x4eb04983340ea02, 0x84602e04c0700d7, 0x6807bf47e62744d, 0x466ce80270280, 0x80e11ca01c0780a, 0x1ec0745f86d0cc1, 0xf1c803c03803004, 0x7914113e5016294, 0x41f4069d749c934, 0x2013603c0380300, 0xc0107d23cd60ed9, 0x844801900f00e00, 0x28e518400068020, 0x702b96c2d642c10, 0x77e42d89acd0480, 0x20e3876de80a827, 0x2340e4358684c47, 0xe0f29e92c09101a, 0x982201f0dc7a03, 0x82ac81006004414, 0x27558aad5502003]
def page183 : List Nat := [0x81e9c8037154698, 0xa03806a0c3007d, 0x1f01901b02407a7, 0xc80508d1b634c6a, 0x1c035628271c80, 0x2a8a50c0480b966, 0x28e49ca1b25e4e, 0xb8710de1a814020, 0x46817296384d618, 0xc0b24e49b934bd0, 0xfc1d8098109ac37, 0xcdf01702c64dbd0, 0x7c03e1fc768ea3a, 0xa29014a0c154408, 0xdc3039231adf04d, 0x520840f08d0850, 0xc3de24005e3006d, 0x9c40810228455c, 0xde1b8e2c5402c, 0x10030028652f81, 0x4804d84225c4bc, 0x1328c468a745421, 0xd6d9a1260b04720, 0x8a3cc0b97837c09]
def page184 : List Nat := [0x27210201c59257, 0x601f32c07acb87a, 0xf6475cab941422, 0xb8ba18509a12920, 0x11c3c1030f204c0, 0x5780660cba070fa, 0xd00950120144180, 0xa48c0800e012e89, 0x6c06a0197b8170d, 0xc02803004436208, 0x16138a00401ea23, 0x81720605c601271, 0xb4608141860895d, 0x11a1e435ac55dcb, 0x733004e8ed1d08f, 0x9e309798f8cbc3, 0x47306080b3ad0fe, 0x6ccab6e008c108f, 0xc1f22e45a00b16c, 0x386eea08f01001, 0x83c83002804c038, 0xe00c0107b01cea, 0x8160343904580f0, 0xfa3e8913ae49446]
def page185 : List Nat := [0x32c15c109718ff1, 0x51390761e476016, 0x2d4a794d788f0c9, 0xc0fa2256bad61f4, 0x5601d01eaedea0a, 0x20400a1fc6bc234, 0x236ecdd00b3750f, 0x47c8176be3e9b88, 0x1a05c0522950ca1, 0x38870c031dd2bb1, 0x98290240282a4a3, 0x11e236281ab89e6, 0x23c4748e054817, 0x644ae90609803de, 0x39052040b97e13e, 0x800d4180f40748, 0x28c0b38c90ec1cc, 0x8f91c1f48202746, 0x810c27848026144, 0x2ccd56582c01cf3, 0xa841f805cfe32b0, 0x66208af6bca2142, 0x64a0a46e0d81a43, 0x9171ba36939973]
def page186 : List Nat := [0x4543c0a30204501, 0x27022240a05f72c, 0x271450a00140180, 0xea2c4f93124a41c, 0xa092034c993702, 0xca681001a1f523a, 0x1a7e49003401aeb, 0xa754e80480684e1, 0x80ca0d61a68286c, 0x13e05c3c8920468, 0x4b8770c0280448a, 0x92c4b0a0028095c, 0xb028d6c46b0e8c8, 0xbb8277620f83cc3, 0x40940a1791ac9ac, 0x8d02d06a0b09505, 0xa4481711a1e44f8, 0xac9545a80e91922, 0x87d12c051132484, 0x552a08d13e97c81, 0x282a62a09f23a9, 0x9c5189c4bc0d815, 0x2bc148dc0420ae2, 0x702688466023450]
def page187 : List Nat := [0x4ec3986a2349881, 0xeedddc0c2174050, 0xfa280534a79732e, 0xd0082458af59ea8, 0x1121e4303111a80, 0xae30389287191d9, 0x4c270e60fa04806, 0x1802441019d3381, 0xe37e028b61712e1, 0x360693056083586, 0x683cc786a8d303c, 0xf2bd02eeb10bc97, 0xc131c20c7012568, 0xf12460240980820, 0xc0180232605cf99, 0x243f1398c301e01, 0x1a4e29b44889b0, 0x80042c020cd816, 0x8e464178090100, 0xe0794889040b937, 0x6343e9a102e23c7, 0xb590029a487d1cc, 0x107b44c0887906, 0x3948e80171603c]
def page188 : List Nat := [0xc6028e15c203302, 0xc0709f038e04730, 0x8a0b139a584ec05, 0x81a4de4bd368470, 0x1c01ba471e28072, 0x280282f8b501a0, 0x1671664b45880f, 0xaec1621a19808d1, 0x502009d51aa26ce, 0x4494d02914011c5, 0xa14002803004c2c, 0x1d13e05e2f12528, 0x822b4e684288459, 0x1a05cfb1fc02e05, 0x456112059dd43b1, 0x3c46ad502ef280a, 0x31004c0b93702e2, 0x602c04264c6180a, 0x14a2704341427c7, 0x31821d83981001b, 0x74b7558af3e2244, 0x6db9fdb6b7f40e0, 0xe45c6b84228911c, 0xc330021824c007a]
def page189 : List Nat := [0x720a6234450d219, 0x81c1b63646b8d86, 0x54060054f40b060, 0x2e510413b026002, 0xe93702e05005178, 0x210473913106283, 0xb53214c0a46a110, 0x140060be4154e29, 0x86fc6c05b37c021, 0x776b2060e0b1a1b, 0x5a488810805c1b1, 0xa434e1613a0d601, 0x7c8a8022208d41, 0xf1132252ec47c07, 0x7a06300f9782e45, 0x80841040800b816, 0x407a46c2e215cb, 0x87064402437f00c, 0x9b1342664c89000, 0x40c80800a25c068, 0x14206500448165a, 0x1381317b251c3e8, 0xe29b4238134dc9b, 0xf225027dd709b4]
def page190 : List Nat := [0x94f80100623c80d, 0x31667cce99c0100, 0x23f11a05cfe0fc, 0xc8cfa0dd3ec90d2, 0xa2983e86c8d73ea, 0x400f215203562a0, 0xf11d2925049c930, 0x5702c05cae95c01, 0x4229401f823e2ec, 0x8a7e9b32a154030, 0x19b04a040c98165, 0x404a8258e91ce39, 0x1d804e08c1013e0, 0x809f418108093e3, 0x234fb2634c097c7, 0xb4705601400d3f8, 0xe3927022741f23, 0x2b295d3ce41d074, 0x600ac0384182579, 0x88281600c6d0d90, 0x3c0902287d1f889, 0x1702eeb87902d0, 0x85cc1171e87d010, 0x4e4565421e0460]
def page191 : List Nat := [0xd14f0629a933950, 0x234190e42400700, 0x58b623454817876, 0x2a0178d6014b400, 0xa45c152cb79c08a, 0x620bae590b02122, 0xe1601700a8bd322, 0xfa3d820b7529453, 0x9f206403c0ebfe7, 0x544989b00c53cf9, 0x13a2707187912e2, 0x8ae504a09d9707d, 0x45482a5c12011e4, 0xd9552a512916046, 0x2aa5423a1e47188, 0xe1e457939044961, 0xa09c578611e23b, 0xc3e80f418ec44fa, 0x446a0ab06700440, 0x3a51f8028cda234, 0x3c130210f61f5d3, 0x6008222121f81, 0x389d1f43d420005, 0x5601212e602fd48]
def page192 : List Nat := [0xe26e0240ba574a8, 0x7a0fa29805217c2, 0xa1117b2f55e6bc9, 0x9c0a626cc480d04, 0x41a0b5136680cf9, 0xe49746089e13225, 0xa7326a4c8098087, 0xb535a6a74606c4d, 0x75218c3603102e1, 0xb2cb0f6aec1900d, 0x228290142005182, 0xf02e234fe28e51a, 0xe28a11280f89888, 0x253d6c81369271c, 0x8d0f6e2c8805271, 0x4548f002e3c80a1, 0x1e8362744d3fa0f, 0x43e87a008560e60, 0xc00816f32627498, 0x2320bc040008db0, 0x29782ee5d890034, 0x408f83401101a0, 0x9670cdc3e0c614a, 0x209417e041c4eb3]
def page193 : List Nat := [0x203c01802002052, 0x17026970488e326, 0x4350141406f9f10, 0x4005ce01bd37816, 0x89d1da074950fa2, 0x5c4f92504afc083, 0x4ed30ccb4a3306, 0x380602eb9806806, 0xb14ff9fe282524a, 0x54dc9cc6e8db052, 0x52bb1cc06ca601, 0x2d0590b1160390, 0x4111e0c40b81602, 0xcf5125152040074, 0xc80c85a94d0fa7a, 0xb981260a87a03e1, 0x75ee3db2d25b8a7, 0x4d25e53597704ef, 0xc8170343c84f95e, 0xecb50ce00aa549, 0x17cd0d61a0e3029, 0xae80f44844c3e82, 0xe0d1f901302effc, 0xfa0286c0690d917]
def page194 : List Nat := [0x40bace59a111628, 0xb279cf31201361e, 0x1da3b0444970143, 0xe40b990318139e7, 0x4748e0478ac11a1, 0x93189491de023c, 0xc82112e0060080, 0xc02e058081e813e, 0x682c111a080078a, 0xc715f7abb59663d, 0xca2f2dc8130226e, 0x8a8650d8084e49, 0x14019ccb9672645, 0x25613e05c4680d0, 0xd82092e1809952d, 0x2c7a17792e7ea3, 0x942884c04c0409f, 0x84a780e1230a96, 0x1602071cc114286, 0xc29070200340180, 0xe47c038e400c1f9, 0xe41827cbd08704, 0xd70ae013e474488, 0x160500835f876b8]
def page195 : List Nat := [0x7d24a06c0a82c3, 0x9a120130107b4f6, 0x2f6cb9969778510, 0xb99303e5d0bec9f, 0x23cca1921f81100, 0x729a1147c9f902e, 0x4e81413e0422c45, 0xc1f962b015febf8, 0x9403804c0b80e55, 0x9208e302ecf84b0, 0x140063336102090, 0x211c80c86f82e0, 0xd1b936d0761e413, 0x4b095c3081416ad, 0x542784802614259, 0xd61988d1c80400, 0x60044b013a1886f, 0xa01001a4901d01, 0x88ccb80cb0ec1cc, 0x911360487e27346, 0x4070020a49c5368, 0x3404c7629a53247, 0xc2204e08d141f00, 0x401380d0fb11224]
def page196 : List Nat := [0x1b0359ef14f0245, 0x90171ba36e0640b, 0x13c130210101f55, 0xf01075cf308d02e, 0x188891c63e8ed89, 0x80e80b002008002, 0x7704e160248e424, 0xc070274d25e5359, 0xfa7942d2bb144b2, 0x81702c2600a0131, 0xf65e4bb11e04220, 0xf21f5590af1bb2, 0x314e66c2bc1604f, 0x6a8d48630d20c0a, 0x38241484a80c35a, 0x6e0c31740506141, 0x81ede542b5beb75, 0x5e1840696a92006, 0x84e93001c084141, 0x142dc098087e830, 0xa1b434f4c9f0140, 0x58a300d006261a4, 0x16a41c288401ea0, 0x88fa04405dc094f]
def page197 : List Nat := [0x400346e02e8289, 0x1521740a02002c, 0x8e8f25d0b9c610c, 0x42480b1e81360c4, 0x80007700500500, 0x5b87d13eb14940, 0xf809ce08801e441, 0xb27036d807c9be0, 0x44f84e0285f484, 0x2c42444708d82ce, 0xb0940390620bc14, 0x8c0ab9a0431944, 0x6794f080bca73d4, 0x10001187747581, 0x838c92012010010, 0x84245050fbce02, 0x807c372c25780d0, 0xe2f3c458168710d, 0x371d0058073391, 0x548391d4144a3, 0x116798928168a24, 0x180e00a01001000, 0x9c4f83a8502447, 0x35c0f03a9af853]
def page198 : List Nat := [0xac81314027e059b, 0x83e81140d815024, 0xb1576b2c0bbd218, 0xc480ee0243b0083, 0xe803446a9b532a5, 0x8168ce0341002a1, 0xec7d01429c53e20, 0x69262cd098b0650, 0xbc4e7a00515db44, 0x541588905913de, 0x701f0fc9c817042, 0x5db2e01e0087a02, 0xab2c7603b05918d, 0x83017105a490769, 0x2a81786d0cc970, 0x4c880389c5044b4, 0x8e300403d0d06f0, 0xd0bb2f786d0d498, 0x1e2c259c86a2eab, 0xab982f203803803, 0x9e46823042a000, 0x7024038800167a8, 0x89d42427d2288, 0x4bc83805006008]
def page199 : List Nat := [0x5d01ca7de50174e, 0x8f286e38a945278, 0xaa848149e304c08, 0x1a0384000b85f1, 0xf4a600e058aa554, 0x76e7b5deacb3d81, 0x1ad1064040043c1, 0xebd4da99024305a, 0x812c1d407a1753a, 0x710002e04d2f85, 0x205c0824511621c, 0x2c88223c5608b06, 0x99607b02c248940, 0xc69852f922152cb, 0x1d12cc554418254, 0x29ad01881e74e07, 0x46c8d46f17d2f61, 0xb3391da3580f0d8, 0x58930302343940, 0x714604cf2339114, 0x51e23c077c3c8a, 0xee85cfb9e136034, 0x177602e80701c79, 0x5683d26f424813b]
def page200 : List Nat := [0x2ebb1b4900576b0, 0x17096040139370, 0x14093d401cb5451, 0x1223141282830ab, 0xb20c7624a1712e0, 0x5d9ef3df1d804cf, 0xc7d627c080252ee, 0xafbed67ccf19dbe, 0x6040129af02c7e5, 0x4d16b1ea3c9b51d, 0x87783c66a17c911, 0xe00c0109f76e03, 0x3416a41de080f0, 0xc88905101e04c90, 0x47125fc3f77ec0, 0x681704c0840bc44, 0x3c03803004d54a, 0xf29eafc09b3929c, 0x2ac002ba4182600, 0x3905480e19a08e, 0xfc3a87497d9d118, 0x100025108d7ea, 0x520d09203a02c01, 0x951280346aa120]
def page201 : List Nat := [0x4037a261362604b, 0x7a6b08370780440, 0xd8a501cce4791c6, 0x38098086621a84, 0xf0d43e45280f00c, 0x2a313166008e108, 0x2ed9d90ee0f605e, 0x8f02e04d5788e67, 0xc0800d8822bc138, 0xda0748389204eb0, 0x3811cc1384f8141, 0x148f80f01ab5005, 0x58e1f5a4b485a2d, 0xa8f40f21f83580d, 0xd0900e46e8041b, 0x702c048f801a208, 0x7603b0723a87403, 0x60080080d015104, 0x138a83c89780500, 0x4020020002b1a08, 0x760489902122e02, 0x8a002e0944fc060, 0xec900ec9692ce03, 0x4d08248fc2540]
def page202 : List Nat := [0xd83e27203c03803, 0x4007238b34264c4, 0x5714e25c390d116, 0xc08802100143229, 0x11dcda9ba04a6bd, 0x6f2dc2607c0108f, 0x4083605c6095729, 0xc837c170020021f, 0xfb16a1a4198e51, 0x7c6481a626b3051, 0x28070c7bd25a02, 0x92795609e048095, 0x6d84a81104a9e98, 0x30d6d259fb3d36e, 0x28d06140340380, 0x163410002ca6c, 0x140d2b8d7281705, 0x3e89b09c2584a8, 0xec831d8b044cc28, 0xca2942e2dc93813, 0x50a602202804251, 0x1364bca28050051, 0xb0d56921b626304, 0x80a00f1b2c806]
def page203 : List Nat := [0x2610c1cd185c01a, 0x5590200c0080982, 0x83486d9e815e2bc, 0x830160946a8d31a, 0x222121f86c8d88, 0x143e90a21342284, 0xfc424124ac0140, 0x2d0a21342083c22, 0x4a85986282411ae, 0x4b0f04e5080fa57, 0x9387909f0d41e43, 0x1f83e80a37449e, 0x4a8176dadb1e8bd, 0x82809009b134258, 0xe48c40c8903c277, 0xd372731ba36c148, 0xeefd88900e0fa04, 0xa5611a27c35bf87, 0x209c02902a0ad2b, 0x48070f79ee0260, 0xe94062ca9d53363, 0xcc070e554a3104, 0xa674ce55cb380d4, 0x60819116061bb02]
def page204 : List Nat := [0x1500905504eaec, 0x2002ee61cb9632d, 0x2881301e038c21, 0x362585281404a48, 0xb7638aac57ca661, 0xf4370106e409838, 0x32a1b0ab02132c1, 0xa3985bcb746101d, 0xe65b839622e0847, 0xb63a14806806020, 0x983ca596ae9e71f, 0xa8d40b820092848, 0x130be1d40b00966, 0xdf213d02c03c030, 0x80a254428700a33, 0x590d40507e9be3, 0x5c0780204e6fcde, 0x1cc1f42710700ed, 0xac0811c09446c06, 0x3e5e20db1bb2da5, 0x602e228c4012684, 0x1c0e92482940b00, 0x6236283fc89afe8, 0x50621e44f8171c]
def page205 : List Nat := [0xe069b336220c060, 0x12564098fd1f902, 0x2564a82445640c8, 0x816a92002e96d2c, 0x45a8a85a80d0584, 0x3803004020053a7, 0x340e0e30f203c0, 0x2fed45a80ba026, 0x1087d0f64c5a9b1, 0xe1f40722644a891, 0x277d0f9c9b81602, 0x41014d08a3f1628, 0xa00c0122902e40, 0x2a0283d42000a0, 0x10c6b2964e1544b, 0x18a040073766ea1, 0xea740427c8f8966, 0x3b01d92d02cfd44, 0xb09c2584a81452c, 0xa614f6089985009, 0x8af95e8900fa2a4, 0xb86d43e47b82502, 0x84b13d12803d1aa, 0xe80503506d5eebd]
def page206 : List Nat := [0x1cb7d6534c10255, 0xfc083ee7da738e6, 0x2ae558a91512489, 0x70901f42253f27b, 0x4800409f04005c0, 0x40641f559462068, 0xce0d92f2e616a8e, 0x68a85a8101cce6d, 0x5813a0911781445, 0x962ac41000387e1, 0xb4fe549124048b1, 0x1af12a0a81f2947, 0x4c03803850ee4dd, 0x920883c8300280, 0x30161851040b905, 0x2bdf208f0d60340, 0xc058af1e4090204, 0x3eac0564de55fb5, 0xc5343e813298034, 0x3711a8b95922a1c, 0xd32a584ac950601, 0x140940ba4247e33, 0x3ea7d2fa09b80e0, 0x1c0b81201c27ceb]
def page207 : List Nat := [0x1f29c53726d4d81, 0xa8101223f00b079, 0x2184c33e02405db, 0xd0291785ab351c6, 0x760912803044f94, 0xadac480f00f2048, 0x8d6e6dbdb6ab756, 0x44e91d1802a4098, 0xd65a93542c1e40c, 0x1737345a00b9664, 0x86564530471586e, 0x40b94a025c02e0, 0x1413e5b4b5857, 0x57407a1d616534a, 0x6008008ef0277fe, 0xbb2721cc4901d01, 0x26d6aa6f2fa5ec, 0x1301e018073ca24, 0x8e8020903e4230, 0x43983ec2784c4a, 0x89d692d3da3b452, 0x384f8c303a04d75, 0x3146204e9000280, 0x1010762234ba827]
def page208 : List Nat := [0x5cb326b2d49a89, 0xf13a4c10909f2d0, 0xb1274288450820, 0xa050051e8158478, 0x520282d4a33cf11, 0x81db818b51647d8, 0x85300a3827003e, 0x89f7bc224a707d6, 0xbe574ad7c005c12, 0x8de66cd08253272, 0x909d26004238c70, 0x1e4330650200082, 0xe4fa2344f85e2ac, 0x780d03a0154427, 0xa1e42380d1fe3f8, 0x161e8f011ea3a11, 0x4800e865c014010, 0x2e05cb80fa0882a, 0x9000262d47909f0, 0x4c2488923c04046, 0x285940709f48e6, 0x4c2884c4804fbb5, 0x4548a1171e4e621, 0x17fa2a49701a4be]
def page209 : List Nat := [0xc82502e2820b40, 0xe04d970929712de, 0x2788804013b2c02, 0x4a681001b2f80a8, 0xfa3900822b4542d, 0x43a86f0d61988d0, 0xa2134252400200d, 0x1365000a3ef5a50, 0x581070205c0b2f4, 0x3806ca694b291c, 0x54088090087d0f2, 0x6a8d842e3742d20, 0x2b07301403cc70, 0x900484085486928, 0x1aa3126a4acda80, 0xd8cd19981366c4e, 0x89f054e0c2f3850, 0xc07c41b0b005d29, 0x13a2625d4b98384, 0xd88a37c05c0a0b5, 0x3903e9263806fcd, 0x6808d943c820028, 0xe289b01012c7e02, 0x89d0578a909c0b1]
def page210 : List Nat := [0x2a649010158de1b, 0x49811d028029418, 0xf40880b12c04ed2, 0xabb13a39165b811, 0x800781001a6bc2f, 0x24494238e225a3, 0x9fc01a0580c818, 0x7fc790f00d45c0c, 0xd13e1108000d400, 0xb88f1c60589411, 0x21b81382629e0c4, 0xa401e0200e9c57b, 0x406a3246059c530, 0x20d75b40f979e1f, 0x809004000911e80, 0x7c4691e0f60bc8c, 0x281e41881723a2, 0x638870e4342f100, 0xa3c044410760589, 0xf0520c08d0e500a, 0x30af0583746dc1, 0x68681302102f0fc, 0x6f2fa5ecbb27243, 0x83085d01a25412a]
def page211 : List Nat := [0xfab14e79b939a6d, 0x7904a050a680d0, 0x200d82c04e0407e, 0x4e027c102e53da7, 0x8a6e4da9b00b812, 0x5780b0060264bd3, 0x722ae607a0f21a0, 0x61ae9184ce40b91, 0x83c4e93042427c, 0x891441250a21142, 0xdcc0925b4b58958, 0x60085644122a23, 0x827272398078070, 0x4c2112e00200a25, 0x5e8f786008b1520, 0xcc9892ebe00a09f, 0x27c070803f823e4, 0xa22c38c8ec85062, 0x7e08b02ec985db2, 0xa07407879108208, 0xc07d2b144781711, 0xcc000e418ec4098, 0x5f10581acb13eae, 0xf03a0d0578272]
def page212 : List Nat := [0x600900e039008b2, 0x3806f83e02702e2, 0xb81001c6f08f91e, 0x3f08291b23004c0, 0xd01000d1300f004, 0x160e60581f48298, 0xc9347909f2808b5, 0x1665c3d162a5049, 0x78e6216081968, 0x4cd25a334516404, 0xe705289d1280d4, 0xa935b060f805c03, 0x2e04cb40cf4d05, 0x702c08a4c4a0027, 0x7d3a12801a0fc2, 0x17a4b41d68270fe, 0x2fc6723ac0b2c, 0xc4009201001c010, 0xe11ca530270e611, 0x80681c87d0f0180, 0x227e9a8b5002003, 0xb969404148bb536, 0xa84e81400ac05cc, 0x3c41b1358170da9]
def page213 : List Nat := [0x89e13be550a8809, 0xa3d4601401c4009, 0xb817028bc176522, 0xa601b136054be97, 0x843d0c3d4306f38, 0x6b8430805082602, 0xce28f20c49a0322, 0x4e7146cb640e21b, 0x2048c1fd4082c0, 0x7009817240038a7, 0x20e5198aa5e01a0, 0xa2937b069429014, 0x104972704242754, 0xe1e41ac0300d1ec, 0x9bf14168290480, 0xa7a00bac9088f38, 0xf004310138c317, 0x1bb02a02c05df90, 0x884743c8381d205, 0x1311f81e4488fa0, 0xb4068057427d80b, 0x268058040060210, 0xa0c237c05c90846, 0x362382c92d2564]
def page214 : List Nat := [0xb0b4024f28b57c6, 0x8e8861302104134, 0xa1f47319b31a058, 0x3748c0403706f38, 0x8478fc0d403807c, 0x65900e80f40680, 0x98e34067c1299e8, 0x7113a261acf4960, 0x46e9240f0d81a43, 0x529a52e0e074924, 0xa915003b2800580, 0x382d054be9782ee, 0xab0680ca0380101, 0xc854f09e01f8120, 0x79020088baa122e, 0x80d3706dedb4220, 0x8a3f40ba1740c16, 0x8524dc9b0238430, 0x5143a861c60080b, 0x67ccf1c6b8c2600, 0x9a2902e8299fb8f, 0x570ad92e4fe5380, 0x8028149c79602be, 0xb8167206e5c71b]
def page215 : List Nat := [0x4014020020010b0, 0x35a45b84783101, 0x80b0060267a457b, 0x36f509c92002e2a, 0x3b408e470900173, 0xe8a6014342635be, 0xa0014018025e83, 0xb01301ccb821945, 0x45c2787b10a2040, 0xc3ec60163115208, 0xf41030288984fa0, 0xdc0280229a058, 0x2f1524001c8ea1d, 0xe24b771e414c4d9, 0xc89a84408402e08, 0xc320c405c3026b0, 0xb80500200600498, 0x2c21f53809b0844, 0x92220e200820b7, 0x380b8294c898d3, 0x70a6ad1568331ce, 0xb02775e5340b90, 0x8a6802a9b310248, 0x7402c2487802c53]
def page216 : List Nat := [0x40c14005862cc6a, 0x1c1f151aa024e06, 0x8c614a04c0806a0, 0xc01032776ce19b, 0xf2138a000f00e0, 0xab7d5a45340b91d, 0x18c780fc028009b, 0xb260db9b69a734c, 0x39820038038c989, 0xa4bc0d80d08e0b1, 0xdb5a0b04c7a6f4d, 0x4028020068987e2, 0xd80ec271400803d, 0x670280340100f1, 0xd50e21b3503c02f, 0x4b09592a94d13e2, 0xb89f1c603806bbb, 0x34869b827023700, 0x10dac851b8d81ac, 0x6c0050f80198612, 0xe36c6c8d71ac0ac, 0xda0323758db1134, 0x81889b23aca1228, 0x9426c900173d03c]
def page217 : List Nat := [0x1f80be2299a88d7, 0x652c2561224399b, 0x494604bf08d2529, 0x200283c878079, 0x7006b196302845, 0x885ba6c083146ba, 0x3187f882987f440, 0x65987be63987f88, 0x882905be6c087be, 0xfe8498ffe83107f, 0x5fac421dfa6c087, 0x8dfa6d087fc6290, 0xa0fba6598ffa641, 0x995f86c905fa4d, 0x2d107f886995fec, 0xe60886fcac885fa, 0xf86c90fea63887f, 0x5fe6c905fac020d, 0x5fa6c207f88708, 0x9857e8c087f8871, 0xda1dfa6c20dfa2d, 0x81887fe84085fa4, 0xe62987fe2d997fe, 0xfe85085fa0da17b]
def page218 : List Nat := [0x7fa62907f240887, 0x857e8c185fa6d10, 0x105fe6da0ffc439, 0x1887fe6518dfe6d, 0x83106f8ac887fa6, 0xa43a05ee2c187f8, 0xf86c885fa2d187f, 0xefea4086fea518d, 0x7ea43887be6498, 0x85fa2d996faa5a, 0xc887fe0d996fea5, 0xc2905fac021ffc4, 0xea5985fa2c207fa, 0xfa65887fc42186f, 0xdfc6c905fc6c90f, 0x86faa4885fa0da0, 0x985fac018efea51, 0x3187fe80887ba62, 0x8c98ff886907fc4, 0xa64905fec090ff8, 0xf886985ea2c187d, 0x7be87997fec2997, 0x97fe62987fe8318, 0x10fea42887be869]
def page219 : List Nat := [0x2906fea498dfa6d, 0xa4185fa4da07f86, 0xa6498dfe6c186fa, 0xfa63a07fe64087b, 0x7fe8518dfc6c887, 0x87fe65087de6499, 0x887fcc2907fe651, 0x79957e8d18ff86c, 0x4d18dfa0da1fb88, 0x886997ba64985fa, 0xfe84987f88718fb, 0x5fa0d10dfa4c187, 0xdfec2905fa4c08, 0x905fa4c18dfa6da, 0x3a05fe6c207fe8c, 0x63107fe80907fc4, 0xac221efea598ffe, 0xfa0d997fe60905f, 0xffe6290ffe64887, 0x87f88690ffa6c90, 0x185fec2995da4c1, 0xda1ffe82887fe85, 0x83085fe6d085fa2, 0xa43187ec42887fe]
def page220 : List Nat := [0xfc42987f88710ff, 0x5da4c086faa598f, 0x87fe62885fe6d88, 0x20ffa65a07fe829, 0xc986faa5a0dfa4c, 0xc090ffec090d788, 0xa43987fa62887fa, 0xfa0d996faa4987f, 0x5fa4c885fa2da15, 0x87fa64885fc4c88, 0x20ff88c887ea628, 0x698efaa4207fa64, 0x65a0dfe6da07f88, 0xe80987fa6290ffa, 0xfa6d18ff88c907f, 0xefaa5085fa4d985, 0x97fe64987be6598, 0xa07f863106fe86a, 0xc185fec498dfa2d, 0xd98ffcc090dfa2, 0xe64987fa60885fa, 0xfe61887ea6218fb, 0x7fc6c887f88c90f, 0x8dfa0d18ff8c299]
def page221 : List Nat := [0x985fec2985fec09, 0xd187fa6c906fea4, 0x6c90ffa2d995fa4, 0xa4d087fe87885fa, 0xfa6da07fe84885f, 0x7fe8290dfa4d98d, 0x87da42905fa6da1, 0x887fa42207f8868, 0x6a97f241087fe85, 0x8c997fe86906f88, 0xaa5987fa40887f8, 0xfe86885fa4c206f, 0xffe8710dfe6da17, 0x87fe8298ffe6498, 0x18ff8c2905fa2d0, 0x2886fea4886fea4, 0xa5186fea5887ec6, 0x86c90dfe6c20efa, 0xfc63a05fa4d887f, 0x5fe6c087f661187, 0x7f8c090ffe6588, 0x987fec2907fe829, 0x6087fc42207fa42, 0x6c907fa42187f88]
def page222 : List Nat := [0xe8c90ffe8690ffe, 0xfaa498dfe6d10ff, 0x7fc6c907fe6c90e, 0x8ffc6c90dfec498, 0x87fa60907fec49, 0xd887f863187fe63, 0xa4187fa41885fa6, 0xa42887fe62906fe, 0xfa43087f887887f, 0x7fa6598ff862987, 0x87ba65987f88718, 0x907ba63987fe631, 0x5b8024dff86c, 0x800000000000003, 0x17a928000000091, 0x40ed082c00, 0x14368040000000, 0x12ef18000000000, 0x2620137a0000403, 0x0, 0x2760031200, 0x81800000ce80001, 0x1f6000001f82507, 0x8000311edd80000]
def page223 : List Nat := [0x42800af, 0x8000037e2e80000, 0x3405004e8, 0x8e6000009f80000, 0x39a0000000000b9, 0x8000c0000035600, 0xbfef480000004fe, 0x25e0300401000c6, 0x2ba6f8b2f581600, 0x53060103400, 0x499bbe0480003, 0xc0000000, 0x800000000220a00, 0x60200406, 0x0, 0x4b480000, 0x800000421980011, 0x4000002b, 0x1680000, 0x20000622600, 0x804001962880000, 0x2f2022de0000037, 0x40000002400, 0x1ee003bafd8000e]
def page224 : List Nat := [0xf082a9b80000, 0xbead38000000001, 0x8000001400008ed, 0xb8010b, 0xa7b37019da00, 0x800003460019200, 0xaa030000000811, 0x19a3280000, 0xf6a82022f611, 0x0, 0x400000001000, 0x28000000100000, 0x6000000, 0x280000001, 0xd000000058, 0x3c0000001c00, 0x14000000098000, 0x5c0000002a00000, 0xc8000000, 0x360000001a, 0xe8000000700, 0x420000001e000, 0x1200000008c0000, 0x27000000]
def page225 : List Nat := [0xa40000005, 0x2e000000158, 0xc40000006000, 0x35000000190000, 0x80000006c00000, 0x40818000204, 0x1020a00008104, 0x408600002042c0, 0x22c00008115000, 0x898000404500001, 0x800018101000084, 0x604140003020, 0x1810c0000c0858, 0x604540003022800, 0x9000000c08b0000, 0x80003120200018, 0xc4820000624, 0x3121600018905, 0xc4898000624300, 0x122c00018915000, 0x898000644100003, 0x2000191140000c8, 0x804140004020, 0x2010c000100858]
def page226 : List Nat := [0x824000004022800, 0x90b000104828000, 0x340004121800020, 0x104898000824, 0x4222800021113, 0x10c808000864000, 0x320a00021902000, 0x8600008642c0004, 0x80002191300010c, 0x8645c0004322, 0x2811400010c8e0, 0x204080011020000, 0x104000440818002, 0x2c0011020a00088, 0x440860002204, 0x11021c0008810d, 0x4408a80022043c0, 0x20000088116000, 0x810002404040012, 0x800090103000480, 0x2404140012020, 0x9010c000480830, 0x404380012021a00, 0x114000480878002]
def page227 : List Nat := [0x5c0012022a00090, 0x484800002404, 0x12120400090901, 0x4848200024240c0, 0x121800090905000, 0x878002424340012, 0xa00090913000484, 0x2604000012122, 0x981030004c0808, 0x604140013020800, 0x10c0004c0858002, 0x540013022800098, 0x4c08b0002604, 0x13023800098117, 0x4c4808002624000, 0x120800098903000, 0x858002624140013, 0x60009890c0004c4, 0x2624540013122, 0x991000004c48b0, 0x644080013220200, 0x1040004c8818002, 0x300013220a00099, 0x4c8870002644]
def page228 : List Nat := [0x13222800099113, 0x4c88b0002644540, 0x21600099117000, 0x8180028242c0014, 0x8000a190b000508, 0x2a44340015220, 0xa9114000548898, 0xa445c0015222a00, 0x11b0005488d0002, 0x9c0015223c000a9, 0x840808002a44, 0x21020600108102, 0x840828004204100, 0x2180010810b000, 0x878004204340021, 0xc00108115000840, 0x4404000021022, 0x110102000880808, 0x404100022020600, 0x10c000880828004, 0x500022021e00110, 0x8808a8004404, 0x22120000110117, 0x884810004424040]
def page229 : List Nat := [0x120800110903000, 0x860004424140022, 0xe0011090d000884, 0x44244c0022121, 0x1181000008848a8, 0x604080023020200, 0x1040008c0818004, 0x2c0023020a00118, 0x8c0860004604, 0x23022a00118114, 0x8c08b8004604580, 0x12000011811c000, 0x8200046240c0023, 0x6001189050008c4, 0x4624300023121, 0x1189150008c4898, 0x644100023122c00, 0x90b0008c88a0004, 0x80031020000121, 0xc40818006204, 0x31020a00188104, 0xc408600062042c0, 0x21c0018810d000, 0x8b0006204540031]
def page230 : List Nat := [0x80019010d000c40, 0x64243c0032022, 0x190916000c84898, 0x604040033020000, 0x105000cc0820006, 0x300033021600198, 0xcc08a0006604, 0x33022c00198115, 0xcc4800006604700, 0x120400198901000, 0x828006624100033, 0x80019890b000cc4, 0x66244c0033121, 0x198916000cc48a8, 0x644040033220000, 0x104000cc8810006, 0x300033220a00199, 0xcc8898006644, 0x33222a00199114, 0xd008080066445c0, 0x216001a0102000, 0x8a0006804300034, 0x1a011c000d00, 0x6824040034120]
def page231 : List Nat := [0x1a090b000d04828, 0x824340034121800, 0x100000d04898006, 0x800342202001a1, 0xd08828006844, 0x34221a001a110c, 0xd088980068443c0, 0x222e001a1114000, 0x808006864000034, 0x6001a1905000d0c, 0x6864300034321, 0x1a1914000d0c898, 0xa44340034323800, 0x114000d48898006, 0x680035222e001a9, 0xd488f0006a44, 0x61104081891820b, 0x4410606c22082c3, 0x40a1b0902040d8, 0x206c2408303612, 0x81b090a050d8485, 0x862408143612141, 0x99920510c485028, 0x2082c4333241821]
def page232 : List Nat := [0x20c1184810288c2, 0x304612140a23090, 0x1184c10588c2428, 0x61314162309820c, 0x485020ac22082c4, 0x141830090a05180, 0x28c22408106012, 0x83089020c184481, 0xc22648146113240, 0x110a041844c9060, 0x6282d0623140883, 0xa0b418cc50220c4, 0x110633141883198, 0x418cc90620c6648, 0x6342418831a0a0b, 0x8810220c68682d0, 0x41888110205440, 0x22204428111022, 0x888118a0b4408c5, 0x2c06082d1603040, 0x2020b4580c1062, 0x40815162204088b, 0x2044588810622c4, 0x2d1623040a8b118]
def page233 : List Nat := [0x4588c10622c4608, 0x63304168b198204, 0xcc90622c6648151, 0x34168b1a020b458, 0x2a402208111634, 0x89008820c480441, 0x404208152021040, 0x888204480841062, 0x208312111040a90, 0x205484481022422, 0x112112041890890, 0x484c4102a426208, 0x60104089098820c, 0xc10624c0608112, 0x4089302020c498, 0x624c2208152611, 0xa93108204498441, 0x4c4208312621040, 0x1182054988c1022, 0x628112623041893, 0x205498c410224c4, 0x112631041893188, 0x498cc10624c6608, 0x634141893198a0c]
def page234 : List Nat := [0xd0d0624c6868152, 0x40898088204498, 0x5a606628113012, 0x898198a0c4c0cc5, 0x622208113033241, 0x890a044c444105a, 0x6082d3113040898, 0x20b4c4c41022622, 0x2d3133040898988, 0x4c4cc9022626608, 0x133241898999205, 0x10d062640868153, 0x40a990902044c8, 0x22642408313212, 0x8990982054c84c1, 0x642628113213041, 0x98a0c4c84c502a, 0x608313233040899, 0xa0c4c8cc5022646, 0x153233240299198, 0x4c8cc9062646648, 0x234340a991a1a01, 0x41022646868313, 0x4169b00820b4d8]
def page235 : List Nat := [0x2a6c2408113604, 0x89b09020c4d8481, 0x6c2428153612140, 0x1082044d8485062, 0x40811362104169b, 0x20c4d888102a6c4, 0x15362214089b110, 0x4d88850626c4428, 0x63104169b188204, 0x4c50226c68082d3, 0x1408a9198a04548, 0x5ac006282d6003, 0x8b0021a0b580105, 0xc02428156012140, 0x821a0b580485062, 0x4081561120408b0, 0x204584481062c22, 0x322611040b13088, 0x8d84410244c2208, 0x61204091b08820b, 0x4810646c2408163, 0x140b1b090a048d8, 0x5c6c2428323612, 0xb30090a04958441]
def page236 : List Nat := [0xc02428326012140, 0x890205984481024, 0x648166112041930, 0x204c18cc90660c6, 0x2f302304178b018, 0xcc0cc902e606628, 0x12104179819920c, 0xcc9066626648173, 0x3419991a1a05cc4, 0x5e6c0208133234, 0x99b020a0bcd8101, 0x6c2408173612040, 0x90a04cd8481066, 0x428333612140b9b, 0x201cd884105e6c2, 0x333622040b9b110, 0xcd888502e6c4408, 0x63104179b110a0c, 0xd0505e6c68082f3, 0x24199b1a1205cd8, 0x5e8c0608173634, 0x9a301820cd180c1, 0x8c2428174612041, 0x118a0bd18485066]
def page237 : List Nat := [0x4281760121409a3, 0xa04d80485066c02, 0x1360131417b0098, 0xd804c902ec02648, 0x1120409b009920c, 0x481066c22408176, 0x40bb0898204d84, 0x66c226082f6113, 0xbb0899204d844c1, 0xc22648336113240, 0x98205d884c1026, 0x6281362130419b1, 0xa0cd884c502ec42, 0xc01a00a001b1098, 0xe06205804c03e02, 0x80be0b20a609407, 0xa12411c1080ee0d, 0xc18617816214a13, 0xe1ce1be1b21a419, 0x21a2102061ee1d, 0x25e25024222a22, 0x82c22a829827e27, 0x831a30e3022e62d, 0xe36a36034c33e32]
def page238 : List Nat := [0x83b83ae3a639437, 0x83fa3f03e23da3c, 0xe45844842c41e40, 0x44b64a849247c45, 0x84f64e84dc4d24c, 0xa55e54a53e52450, 0x85a659a58c57656, 0xe5f45e65d45c85b, 0x264063662661c5f, 0x46a868a67a66865, 0x471a7006ee6d06b, 0x75074473873072, 0x87a679678477276, 0x47fc7e47da7cc7b, 0x85284882881880, 0xe8c68a888687c86, 0x29329169028f88d, 0x297496895a95094, 0x9e29d89ca9aa99, 0x6a3ca30a1ca0c9f, 0x4a96a84a66a52a4, 0xcb04ae6ad6ac4ab, 0xab62b50b3eb32b1, 0x6bb8b9ab88b7cb6]
def page239 : List Nat := [0x2bf6beebe2bd8bc, 0x8c48c3ac24c14c0, 0x8ca6c88c78c66c5, 0x8cf8ce8cd4cc2cb, 0x8d3ed36d1ed12d0, 0x4d90d84d74d68d5, 0xede4dd6dc2dbcda, 0xee4ce32e1ae00de, 0xaeace90e82e6ce5, 0x6f02eeaed8ec8eb, 0x8f5cf4ef32f22f1, 0x8f94f8af7ef72f6, 0x6fdcfd6fccfbcfa, 0x906304102b010ff, 0xd0db0c30ab08b07, 0x313b12910b0fd0e, 0x51b319f18117115, 0x32191f91e91d11c, 0xb28526d25f24323, 0x72e72c92bf2a929, 0x82fb9ae60240602, 0xa61ad4b4ad00a81, 0x444018450961098, 0x6261ba420924082]
def page240 : List Nat := [0x26b9046a0240c9b, 0x404c068002a1089, 0xb022287f0323083, 0x60a842060264240, 0xe0c8983509238c1, 0x8060e4250d23388, 0xe90a48620960a82, 0x5e23c0c82a0b17, 0x49691c480429018, 0x80d924950309602, 0xb81ce6b980981, 0x20a948068180894, 0x350d0339bc710e, 0x639028061ca719c, 0x6073acea90c0603, 0x20a8c67d0120200, 0x4c86e4b2121d02, 0x21e93e4f1361c87, 0x4e2b883e02a8484, 0x20b82c4f93c3087, 0x6a108018032d104, 0xa6881a0581203a8, 0x516c59159fc0a9e, 0xe298220a81e0681]
def page241 : List Nat := [0xc7392e289324c36, 0x6b902a2f93e4f0a, 0x86181c05818ba2e, 0xfc040078267500, 0x807a000f0380d00, 0xe2e9f608a027f1f, 0x2d8b600983c310b, 0x604a8ca28821d03, 0x804bc8108263281, 0x68a421079fc0c89, 0xc0a972101080681, 0x81096a298ba5d0a, 0x411008e701c0901, 0xc5e97e298aa621f, 0x62b0a4278240897, 0xc1082a070180998, 0xa10a00bd2f21083, 0x8d182a0b8320982, 0x10a5a138529634, 0xc1304a1202a9283, 0x40c82a79a3a0fa5, 0x2481c48a8428d1d, 0x6318c210a288983, 0x5bb50d4b4e4321]
def page242 : List Nat := [0xc06812962cc1083, 0xa969665a9729601, 0x82e964928320c02, 0x2c02fe388be9416, 0x24802a068e60630, 0xe0a1264891c458e, 0x8090e4848d6350c, 0x6073b2ec3ae0610, 0x2070187d0160200, 0xc8044110c3e0a82, 0x86518c0882a669f, 0x2679fe7e1f66819, 0xc070130e0340b20, 0xf0b42a7f0320a87, 0x59207102a10c2, 0x4059da4503c88a2, 0xe798c2421de411d, 0x22caa60f01e3290, 0x85f892261867504, 0x62408e0c82a5f17, 0x43f4020a8420602, 0x80c82a8e0f00fa3, 0xcba824060ee8c0e, 0x8070c66caeebc2e]
def page243 : List Nat := [0x41e0169f8427500, 0xc0f1e20d01e0686, 0x21504e0f272711c, 0x28a82a480429d27, 0xa069de371c4db03, 0xe1382ac6b18c58f, 0x109488d040110b, 0xc078188aaf80c92, 0xa0ca722f1745a83, 0xe8ac00ff9086b82, 0xa300bc6182a078b, 0xa443def70c867bd, 0x80781a073ca0882, 0x4338cc079de2f82, 0x6f50e43896a0a8d, 0x8b88420a8caf63d, 0xc1083c231d40701, 0x46418c18064679f, 0x27f05c168240899, 0xe4f02a680666686, 0x6771da4c9d64a9d, 0xa741c40a93e7993, 0xc02006073eefb3e, 0x8f9be46b82a7b86]
def page244 : List Nat := [0xa7a0420b01c05be, 0x2f82607012922c, 0xe0d94e550345584, 0xa108269c9b69c1a, 0xc0d82a003c6f102, 0x80f8c205b5ed710, 0x48e2340c8400a8c, 0x4089ae6c99e2e0b, 0x8659946a9a46302, 0xa298e4681b46c10, 0xc2a0d208a8e3502, 0xa108e234028060a, 0xc7791a112a44a02, 0x27b0fa07c5113c4, 0x6dd3720a8220501, 0xab7818108100637, 0xe440240d2e0b702, 0xc420a66a9020490, 0xa4f0368482a430a, 0xc0aa640c92c4fc6, 0x20b1b41041504a2, 0x26da426b9040903, 0xd4170788340d84, 0x4e49329902a8390]
def page245 : List Nat := [0xec330a3e8bee5b9, 0xa8180a98a06b0, 0xc073b8edbb40692, 0x438a72841284803, 0xa1d8701a8220a87, 0xa848d4338280607, 0x85d8420b83e390d, 0xc57158098601014, 0xa7e1fc0a94e7f14, 0xdf93c4802a089f, 0x20a93e84816e0b8, 0xa888468722a1384, 0x80a8428b8521404, 0x8d11a1103e0692, 0x8f81b2f88360a92, 0x711ca969700701, 0xe0c02408a4e931c, 0xa961c8959c2471b, 0xae438ee30100c82, 0xc599628a8225a82, 0x2fa2488a1c5c96, 0xc421ae090228b17, 0x86c224889aa69a1, 0x20a22c6d22a6ca2]
def page246 : List Nat := [0xaff3fafe0be778e, 0x206a7e0a81e3902, 0x4320b6062809f04, 0x20a81c098643183, 0x4a482229a2d1284, 0x6b3a040a83288a9, 0xa3a80ccd9c40a82, 0xe4fb7cdeb784202, 0x208b70db82a2993, 0xa2c0227302a7493, 0x4109c42991c289c, 0xa93830061044225, 0xc7818180424325, 0xe0992e3301a0ab2, 0x88140499eae8b, 0xcc702a138180980, 0xf1716a3a81e0880, 0xc059f03881f1845, 0x80702c0a8420901, 0x21d0320986c1100, 0x2352340f8280604, 0x23303a0a8e4510d, 0x1062040a835110e, 0x26303e652348e1a]
def page247 : List Nat := [0x43903e8d8320a99, 0x6348cc8e0320aa3, 0xa5e97808a126121, 0x48420e5fa080901, 0xc84842622184807, 0xcf48224a12e9c83, 0x47f02a0781c060a, 0xc08a02801fe7e1f, 0x2388e0378d8350c, 0xa2fa2a0d02a4204, 0x687a1c8ba2a0882, 0xa3222c300ba888b, 0xa848f8318dc0781, 0x8420e3b0ea8281, 0xc3e8f0862167b92, 0x8e9ba48482a480f, 0x6710fc4f0fa3e3a, 0x2a40ac3c0a63f0f, 0xc068aa3b8a00902, 0xc782a060423e8e, 0xd1bc6d1a82a84b2, 0x86d01e020020713, 0xa0c0240c9aa6ba5, 0xa6ca506b1046a24]
def page248 : List Nat := [0x20c8ca098c80b25, 0xc0aa1a0ca469224, 0xc83c070029aaf, 0x6921720b4280d20, 0x62f8265d2420c82, 0x46b8fa0a8e667ad, 0x46b1aa690226c82, 0xc420f23c0e8069b, 0x264194298ac680f, 0xe2a8a8280240899, 0x630244219a4319, 0xc41100088186519, 0x20d1a04390a6b9f, 0x65515010bc209a1, 0x61081ec702a0602, 0x6309a205c348582, 0x28381e0602a098c, 0x2f8ba2da088621, 0x40b104918423217, 0x40a842422420604, 0x84e1324c12a0fa3, 0x4060420982e4f23, 0xc10026908443a82, 0x20901ca80aa1094]
def page249 : List Nat := [0x113c4c7b0fa77aa, 0xa2f8f62f8fc07c5, 0x25a81ef43cef30f, 0x6778f03a8e83f0e, 0x6d63560983c3e0f, 0xa7f0c84981e0601, 0x7d8e8800f60882, 0x23f0f83d1fa7e0f, 0xa11108538403ea0, 0xa420425694c4510, 0xe0280006ac8b182, 0x20725a7c8420c01, 0x6c90be078240600, 0x60480c388faca32, 0xe7796a018020001, 0xc6199ef7bdcf68b, 0xc63976078240880, 0xc4f9320793c2f83, 0x80f142320f82e92, 0xe3281ad6356061b, 0x80e8380aa963201, 0x80913c248422309, 0x81113a259304b09, 0x64a0340a9525408]
def page250 : List Nat := [0xe480a67011a0692, 0x2068170d81c0d03, 0x49213e4c82c9084, 0xa3e01a4813a9182, 0x2479183a82405b5, 0x23d8fc498fa490f, 0x88d1023f82a1004, 0xaa6a98350883923, 0xa4802a3882a2683, 0xe7f0420aa0a4701, 0x40996a1001ad033, 0x10440e8aa120c83, 0x288012420241092, 0x6991544322a6ba2, 0xa579509b14c5726, 0x5f9781a8746182, 0x20f87a621821c87, 0x1002407238be84, 0xa6747b1e4760a92, 0xc0aade060420322, 0x22f96a3e864b82d, 0x23f1860abf6fd3f, 0xe432c2b12c00a84, 0x8d281e0683c0481]
def page251 : List Nat := [0x6400b44390c3090, 0xc108c8788be2e8b, 0xe09228d5032420d, 0x6058260c82a319a, 0xc7e1da08a060f03, 0x248fc809e4779f, 0x23b89c0ea9ea70f, 0x6f83e20783c3e8f, 0xc1d02a3201a0601, 0xc4fab8adab48493, 0xf014afabc0983, 0x60901407c5514a0, 0x434691946285c6, 0x80f0160481e0717, 0xc420280aa724410, 0x4389ea7f0d4340c, 0x61aee8ba0e78e, 0x20680c09334ccb3, 0xa8a2f8bda2a4803, 0x2033a8e9ba44802, 0xe0c9e89b02a4f21, 0xecb32a0a96a991d, 0x82f8e20880c0632, 0x207a5a960be328c]
def page252 : List Nat := [0x97254930300a83, 0x20ca1210bbe1084, 0x4b98e058184f34, 0x8f832908fc0b12, 0x80114a0a8429224, 0xc5312c40e23e80, 0xa328c80602a0681, 0xa060a6078222b02, 0x83e8ae2f8b82801, 0x40c82a3f08c3c08, 0x6968f23a01a2188, 0xa0c8300a9da779e, 0xa96252770ba7624, 0x8c1b04060e20a96, 0x530a60d04e2fb0, 0x49902a520b05504, 0xa26a99a5e0c8d, 0x4c82a108e2358d, 0xa060be4f0a64d13, 0x407b02c02fe3882, 0x4380ce3301a320e, 0x442042818407f03, 0xac882a108180b95, 0x49a8323282a3501]
def page253 : List Nat := [0xc748222fa6007a6, 0xe0681604c3d0e81, 0x40c994991a09a87, 0xe9a266659909802, 0xcdab68480220a99, 0xc10a2c499c406b6, 0xe07a4609a489082, 0x40581a2e82a2f0b, 0x2ac2ae5a84e389d, 0x43382a0a018162b, 0x61d07c9c8e4368d, 0xc2f8ca9c2109d83, 0x64483c9d0429c83, 0xc779e89cadab602, 0xa0d1ae100bc1083, 0xa09822869524215, 0xca2a883e07404c1, 0xe3f0823e9c40ea8, 0xc3eb3cceb38069d, 0xa72a3a2f8240880, 0x4712348c83e7302, 0x20f013010320d83, 0x60882a77a2a0983, 0xe88a1c799e0769d]
def page254 : List Nat := [0x87784e3ea2c898b, 0x8068560aaacaaaa, 0x4908e43f0f23c0e, 0x89123c0ca480b0d, 0x25aa46358ce0a82, 0xf1845f171f00a0e, 0x4420f6380e40a81, 0xc400e8088184302, 0xe7f10e418f0410e, 0x42208c678fc319a, 0xa65884630320a99, 0x61502a148b06808, 0x3e8ae1389e088a, 0xc168e81902a0886, 0xc06866178f0170e, 0x7f02a0a0fc3d9f, 0xec2107c1c4202, 0xca643f0e43886, 0xc9a262980249a8f, 0xc3c2423f0fa3c8e, 0x23e9460ec491182, 0x203c330c01a8483, 0x57044480264601, 0x2482123e14e543c]
def page255 : List Nat := [0xa8a9ee0ec270942, 0xa3f0fa1d0f03b0e, 0x8183e8f9be46b82, 0x51cc70420e43882, 0x60481a032280947, 0xcfa82a711fc8817, 0xc740fa7b874fbbe, 0xa3d9203c8f03b0f, 0x66747b1e4764802, 0xe3334c4202a8a92, 0x84390c429fc340f, 0xf0e4389ea3501, 0x68396604c0c0997, 0x86e8220da185c8c, 0xa1e9b41c1aa9e87, 0x20d81cef3ba0982, 0x769d42f82a778e, 0x390da350cc799e, 0xe7ea789d8601a27, 0x20682a848e09ca6, 0x88520e340ce8202, 0x6390c21d0d40a21, 0xc0a81ec28fa2f82, 0x63e0f63a018320f]
def page256 : List Nat := [0xa0882a7a1e62c0c, 0xe0696a3e9de298b, 0x85c968599600a8b, 0x4108fc5c0f23c0e, 0xa420741c0c24502, 0x6e212e4b2120882, 0x44fa181d2108301, 0x6411a86d1b60903, 0xc0a9b22b0aa6b8a, 0x43e138e1b84109f, 0xe6a9a4858c60d83, 0x20f1b4861ae84a0, 0x80a860d9b648004, 0x43883aa1a84a082, 0x7a8da34020060e, 0x3fa43fc31ff188e, 0xc41fc43fe887f10, 0x1ff30ffa17fd0ff, 0xc30ff10ffccbfa4, 0x2ffa0ff4c6fea5f, 0xf98df54bf821fd3, 0x87fd03fa61fe10f, 0x223fe21fc41ff1, 0x747000020802930]
def page257 : List Nat := [0x200000800002fd, 0x280001000006000, 0x4000180000b0000, 0x130000780003, 0xb00005400028, 0x6c00034000170, 0x4e0001e0000e00, 0xb040820000d400, 0x606042c30208081, 0xc402161890b0c08, 0x8810410c8588242, 0x408622042d1020a, 0x4312020a901044, 0x218909054848224, 0xb4c082a6041121, 0x2a6241130218981, 0x1312189890b4c48, 0x9910c4c882a6441, 0x4082c2041152208, 0x412102190810b8, 0x2091010c88082c4, 0x48848644241621, 0x646042e3020b181, 0x231217189048c08]
def page258 : List Nat := [0x98104c4085e2041, 0xc48266043330217, 0x4413312199890bc, 0x217a010bcc88666, 0xd0c85e8443341, 0x33c342d211a120a, 0x7d7b6e675e564b4, 0x3b7afa5a1968d87, 0x708911ded9d3cac, 0x264460a12101018, 0x64a1860a1210a1a, 0x1b143448c142d3a, 0x9f3c2c50c16509, 0x689100400c1c81, 0xe030a162818f3a3, 0x24860d182c93a72, 0x940a06182c513a, 0x71122312282c505, 0x234418509182c04, 0x6cc0c5040c16292, 0x1d86162460b140a, 0x64b98282860a7af, 0xa305880c1000224, 0x12b97ad582c9061]
def page259 : List Nat := [0xa282e78c1a2060a, 0xc1629931604830, 0x2010048b1514444, 0x4a33221c30e1818, 0x30501052e48b942, 0x309366ed5a0b14, 0x40080a54ad4a81, 0x3282a70c1a30584, 0x8821020bf7c2858, 0x88a0650e0d22305, 0x20cb54fc6458828, 0x2d]
def storagePage (p : Nat) : List Nat := (if p < 130 then (if p < 65 then (if p < 32 then (if p < 16 then (if p < 8 then (if p < 4 then (if p < 2 then (if p < 1 then page0 else page1) else (if p < 3 then page2 else page3)) else (if p < 6 then (if p < 5 then page4 else page5) else (if p < 7 then page6 else page7))) else (if p < 12 then (if p < 10 then (if p < 9 then page8 else page9) else (if p < 11 then page10 else page11)) else (if p < 14 then (if p < 13 then page12 else page13) else (if p < 15 then page14 else page15)))) else (if p < 24 then (if p < 20 then (if p < 18 then (if p < 17 then page16 else page17) else (if p < 19 then page18 else page19)) else (if p < 22 then (if p < 21 then page20 else page21) else (if p < 23 then page22 else page23))) else (if p < 28 then (if p < 26 then (if p < 25 then page24 else page25) else (if p < 27 then page26 else page27)) else (if p < 30 then (if p < 29 then page28 else page29) else (if p < 31 then page30 else page31))))) else (if p < 48 then (if p < 40 then (if p < 36 then (if p < 34 then (if p < 33 then page32 else page33) else (if p < 35 then page34 else page35)) else (if p < 38 then (if p < 37 then page36 else page37) else (if p < 39 then page38 else page39))) else (if p < 44 then (if p < 42 then (if p < 41 then page40 else page41) else (if p < 43 then page42 else page43)) else (if p < 46 then (if p < 45 then page44 else page45) else (if p < 47 then page46 else page47)))) else (if p < 56 then (if p < 52 then (if p < 50 then (if p < 49 then page48 else page49) else (if p < 51 then page50 else page51)) else (if p < 54 then (if p < 53 then page52 else page53) else (if p < 55 then page54 else page55))) else (if p < 60 then (if p < 58 then (if p < 57 then page56 else page57) else (if p < 59 then page58 else page59)) else (if p < 62 then (if p < 61 then page60 else page61) else (if p < 63 then page62 else (if p < 64 then page63 else page64))))))) else (if p < 97 then (if p < 81 then (if p < 73 then (if p < 69 then (if p < 67 then (if p < 66 then page65 else page66) else (if p < 68 then page67 else page68)) else (if p < 71 then (if p < 70 then page69 else page70) else (if p < 72 then page71 else page72))) else (if p < 77 then (if p < 75 then (if p < 74 then page73 else page74) else (if p < 76 then page75 else page76)) else (if p < 79 then (if p < 78 then page77 else page78) else (if p < 80 then page79 else page80)))) else (if p < 89 then (if p < 85 then (if p < 83 then (if p < 82 then page81 else page82) else (if p < 84 then page83 else page84)) else (if p < 87 then (if p < 86 then page85 else page86) else (if p < 88 then page87 else page88))) else (if p < 93 then (if p < 91 then (if p < 90 then page89 else page90) else (if p < 92 then page91 else page92)) else (if p < 95 then (if p < 94 then page93 else page94) else (if p < 96 then page95 else page96))))) else (if p < 113 then (if p < 105 then (if p < 101 then (if p < 99 then (if p < 98 then page97 else page98) else (if p < 100 then page99 else page100)) else (if p < 103 then (if p < 102 then page101 else page102) else (if p < 104 then page103 else page104))) else (if p < 109 then (if p < 107 then (if p < 106 then page105 else page106) else (if p < 108 then page107 else page108)) else (if p < 111 then (if p < 110 then page109 else page110) else (if p < 112 then page111 else page112)))) else (if p < 121 then (if p < 117 then (if p < 115 then (if p < 114 then page113 else page114) else (if p < 116 then page115 else page116)) else (if p < 119 then (if p < 118 then page117 else page118) else (if p < 120 then page119 else page120))) else (if p < 125 then (if p < 123 then (if p < 122 then page121 else page122) else (if p < 124 then page123 else page124)) else (if p < 127 then (if p < 126 then page125 else page126) else (if p < 128 then page127 else (if p < 129 then page128 else page129)))))))) else (if p < 195 then (if p < 162 then (if p < 146 then (if p < 138 then (if p < 134 then (if p < 132 then (if p < 131 then page130 else page131) else (if p < 133 then page132 else page133)) else (if p < 136 then (if p < 135 then page134 else page135) else (if p < 137 then page136 else page137))) else (if p < 142 then (if p < 140 then (if p < 139 then page138 else page139) else (if p < 141 then page140 else page141)) else (if p < 144 then (if p < 143 then page142 else page143) else (if p < 145 then page144 else page145)))) else (if p < 154 then (if p < 150 then (if p < 148 then (if p < 147 then page146 else page147) else (if p < 149 then page148 else page149)) else (if p < 152 then (if p < 151 then page150 else page151) else (if p < 153 then page152 else page153))) else (if p < 158 then (if p < 156 then (if p < 155 then page154 else page155) else (if p < 157 then page156 else page157)) else (if p < 160 then (if p < 159 then page158 else page159) else (if p < 161 then page160 else page161))))) else (if p < 178 then (if p < 170 then (if p < 166 then (if p < 164 then (if p < 163 then page162 else page163) else (if p < 165 then page164 else page165)) else (if p < 168 then (if p < 167 then page166 else page167) else (if p < 169 then page168 else page169))) else (if p < 174 then (if p < 172 then (if p < 171 then page170 else page171) else (if p < 173 then page172 else page173)) else (if p < 176 then (if p < 175 then page174 else page175) else (if p < 177 then page176 else page177)))) else (if p < 186 then (if p < 182 then (if p < 180 then (if p < 179 then page178 else page179) else (if p < 181 then page180 else page181)) else (if p < 184 then (if p < 183 then page182 else page183) else (if p < 185 then page184 else page185))) else (if p < 190 then (if p < 188 then (if p < 187 then page186 else page187) else (if p < 189 then page188 else page189)) else (if p < 192 then (if p < 191 then page190 else page191) else (if p < 193 then page192 else (if p < 194 then page193 else page194))))))) else (if p < 227 then (if p < 211 then (if p < 203 then (if p < 199 then (if p < 197 then (if p < 196 then page195 else page196) else (if p < 198 then page197 else page198)) else (if p < 201 then (if p < 200 then page199 else page200) else (if p < 202 then page201 else page202))) else (if p < 207 then (if p < 205 then (if p < 204 then page203 else page204) else (if p < 206 then page205 else page206)) else (if p < 209 then (if p < 208 then page207 else page208) else (if p < 210 then page209 else page210)))) else (if p < 219 then (if p < 215 then (if p < 213 then (if p < 212 then page211 else page212) else (if p < 214 then page213 else page214)) else (if p < 217 then (if p < 216 then page215 else page216) else (if p < 218 then page217 else page218))) else (if p < 223 then (if p < 221 then (if p < 220 then page219 else page220) else (if p < 222 then page221 else page222)) else (if p < 225 then (if p < 224 then page223 else page224) else (if p < 226 then page225 else page226))))) else (if p < 243 then (if p < 235 then (if p < 231 then (if p < 229 then (if p < 228 then page227 else page228) else (if p < 230 then page229 else page230)) else (if p < 233 then (if p < 232 then page231 else page232) else (if p < 234 then page233 else page234))) else (if p < 239 then (if p < 237 then (if p < 236 then page235 else page236) else (if p < 238 then page237 else page238)) else (if p < 241 then (if p < 240 then page239 else page240) else (if p < 242 then page241 else page242)))) else (if p < 251 then (if p < 247 then (if p < 245 then (if p < 244 then page243 else page244) else (if p < 246 then page245 else page246)) else (if p < 249 then (if p < 248 then page247 else page248) else (if p < 250 then page249 else page250))) else (if p < 255 then (if p < 253 then (if p < 252 then page251 else page252) else (if p < 254 then page253 else page254)) else (if p < 257 then (if p < 256 then page255 else page256) else (if p < 258 then page257 else (if p < 259 then page258 else page259)))))))))
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
  | 2 => BitVec.ofNat 152 (big [0x84002cb0002821, 0x84200165800141, 0xb2c000a])
  | 3 => BitVec.ofNat 152 (big [0xef7e3fefddfebbd, 0xef7bf1ff7eeff5d, 0xffbf77fa])
  | 4 => BitVec.ofNat 152 (big [0xe20e0004100c01c, 0x71070002080600, 0x104030])
  | 5 => BitVec.ofNat 152 (big [0xfbdfeedffecfc7f, 0x1fdeff76fff67e3, 0xbb7ffb3f])
  | _ => 0

def a1Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x8fbd751fa47fcb1, 0x2c7deba8fd23fe5, 0xd47e91ff])
  | 3 => BitVec.ofNat 152 (big [0xa881d60404daa95, 0xa5440eb02026d54, 0x5810136a])
  | 4 => BitVec.ofNat 152 (big [0xfdf8de7a73de21f, 0x87efc6f3d39ef10, 0x79e9cf78])
  | 5 => BitVec.ofNat 152 (big [0xdc145162e04443b, 0xee0a28b1702221, 0x458b8111])
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
  | 4 => field storageWord (369+i*26) 26
  | 5 => field storageWord (1474+i*15) 15
  | 6 => field storageWord (1703+i*4) 4
  | _ => 0

def a1Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 8 3 (field storageWord (299+(tag % 3)*4) 4) tag
  | 4 => hashRow 28 28 (field storageWord (1097+(tag % 28)*6) 6) tag
  | 5 => hashRow 6 12 (field storageWord (1564+(tag % 12)*4) 4) tag
  | 6 => 0
  | _ => 0

def a1Hints (k i : Nat) : List Nat :=
  match k with
  | 3 => hintsAt storageWord 317 4 353 2 311 2 i
  | 4 => hintsAt storageWord 1273 5 1418 2 1265 2 i
  | 5 => hintsAt storageWord 1620 5 1655 2 1612 2 i
  | 6 => hintsAt storageWord 1715 3 1721 2 1707 2 i
  | _ => []

def a1 : Atlas := ⟨6,rawDecor 60 a1Pos a1Neg,repeatWord 1081144350458515200,a1Count,a1Rec,(fun _ _ => 0),a1Loc⟩
def a1Domains : Catalog := [(repeatWord 1085102592571150095, 4), (repeatWord 18374966859414961920, 4), (repeatWord 281470681808895, 4), (repeatWord 18446744069414584320, 4)]
def a2Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xffdfffdfb7ff77b, 0xfdfffdfb7ff77bd, 0x7ff77bdf])
  | 1 => BitVec.ofNat 152 (big [0x55be97b1cbdde96, 0x5be97b1cbdde96b, 0xbdde96b5])
  | 4 => BitVec.ofNat 152 (big [0xec6fcda87d77dac, 0xc6fcda87d77dac3, 0xd77dac3e])
  | 5 => BitVec.ofNat 152 (big [0x9050d58124bc532, 0x50d58124bc5321, 0x4bc53219])
  | _ => 0

def a2Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x40000101004103, 0x400001010041032, 0x410320])
  | 1 => BitVec.ofNat 152 (big [0xa849260542f1694, 0x849260542f16944, 0x2f16944a])
  | 4 => BitVec.ofNat 152 (big [0x129303ab2121ca8, 0x29303ab2121ca8c, 0x121ca8c1])
  | 5 => BitVec.ofNat 152 (big [0x677baaf9563d5b3, 0x77baaf9563d5b3e, 0x63d5b3e6])
  | _ => 0

def a2Count (k : Nat) : Nat :=
  match k with
  | 4 => 12
  | 5 => 1
  | _ => 0

def a2Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (1729+i*15) 15
  | 5 => field storageWord (2029+i*4) 4
  | _ => 0

def a2Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 12 12 (field storageWord (1909+(tag % 12)*5) 5) tag
  | 5 => 0
  | _ => 0

def a2Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 1978 3 2017 2 1969 3 i
  | 5 => hintsAt storageWord 2051 3 2057 3 2033 3 i
  | _ => []

def a2 : Atlas := ⟨5,rawDecor 51 a2Pos a2Neg,repeatWord 12297791854194109098,a2Count,a2Rec,(fun _ _ => 0),a2Loc⟩
def a2Domains : Catalog := [(repeatWord 7378697629483820646, 4), (repeatWord 6149008514797120170, 4), (repeatWord 12297829381041378645, 4), (repeatWord 14757226376558555955, 4), (repeatWord 3689348817318890700, 4), (repeatWord 281474976645120, 4)]
def a3Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x4001500108100d, 0x4001500108100d, 0x108100d])
  | 2 => BitVec.ofNat 152 (big [0x1990c8288e141d0, 0x1990c8288e141d0, 0x88e141d0])
  | 4 => BitVec.ofNat 152 (big [0xb7d577bf15e96ed, 0xb7d577bf15e96ed, 0xf15e96ed])
  | 5 => BitVec.ofNat 152 (big [0xdffedf7ffed79df, 0xdffedf7ffed79df, 0xffed79df])
  | _ => 0

def a3Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xf97deedad7db8bd, 0xf97deedad7db8bd, 0xad7db8bd])
  | 2 => BitVec.ofNat 152 (big [0xe61f2f6cbcfa3d4, 0xe61f2f6cbcfa3d4, 0xcbcfa3d4])
  | 4 => BitVec.ofNat 152 (big [0x482f490e18582e5, 0x482f490e18582e5, 0xe18582e5])
  | 5 => BitVec.ofNat 152 (big [0x2109029006d289c, 0x2109029006d289c, 0x6d289c])
  | _ => 0

def a3Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a3Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (2075+i*4) 4
  | _ => 0

def a3Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a3Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2080 1 2082 1 2079 1 i
  | _ => []

def a3 : Atlas := ⟨4,rawDecor 54 a3Pos a3Neg,repeatWord 4557417642109108224,a3Count,a3Rec,(fun _ _ => 0),a3Loc⟩
def a3Domains : Catalog := [(repeatWord 1085102592571150095, 4)]
def a4Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfeffe7fcd9fefc5, 0xf7ff3fe6cff7e2b, 0x67fbf15f])
  | 2 => BitVec.ofNat 152 (big [0x7f9edaaf36cf63b, 0xfcf6d579b67b1de, 0xdb3d8ef3])
  | 3 => BitVec.ofNat 152 (big [0xb7e664dbdc525b4, 0xbf3326dee292da4, 0x71496d25])
  | 5 => BitVec.ofNat 152 (big [0x10b84480885e685, 0x85c2240442f342a, 0x2179a150])
  | _ => 0

def a4Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x20010140040805, 0x100080a0020402c, 0x1020160])
  | 2 => BitVec.ofNat 152 (big [0x8005a489a088612, 0x2d244d0443091, 0x8221848c])
  | 3 => BitVec.ofNat 152 (big [0x4812e948b51b5b0, 0x40974a45a8dad83, 0xd46d6c1a])
  | 5 => BitVec.ofNat 152 (big [0xe3d7bfddaeeee97, 0x1ebdfeed77774bd, 0xbbbba5ef])
  | _ => 0

def a4Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a4Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (2083+i*4) 4
  | _ => 0

def a4Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a4Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2088 1 2090 1 2087 1 i
  | _ => []

def a4 : Atlas := ⟨4,rawDecor 45 a4Pos a4Neg,repeatWord 12295014591103695610,a4Count,a4Rec,(fun _ _ => 0),a4Loc⟩
def a4Domains : Catalog := [(repeatWord 71777214294589695, 4)]
def a5Pos : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x8dfdfc9fffa78df, 0xfa78dfdfc9fffa7, 0xdfdfc9ff])
  | 3 => BitVec.ofNat 152 (big [0xc484812d0020c4, 0x20c484812d002, 0xc484812d])
  | 4 => BitVec.ofNat 152 (big [0x81a1a00c058081a, 0x58081a1a00c0580, 0x1a1a00c0])
  | 5 => BitVec.ofNat 152 (big [0xfffffffffffffff, 0xfffffffffffffff, 0xffffffff])
  | _ => 0

def a5Neg : Nat → Bits
  | 2 => BitVec.ofNat 152 (big [0x8d3289e0390b8d3, 0x90b8d3289e0390b, 0xd3289e03])
  | 3 => BitVec.ofNat 152 (big [0xce67b2f5ee12ce6, 0xe12ce67b2f5ee12, 0xe67b2f5e])
  | 4 => BitVec.ofNat 152 (big [0xe9ae4fb5a4c7e9a, 0x4c7e9ae4fb5a4c7, 0x9ae4fb5a])
  | 5 => BitVec.ofNat 152 (big [0x6ae06021a6046ae, 0x6046ae06021a604, 0xae06021a])
  | _ => 0

def a5Count (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0

def a5Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (2091+i*4) 4
  | _ => 0

def a5Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => 0
  | _ => 0

def a5Hints (k i : Nat) : List Nat :=
  match k with
  | 4 => hintsAt storageWord 2096 1 2098 1 2095 1 i
  | _ => []

def a5 : Atlas := ⟨4,rawDecor 60 a5Pos a5Neg,repeatWord 67818972417884160,a5Count,a5Rec,(fun _ _ => 0),a5Loc⟩
def a5Domains : Catalog := [(repeatWord 18446744069414584320, 4)]
def a6Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdc3bfc09b187d2d, 0xbceb76bfdbf7b57, 0xbdfcf7fe])
  | 1 => BitVec.ofNat 152 (big [0xe29e33fa66587c7, 0xd7feb9e025fa4fd, 0x4bee8feb])
  | 2 => BitVec.ofNat 152 (big [0x3fde8bdebe332b2, 0x4fffbf5c56095fa, 0x865f69bb])
  | 4 => BitVec.ofNat 152 (big [0x35e337666cfac58, 0xfd6cee82ffb5600, 0x731f5370])
  | 5 => BitVec.ofNat 152 (big [0x2807805ab692da1, 0xb3e131a01bdf2f1, 0xae1644c2])
  | _ => 0

def a6Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x800000001004900, 0x2009080042, 0x440000])
  | 1 => BitVec.ofNat 152 (big [0x429330120640447, 0x15d01802201ac11, 0x91112100])
  | 2 => BitVec.ofNat 152 (big [0x40cc1cca8132b0, 0x200424484e00180, 0x408a146a])
  | 4 => BitVec.ofNat 152 (big [0x30431610e4fa418, 0xc23910794d25481, 0x12199355])
  | 5 => BitVec.ofNat 152 (big [0xea4314dff6d6db1, 0x62757eecffd17f3, 0x917d5fdc])
  | _ => 0

def a6Count (k : Nat) : Nat :=
  match k with
  | 4 => 7
  | 5 => 88
  | 6 => 71
  | 7 => 19
  | 8 => 1
  | _ => 0

def a6Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (2099+i*49) 49
  | 5 => field storageWord (2454+i*38) 38
  | 6 => field storageWord (8576+i*27) 27
  | 7 => field storageWord (16728+i*16) 16
  | 8 => field storageWord (18704+i*5) 5
  | _ => 0

def a6Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 7 4 (field storageWord (2442+(tag % 4)*3) 3) tag
  | 5 => hashRow 88 88 (field storageWord (5798+(tag % 88)*8) 8) tag
  | 6 => hashRow 71 71 (field storageWord (10493+(tag % 71)*7) 7) tag
  | 7 => hashRow 19 10 (field storageWord (17032+(tag % 10)*5) 5) tag
  | 8 => 0
  | _ => 0

def a6Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 7558 7 8181 5 6502 33 i
  | 6 => hintsAt storageWord 13574 9 14222 7 10990 34 i
  | 7 => hintsAt storageWord 17964 7 18104 6 17082 21 i
  | 8 => hintsAt storageWord 18724 3 18730 3 18709 3 i
  | _ => []

def a6 : Atlas := ⟨8,rawDecor 55 a6Pos a6Neg,repeatWord 16927598236833606378,a6Count,a6Rec,(fun _ _ => 0),a6Loc⟩
def a6Domains : Catalog := [(repeatWord 6149008514797120170, 7), (repeatWord 12297829381041378645, 7), (repeatWord 281474976645120, 7), (repeatWord 3689348814741910323, 6), (repeatWord 1085102592571150095, 6), (repeatWord 6148914691236517205, 5), (repeatWord 281470681808895, 5), (repeatWord 18446462603027742720, 5), (repeatWord 4294967295, 5), (repeatWord 18446744069414584320, 5), (repeatWord 7378697629483820646, 5), (repeatWord 6510615555426900570, 5), (repeatWord 6148820867675914240, 4), (repeatWord 1431655765, 4), (repeatWord 281470681743360, 4)]
def a7Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xb936f5e3aeb700e, 0xa7bcc797f8d4aab, 0xbe34efef])
  | 1 => BitVec.ofNat 152 (big [0x35eb81dfd8d1bd1, 0x7c78bb3d1fa9594, 0xf9ffa922])
  | 2 => BitVec.ofNat 152 (big [0xd6c42a69f12a765, 0xb9139efb4deb673, 0xdff3155f])
  | 3 => BitVec.ofNat 152 (big [0xeecdae1e2b4ccb2, 0x54d3bbeee3129de, 0x507ef7d5])
  | 5 => BitVec.ofNat 152 (big [0xc9b1f33f97a0e58, 0x266c56917675078, 0x5546f71b])
  | _ => 0

def a7Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x10400400407000, 0x401000100100a0, 0xa80400])
  | 1 => BitVec.ofNat 152 (big [0x30aa9010c0d0051, 0x1004c500120000, 0x90509280])
  | 2 => BitVec.ofNat 152 (big [0x4060290028704, 0xdc20084083642, 0x28024142])
  | 3 => BitVec.ofNat 152 (big [0x861006062b008a2, 0x9a008206140001c, 0x40040029])
  | 5 => BitVec.ofNat 152 (big [0xca9bf50bd3a0e58, 0x704a1e8e9442614, 0x9a017b48])
  | _ => 0

def a7Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a7Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (18745+i*5) 5
  | _ => 0

def a7Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a7Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 18751 1 18753 1 18750 1 i
  | _ => []

def a7 : Atlas := ⟨7,rawDecor 47 a7Pos a7Neg,repeatWord 18368774315436474088,a7Count,a7Rec,(fun _ _ => 0),a7Loc⟩
def a7Domains : Catalog := [(repeatWord 4294967295, 7)]
def a8Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x9ce7f75fab5570e, 0xfbb3ee8bf0bbb4d, 0x86edffce])
  | 1 => BitVec.ofNat 152 (big [0xe36fcf33f6a4ab9, 0xf679f1b61f665e6, 0x5fdc7733])
  | 2 => BitVec.ofNat 152 (big [0x5f9ceda60d8b4f3, 0xadf7ffddeb757b2, 0xff93127a])
  | 3 => BitVec.ofNat 152 (big [0x78587ae8d4fed44, 0xe7ddb7fe57db959, 0x626fabcf])
  | 4 => BitVec.ofNat 152 (big [0xb87c0bf0513ba5d, 0x8a7f07fb95e9632, 0xa1eac6ff])
  | _ => 0

def a8Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xc0120120310302, 0x4081646300a0041, 0x11080000])
  | 1 => BitVec.ofNat 152 (big [0xc24e4e013404889, 0xa12401000406c00, 0x4069402])
  | 2 => BitVec.ofNat 152 (big [0x118091200889470, 0x89080ab11112, 0x80202ac1])
  | 3 => BitVec.ofNat 152 (big [0x18a52e8d4e6444, 0x9d58028c5045900, 0x8253b590])
  | 4 => BitVec.ofNat 152 (big [0x3e750909013ba1d, 0x4e95587a3968221, 0xda5031b])
  | _ => 0

def a8Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a8Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (18754+i*5) 5
  | _ => 0

def a8Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a8Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 18760 1 18762 1 18759 1 i
  | _ => []

def a8 : Atlas := ⟨7,rawDecor 31 a8Pos a8Neg,repeatWord 18368189366660557544,a8Count,a8Rec,(fun _ _ => 0),a8Loc⟩
def a8Domains : Catalog := [(repeatWord 18446462603027742720, 7)]
def a9Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xd9da3f3aabe80be, 0xd39faff6873cbfe, 0xddddaffe])
  | 2 => BitVec.ofNat 152 (big [0x61e9b7d5bd30e55, 0xe62fbcf53aeaf51, 0x648afdd5])
  | 3 => BitVec.ofNat 152 (big [0xe67e7267560f72c, 0xfdde63cbddd521e, 0xf330675a])
  | 4 => BitVec.ofNat 152 (big [0x96eb535fb8556b9, 0xb368174b872088, 0xf2e17492])
  | 5 => BitVec.ofNat 152 (big [0xc1da32249b2863c, 0x4112a4b21e28a0a, 0xc0108f00])
  | _ => 0

def a9Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x50200aa1080b2, 0x2062000004868, 0x6800003])
  | 2 => BitVec.ofNat 152 (big [0x2983c40c30e04, 0xe59004042a8312, 0xa1002724])
  | 3 => BitVec.ofNat 152 (big [0x602ad021160640c, 0x958080c809016, 0x49032840])
  | 4 => BitVec.ofNat 152 (big [0x9cd013f378552b9, 0x1da6badeb251c20, 0x96058114])
  | 5 => BitVec.ofNat 152 (big [0xf5fffbefbf3eebe, 0x6efff2eefeadb7f, 0xffefbf6f])
  | _ => 0

def a9Count (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | _ => 0

def a9Rec (k i : Nat) : Nat :=
  match k with
  | 7 => field storageWord (18763+i*5) 5
  | _ => 0

def a9Loc (k tag : Nat) : Nat :=
  match k with
  | 7 => 0
  | _ => 0

def a9Hints (k i : Nat) : List Nat :=
  match k with
  | 7 => hintsAt storageWord 18769 1 18771 1 18768 1 i
  | _ => []

def a9 : Atlas := ⟨7,rawDecor 62 a9Pos a9Neg,repeatWord 18212782022386843644,a9Count,a9Rec,(fun _ _ => 0),a9Loc⟩
def a9Domains : Catalog := [(repeatWord 18446462603027742720, 7)]
def a10Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x7ff7fddebeaef36, 0xb3bdfbbff44f7fa, 0xe7ffd6ff])
  | 1 => BitVec.ofNat 152 (big [0x9b8ddffbcd5f1eb, 0xdfd7cdda2fff905, 0xffeffbe0])
  | 3 => BitVec.ofNat 152 (big [0xee595fa57751ed9, 0x6ef3e66bdbf1ef7, 0xfd9c7f5f])
  | 4 => BitVec.ofNat 152 (big [0x88a76aeb38f846d, 0xd8ab75a4cb7aebb, 0xc849ee1d])
  | 5 => BitVec.ofNat 152 (big [0xa0ab3b3a53fd194, 0xf7cdf6fde8adc6c, 0x5346b764])
  | _ => 0

def a10Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x660908822a6820, 0x24010020a40a0c0, 0x48c8224])
  | 1 => BitVec.ofNat 152 (big [0xd98e0f528c191ca, 0xb38880803e4000, 0xa0002000])
  | 3 => BitVec.ofNat 152 (big [0xf01141211541619, 0x408470475051e06, 0x1610948])
  | 4 => BitVec.ofNat 152 (big [0x2d1f4a823878465, 0xa33a4de40e1cc3b, 0xd75147a1])
  | 5 => BitVec.ofNat 152 (big [0x20cfb828d3dc194, 0x1e871adcda35022, 0xf3c0180b])
  | _ => 0

def a10Count (k : Nat) : Nat :=
  match k with
  | 5 => 12
  | 6 => 6
  | 7 => 1
  | _ => 0

def a10Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (18772+i*27) 27
  | 6 => field storageWord (19917+i*16) 16
  | 7 => field storageWord (20638+i*5) 5
  | _ => 0

def a10Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 12 12 (field storageWord (19096+(tag % 12)*5) 5) tag
  | 6 => hashRow 6 2 (field storageWord (20013+(tag % 2)*3) 3) tag
  | 7 => 0
  | _ => 0

def a10Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 19639 6 19717 5 19156 21 i
  | 6 => hintsAt storageWord 20376 6 20418 5 20019 21 i
  | 7 => hintsAt storageWord 20671 3 20677 3 20643 4 i
  | _ => []

def a10 : Atlas := ⟨7,rawDecor 59 a10Pos a10Neg,repeatWord 17197820398952557192,a10Count,a10Rec,(fun _ _ => 0),a10Loc⟩
def a10Domains : Catalog := [(repeatWord 7378697629483820646, 6), (repeatWord 6172840429334713770, 6), (repeatWord 12297735558912431445, 6), (repeatWord 12297829381041378645, 6), (repeatWord 14714328930390887475, 6), (repeatWord 3689517697150995660, 6), (repeatWord 3689348817318890700, 6), (repeatWord 281470681808895, 5), (repeatWord 18446462603027742720, 5), (repeatWord 4294967295, 5), (repeatWord 18446744069414584320, 5)]
def a11Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x1fb3857ef7484ed, 0xd1db7d3fef4c8de, 0xbf1bafee])
  | 1 => BitVec.ofNat 152 (big [0xf8dbfe911a37516, 0x7b2ed3fad07bbab, 0x65f9f0bf])
  | 3 => BitVec.ofNat 152 (big [0x11d6aff3ce6b88, 0x75adb7e9fcbe785, 0xe8dc7e4d])
  | 4 => BitVec.ofNat 152 (big [0x4f662748f6b5a61, 0xaf59fe885a9f50b, 0x135cbdc2])
  | 5 => BitVec.ofNat 152 (big [0xa814ff9de6642d, 0xa182ac60684a08d, 0xee50e80e])
  | _ => 0

def a11Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x820000c000802c, 0xc000880, 0x400000c0])
  | 1 => BitVec.ofNat 152 (big [0x8390808a14402, 0x90105400002b108, 0x28043021])
  | 3 => BitVec.ofNat 152 (big [0x3184a703462b80, 0x84809303410460, 0x4da8314])
  | 4 => BitVec.ofNat 152 (big [0x63863c80d6b5241, 0x1f3962f3a0c113, 0x20acca21])
  | 5 => BitVec.ofNat 152 (big [0xcbaf9fdd9e7e62f, 0xb7d77f24ff6bd8d, 0x7cbff2fb])
  | _ => 0

def a11Count (k : Nat) : Nat :=
  match k with
  | 5 => 5
  | 6 => 3
  | 7 => 1
  | _ => 0

def a11Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (20698+i*27) 27
  | 6 => field storageWord (21000+i*16) 16
  | 7 => field storageWord (21452+i*5) 5
  | _ => 0

def a11Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => hashRow 5 3 (field storageWord (20833+(tag % 3)*3) 3) tag
  | 6 => hashRow 3 2 (field storageWord (21048+(tag % 2)*3) 3) tag
  | 7 => 0
  | _ => 0

def a11Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 20974 3 20992 2 20842 33 i
  | 6 => hintsAt storageWord 21348 5 21368 4 21054 21 i
  | 7 => hintsAt storageWord 21478 3 21484 3 21457 3 i
  | _ => []

def a11 : Atlas := ⟨7,rawDecor 59 a11Pos a11Neg,repeatWord 17197820399244472046,a11Count,a11Rec,(fun _ _ => 0),a11Loc⟩
def a11Domains : Catalog := [(repeatWord 6149008514797120170, 7), (repeatWord 18374687579166474495, 7), (repeatWord 281474976645120, 7), (repeatWord 3689348814741910323, 6), (repeatWord 6148914691236517205, 5), (repeatWord 71777214294589695, 5), (repeatWord 18446744069414584320, 5), (repeatWord 6172840429334713770, 5)]
def a12Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xcd66aee7ec467dd, 0xfc6eff7b79b7f76, 0x759f7fef])
  | 1 => BitVec.ofNat 152 (big [0x7ffb793bd3bbab2, 0x1fd995e48e498bd, 0xbee4fed2])
  | 2 => BitVec.ofNat 152 (big [0x72cff31c57dc42a, 0x3fbfbb32f3d4ced, 0xae9fb92])
  | 4 => BitVec.ofNat 152 (big [0xbc67ba92c9e38a, 0x13fd061053c19c6, 0x69a3b0b])
  | 5 => BitVec.ofNat 152 (big [0xa41fcbff2869b2e, 0xde9c6494142c3f7, 0xb4d614ab])
  | _ => 0

def a12Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x4008000804081, 0x20202800240, 0x2041000])
  | 1 => BitVec.ofNat 152 (big [0x4e222113123b210, 0x848804010049101, 0x4009cc08])
  | 2 => BitVec.ofNat 152 (big [0x309c920845c042a, 0x3914d282c1368a6, 0xa03020e7])
  | 4 => BitVec.ofNat 152 (big [0x2966fdf31c9f38b, 0x7e0b7064bbd8bc6, 0xc3ecd719])
  | 5 => BitVec.ofNat 152 (big [0x3813d27e2049b2e, 0x2d01ca1e1160136, 0xadf08106])
  | _ => 0

def a12Count (k : Nat) : Nat :=
  match k with
  | 3 => 2
  | 4 => 22
  | 5 => 50
  | 6 => 12
  | 7 => 1
  | _ => 0

def a12Rec (k i : Nat) : Nat :=
  match k with
  | 3 => field storageWord (21505+i*49) 49
  | 4 => field storageWord (21607+i*38) 38
  | 5 => field storageWord (22575+i*27) 27
  | 6 => field storageWord (25305+i*16) 16
  | 7 => field storageWord (26305+i*5) 5
  | _ => 0

def a12Loc (k tag : Nat) : Nat :=
  match k with
  | 3 => hashRow 2 2 (field storageWord (21603+(tag % 2)*2) 2) tag
  | 4 => hashRow 22 22 (field storageWord (22443+(tag % 22)*6) 6) tag
  | 5 => hashRow 50 50 (field storageWord (23925+(tag % 50)*7) 7) tag
  | 6 => hashRow 12 12 (field storageWord (25497+(tag % 12)*5) 5) tag
  | 7 => 0
  | _ => 0

def a12Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 24803 6 25109 4 24275 33 i
  | 6 => hintsAt storageWord 25977 6 26055 5 25557 21 i
  | 7 => hintsAt storageWord 26318 2 26322 1 26310 4 i
  | _ => []

def a12 : Atlas := ⟨7,rawDecor 55 a12Pos a12Neg,repeatWord 16927604859302636266,a12Count,a12Rec,(fun _ _ => 0),a12Loc⟩
def a12Domains : Catalog := [(repeatWord 1085102592571150095, 6), (repeatWord 18446462603027742720, 5), (repeatWord 4294967295, 5), (repeatWord 7378697629483820646, 5), (repeatWord 12297735558912431445, 5), (repeatWord 6148914692668172970, 5), (repeatWord 3689517697150995660, 5), (repeatWord 14757395256390660915, 5), (repeatWord 4294901760, 4)]
def a13Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x37339effd5e63f1, 0xef2bf7ff6ea6c9f, 0xfedbdddf])
  | 1 => BitVec.ofNat 152 (big [0xf9cd6b292e9be1e, 0x1bf64fb4f95f7fb, 0xbbf6e7e2])
  | 2 => BitVec.ofNat 152 (big [0x585c7e87e079ceb, 0xd8c88dfe9773b74, 0xe77c76af])
  | 3 => BitVec.ofNat 152 (big [0xaeaac3dabb05fa4, 0x7697f28fc0aff2d, 0xf9d5ae17])
  | 5 => BitVec.ofNat 152 (big [0xc6e945118b3643d, 0xb9bd1e68d61fcbe, 0xf868d6f1])
  | _ => 0

def a13Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x20104890a4050, 0x480600302220402, 0x108001])
  | 1 => BitVec.ofNat 152 (big [0x50050120060b20c, 0x12085c900239, 0xb4a45204])
  | 2 => BitVec.ofNat 152 (big [0xc48ce856050ca3, 0x9270114a104a044, 0x4a030c98])
  | 3 => BitVec.ofNat 152 (big [0xa600c2862901fa4, 0x83d1d04d19cf928, 0x8b6904ae])
  | 5 => BitVec.ofNat 152 (big [0x48c10f1eb36439, 0x4566c760f49fcd4, 0x29cd11b8])
  | _ => 0

def a13Count (k : Nat) : Nat :=
  match k with
  | 4 => 2
  | 5 => 4
  | 6 => 1
  | _ => 0

def a13Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (26324+i*27) 27
  | 5 => field storageWord (26382+i*16) 16
  | 6 => field storageWord (26547+i*5) 5
  | _ => 0

def a13Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 2 2 (field storageWord (26378+(tag % 2)*2) 2) tag
  | 5 => hashRow 4 8 (field storageWord (26446+(tag % 8)*3) 3) tag
  | 6 => 0
  | _ => 0

def a13Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 26485 4 26505 3 26470 3 i
  | 6 => hintsAt storageWord 26561 2 26565 2 26552 3 i
  | _ => []

def a13 : Atlas := ⟨6,rawDecor 47 a13Pos a13Neg,repeatWord 17215272259764677352,a13Count,a13Rec,(fun _ _ => 0),a13Loc⟩
def a13Domains : Catalog := [(repeatWord 1085102592571150095, 5), (repeatWord 4294967295, 5), (repeatWord 18446744069414584320, 5), (repeatWord 6172840429334713770, 5), (repeatWord 14714328930390887475, 5), (repeatWord 16711935, 4)]
def a14Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xfbbbfe7effd5bee, 0xffffbff7ebbbfef, 0xfffffbcb])
  | 2 => BitVec.ofNat 152 (big [0xdeef19fb472a7db, 0x86c76ecfbef7c90, 0x5bfb4fbf])
  | 3 => BitVec.ofNat 152 (big [0xfdd5fdc9b27f635, 0xf838efa857c737e, 0xf9b794f5])
  | 4 => BitVec.ofNat 152 (big [0x5ef6abe769aecb7, 0x579f571d75cc151, 0x6c5db77d])
  | 5 => BitVec.ofNat 152 (big [0xd36eb7cc3e8fd80, 0xe5e077f938280e5, 0xbf0c7731])
  | _ => 0

def a14Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x8002c0120cc1062, 0x620801314280482, 0x12000280])
  | 2 => BitVec.ofNat 152 (big [0x4a0909e80328798, 0x9c24d08e2c3d838, 0x2cbdc80d])
  | 3 => BitVec.ofNat 152 (big [0x5cc13689b23e205, 0x9102e00113632c, 0x894ec118])
  | 4 => BitVec.ofNat 152 (big [0x16bc8b646906cb7, 0x31c1040315c8646, 0xe7630960])
  | 5 => BitVec.ofNat 152 (big [0xd56f7270968fd80, 0xa7d1bc8252c865, 0x218d1dc7])
  | _ => 0

def a14Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a14Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (26571+i*5) 5
  | _ => 0

def a14Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a14Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 26577 1 26579 1 26576 1 i
  | _ => []

def a14 : Atlas := ⟨6,rawDecor 61 a14Pos a14Neg,repeatWord 18062436863899118240,a14Count,a14Rec,(fun _ _ => 0),a14Loc⟩
def a14Domains : Catalog := [(repeatWord 18446744069414584320, 6)]
def a15Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xfa18fe3b0c692d6, 0x197c9d6b6b34324, 0x24408832])
  | 2 => BitVec.ofNat 152 (big [0x5b7ad5aa5c122f2, 0x5cb7df6d616ec6c, 0x7dddfffb])
  | 3 => BitVec.ofNat 152 (big [0xe42c2ff587ed407, 0xe7edc1fb9e95b93, 0x9f26fe3c])
  | 4 => BitVec.ofNat 152 (big [0xf4a7b205342eb8c, 0xb7f2f99349156fc, 0xa5bba6a0])
  | 5 => BitVec.ofNat 152 (big [0xa2d94c90f0d9998, 0xdd1ae4bc8f153ff, 0x7dac8d6e])
  | _ => 0

def a15Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xfe1fae72ec69ad7, 0xae2eb38ef5dda2d, 0xda3cebbb])
  | 2 => BitVec.ofNat 152 (big [0x0])
  | 3 => BitVec.ofNat 152 (big [0x404008c01007, 0x880080004000a00, 0x40040201])
  | 4 => BitVec.ofNat 152 (big [0xd4333803112eb80, 0x25394009a0c708c, 0x16782176])
  | 5 => BitVec.ofNat 152 (big [0x3918688062d8898, 0x342612aab825179, 0x92139508])
  | _ => 0

def a15Count (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def a15Rec (k i : Nat) : Nat :=
  match k with
  | 6 => field storageWord (26580+i*5) 5
  | _ => 0

def a15Loc (k tag : Nat) : Nat :=
  match k with
  | 6 => 0
  | _ => 0

def a15Hints (k i : Nat) : List Nat :=
  match k with
  | 6 => hintsAt storageWord 26586 1 26588 1 26585 1 i
  | _ => []

def a15 : Atlas := ⟨6,rawDecor 62 a15Pos a15Neg,repeatWord 18443366309563528176,a15Count,a15Rec,(fun _ _ => 0),a15Loc⟩
def a15Domains : Catalog := [(repeatWord 1085102592571150095, 6)]
def a16Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xb2dfbb6bb9e2fd7, 0x6ff3fbdaee777df, 0xeff77df9])
  | 1 => BitVec.ofNat 152 (big [0xff2566fd573f06d, 0xdacf57757bd9dee, 0xb9cfb2f7])
  | 2 => BitVec.ofNat 152 (big [0x4fea5db6eeddea8, 0xfe3effbf1bcfaf9, 0x5bfebfff])
  | 4 => BitVec.ofNat 152 (big [0xd63ce204a3b53d2, 0x1f94359fa5ed417, 0x77e9d080])
  | 5 => BitVec.ofNat 152 (big [0x1299b4e6915173e, 0x6b0fefeb97a8766, 0xc6c9463c])
  | _ => 0

def a16Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x9042900890429d0, 0x2000048420100b, 0x2030424])
  | 1 => BitVec.ofNat 152 (big [0x44052091433800d, 0x900c50029f0164, 0x1c141090])
  | 2 => BitVec.ofNat 152 (big [0xaa841262c85620, 0xc0cc1ab0140a890, 0x40e02801])
  | 4 => BitVec.ofNat 152 (big [0x5a5c4316a3b53c2, 0x8fa90b374575524, 0x14e8e99])
  | 5 => BitVec.ofNat 152 (big [0x4206646b715163e, 0x8403a3ab86aaf62, 0x1ca0ab9e])
  | _ => 0

def a16Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a16Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (26589+i*5) 5
  | _ => 0

def a16Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a16Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 26595 1 26597 1 26594 1 i
  | _ => []

def a16 : Atlas := ⟨5,rawDecor 55 a16Pos a16Neg,repeatWord 16927598236463065320,a16Count,a16Rec,(fun _ _ => 0),a16Loc⟩
def a16Domains : Catalog := [(repeatWord 18446462603027742720, 5)]
def a17Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xb5727e5d88081ba, 0xfdf775671557e35, 0xe3ff7a5f])
  | 1 => BitVec.ofNat 152 (big [0xee96d1a435b64c5, 0xdf67ab9caaa39c3, 0x5ff997b1])
  | 2 => BitVec.ofNat 152 (big [0x58e9f152d3c5f24, 0x6fc8b21cfccc89b, 0xde787c6b])
  | 4 => BitVec.ofNat 152 (big [0x553f23a3536ba42, 0xf36c6e7efe691dc, 0xa6b6a10a])
  | 5 => BitVec.ofNat 152 (big [0x83eb33bc7c9aa2d, 0x3d1491dfe241a42, 0x6b42e3f6])
  | _ => 0

def a17Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x0])
  | 1 => BitVec.ofNat 152 (big [0x400002400040c1, 0x142020200cc83, 0xa0000000])
  | 2 => BitVec.ofNat 152 (big [0xa0179128981d24, 0x7420d130740010, 0x2269080])
  | 4 => BitVec.ofNat 152 (big [0x503a0289166a202, 0x502192848010120, 0x59194e0e])
  | 5 => BitVec.ofNat 152 (big [0x8be2350bde1aa2c, 0x2ba8d30e07b3140, 0x54b51208])
  | _ => 0

def a17Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a17Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (26598+i*5) 5
  | _ => 0

def a17Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a17Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 26604 1 26606 1 26603 1 i
  | _ => []

def a17 : Atlas := ⟨5,rawDecor 55 a17Pos a17Neg,repeatWord 18374386239965948650,a17Count,a17Rec,(fun _ _ => 0),a17Loc⟩
def a17Domains : Catalog := [(repeatWord 6148914691236517205, 5)]
def a18Pos : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0xeef93a8abb03c5a, 0xe5ffbda27e257eb, 0xf9caff6f])
  | 2 => BitVec.ofNat 152 (big [0x2ad6a00ef169e50, 0xa8847a00583475b, 0xc3cafa1c])
  | 3 => BitVec.ofNat 152 (big [0x99f6c36655ed381, 0x5edcdf5cb1dacb5, 0x5e3b3fd8])
  | 4 => BitVec.ofNat 152 (big [0x192fdcf7607c276, 0x5993f39b7816d53, 0x123d7c96])
  | 5 => BitVec.ofNat 152 (big [0x5a9de591e11abe4, 0x31c8f97fa6e7ca0, 0x2ae64c1a])
  | _ => 0

def a18Neg : Nat → Bits
  | 1 => BitVec.ofNat 152 (big [0x0])
  | 2 => BitVec.ofNat 152 (big [0x3edcf76f7179f51, 0x5ef5b0ebe5b54df, 0xeffe39af])
  | 3 => BitVec.ofNat 152 (big [0x10c022444141301, 0x44602008248048d, 0x1842884])
  | 4 => BitVec.ofNat 152 (big [0x82bd42a2c3c072, 0x101191049230902, 0xe4529072])
  | 5 => BitVec.ofNat 152 (big [0x385c6185831abc4, 0x8e87ec02e43f4a6, 0xa9377481])
  | _ => 0

def a18Count (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def a18Rec (k i : Nat) : Nat :=
  match k with
  | 5 => field storageWord (26607+i*5) 5
  | _ => 0

def a18Loc (k tag : Nat) : Nat :=
  match k with
  | 5 => 0
  | _ => 0

def a18Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 26613 1 26615 1 26612 1 i
  | _ => []

def a18 : Atlas := ⟨5,rawDecor 62 a18Pos a18Neg,repeatWord 18433180279222620108,a18Count,a18Rec,(fun _ _ => 0),a18Loc⟩
def a18Domains : Catalog := [(repeatWord 3689348814741910323, 5)]
def a19Pos : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0xdeba7875f8516c4, 0x86efebdd7597017, 0x8f1b31d9])
  | 1 => BitVec.ofNat 152 (big [0xe547c59137cc9ab, 0xfbb69c279e66a6c, 0x73e8cfa6])
  | 2 => BitVec.ofNat 152 (big [0x129d332e07ba878, 0x3f6930fce7a8de9, 0x70d6aebf])
  | 3 => BitVec.ofNat 152 (big [0x2940ae8ac4b7f97, 0x7950fd8b49ddf9a, 0x39b5dad8])
  | 4 => BitVec.ofNat 152 (big [0xbaed3cb4923533, 0x68c9d671e54958e, 0x973fdb10])
  | 5 => BitVec.ofNat 152 (big [0x63692d7b198654d, 0xa699cfa2ad03ff0, 0xfe3a060f])
  | _ => 0

def a19Neg : Nat → Bits
  | 0 => BitVec.ofNat 152 (big [0x4a040744040204, 0x80c808803010000, 0x3000])
  | 1 => BitVec.ofNat 152 (big [0xe14684813508188, 0x182200028440824, 0x30883a2])
  | 2 => BitVec.ofNat 152 (big [0x21933080292870, 0x2600306c4300051, 0x34c20c15])
  | 3 => BitVec.ofNat 152 (big [0x40a80a84b5c93, 0x4900d309088cf5a, 0x18350098])
  | 4 => BitVec.ofNat 152 (big [0x4eae53834923523, 0x60438673ef091aa, 0x8f10cb25])
  | 5 => BitVec.ofNat 152 (big [0xc1092d7b198654d, 0x6299ceca1d1b4f3, 0x7c7a230d])
  | _ => 0

def a19Count (k : Nat) : Nat :=
  match k with
  | 4 => 3
  | 5 => 139
  | 6 => 902
  | 7 => 1051
  | 8 => 272
  | 9 => 27
  | 10 => 1
  | _ => 0

def a19Rec (k i : Nat) : Nat :=
  match k with
  | 4 => field storageWord (26616+i*72) 72
  | 5 => field storageWord (26834+i*61) 61
  | 6 => field storageWord (38364+i*50) 50
  | 7 => field storageWord (138323+i*39) 39
  | 8 => field storageWord (312803+i*28) 28
  | 9 => field storageWord (369547+i*17) 17
  | 10 => field storageWord (373590+i*6) 6
  | _ => 0

def a19Loc (k tag : Nat) : Nat :=
  match k with
  | 4 => hashRow 3 2 (field storageWord (26832+(tag % 2)*1) 1) tag
  | 5 => hashRow 139 70 (field storageWord (35313+(tag % 70)*8) 8) tag
  | 6 => hashRow 902 902 (field storageWord (83464+(tag % 902)*11) 11) tag
  | 7 => hashRow 1051 526 (field storageWord (179312+(tag % 526)*12) 12) tag
  | 8 => hashRow 272 272 (field storageWord (320419+(tag % 272)*10) 10) tag
  | 9 => hashRow 27 14 (field storageWord (370006+(tag % 14)*6) 6) tag
  | 10 => 0
  | _ => 0

def a19Hints (k i : Nat) : List Nat :=
  match k with
  | 5 => hintsAt storageWord 37329 6 38169 5 35873 56 i
  | 6 => hintsAt storageWord 117914 11 127847 9 93386 56 i
  | 7 => hintsAt storageWord 240299 13 253975 11 185624 45 i
  | 8 => hintsAt storageWord 342081 12 345357 10 323139 33 i
  | 9 => hintsAt storageWord 371812 8 372036 7 370090 21 i
  | 10 => hintsAt storageWord 373612 3 373618 2 373596 4 i
  | _ => []

def a19 : Atlas := ⟨10,rawDecor 63 a19Pos a19Neg,repeatWord 18368756714660489960,a19Count,a19Rec,(fun _ _ => 0),a19Loc⟩
def a19Domains : Catalog := [(repeatWord 12297829381041378645, 9), (repeatWord 3689348817318890700, 9), (repeatWord 71777218556133120, 9), (repeatWord 18446462598732906495, 9), (repeatWord 18446462603027742720, 8), (repeatWord 4294967295, 8), (repeatWord 6148914692668172970, 8), (repeatWord 14757395256390660915, 8), (repeatWord 17361393124654452495, 8), (repeatWord 17361641477348724495, 8), (repeatWord 18374966855153418495, 8), (repeatWord 1085102592571150095, 8), (repeatWord 18446744069414584320, 8), (repeatWord 6172840429334713770, 8), (repeatWord 12297735558912431445, 8), (repeatWord 14714328930390887475, 8), (repeatWord 3689517697150995660, 8), (repeatWord 1085102596360827120, 8), (repeatWord 72056494543077120, 8), (repeatWord 6148914691236517205, 7), (repeatWord 3689348814741910323, 7), (repeatWord 281470681808895, 7), (repeatWord 4294901760, 7), (repeatWord 7378697629483820646, 7), (repeatWord 6149008514797120170, 7), (repeatWord 17298308644996116495, 7), (repeatWord 71777214294589695, 6), (repeatWord 18374966859414961920, 6), (repeatWord 3689348813882916864, 6), (repeatWord 6510615555426900570, 6), (repeatWord 6124988953138320640, 5), (repeatWord 1431655765, 5), (repeatWord 6148914689804861440, 5), (repeatWord 3689292520605548544, 5), (repeatWord 858993459, 5), (repeatWord 16557098929935, 5), (repeatWord 1085086035472220160, 5), (repeatWord 252645135, 5), (repeatWord 1085102592318504960, 5), (repeatWord 71776119077928960, 5), (repeatWord 71777214277877760, 5), (repeatWord 4278255360, 5), (repeatWord 65535, 5), (repeatWord 281470681743360, 5), (repeatWord 18446462598732840960, 5), (repeatWord 6148820867675914240, 4), (repeatWord 1095216660735, 4), (repeatWord 16711935, 4), (repeatWord 1426085120, 4), (repeatWord 1431633920, 4), (repeatWord 6148820866244280320, 4), (repeatWord 16557098926080, 4), (repeatWord 252641280, 4), (repeatWord 255, 4), (repeatWord 1095216660480, 4)]
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
theorem a1S4P0 : segment (checkRow a1 a1Domains a1Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1S4P1 : segment (checkRow a1 a1Domains a1Hints 4) 16 12 = true := by decide +kernel
theorem a1S4 (j : Nat) (hj : j < 28) : (checkRow a1 a1Domains a1Hints 4) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a1S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a1S4P1 j (by omega) (by omega)
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
theorem a2S4P0 : segment (checkRow a2 a2Domains a2Hints 4) 0 12 = true := by decide +kernel
theorem a2S4 (j : Nat) (hj : j < 12) : (checkRow a2 a2Domains a2Hints 4) j = true := by
  exact segmentRange a2S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2S5P0 : segment (checkRow a2 a2Domains a2Hints 5) 0 1 = true := by decide +kernel
theorem a2S5 (j : Nat) (hj : j < 1) : (checkRow a2 a2Domains a2Hints 5) j = true := by
  exact segmentRange a2S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Complete : Complete a2 a2Domains a2Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a2S4 j hj
  · exact a2S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3S4P0 : segment (checkRow a3 a3Domains a3Hints 4) 0 1 = true := by decide +kernel
theorem a3S4 (j : Nat) (hj : j < 1) : (checkRow a3 a3Domains a3Hints 4) j = true := by
  exact segmentRange a3S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Complete : Complete a3 a3Domains a3Hints := by
  intro k hk j hj
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a3S4 j hj
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
theorem a6S4P0 : segment (checkRow a6 a6Domains a6Hints 4) 0 7 = true := by decide +kernel
theorem a6S4 (j : Nat) (hj : j < 7) : (checkRow a6 a6Domains a6Hints 4) j = true := by
  exact segmentRange a6S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P0 : segment (checkRow a6 a6Domains a6Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P1 : segment (checkRow a6 a6Domains a6Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P2 : segment (checkRow a6 a6Domains a6Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P3 : segment (checkRow a6 a6Domains a6Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P4 : segment (checkRow a6 a6Domains a6Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S5P5 : segment (checkRow a6 a6Domains a6Hints 5) 80 8 = true := by decide +kernel
theorem a6S5 (j : Nat) (hj : j < 88) : (checkRow a6 a6Domains a6Hints 5) j = true := by
  by_cases bound : j < 48
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a6S5P0 j (by omega) (by omega)
    ·
      by_cases bound : j < 32
      ·
        exact segmentRange a6S5P1 j (by omega) (by omega)
      ·
        exact segmentRange a6S5P2 j (by omega) (by omega)
  ·
    by_cases bound : j < 64
    ·
      exact segmentRange a6S5P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a6S5P4 j (by omega) (by omega)
      ·
        exact segmentRange a6S5P5 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S6P0 : segment (checkRow a6 a6Domains a6Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S6P1 : segment (checkRow a6 a6Domains a6Hints 6) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S6P2 : segment (checkRow a6 a6Domains a6Hints 6) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S6P3 : segment (checkRow a6 a6Domains a6Hints 6) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S6P4 : segment (checkRow a6 a6Domains a6Hints 6) 64 7 = true := by decide +kernel
theorem a6S6 (j : Nat) (hj : j < 71) : (checkRow a6 a6Domains a6Hints 6) j = true := by
  by_cases bound : j < 32
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a6S6P0 j (by omega) (by omega)
    ·
      exact segmentRange a6S6P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 48
    ·
      exact segmentRange a6S6P2 j (by omega) (by omega)
    ·
      by_cases bound : j < 64
      ·
        exact segmentRange a6S6P3 j (by omega) (by omega)
      ·
        exact segmentRange a6S6P4 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S7P0 : segment (checkRow a6 a6Domains a6Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S7P1 : segment (checkRow a6 a6Domains a6Hints 7) 16 3 = true := by decide +kernel
theorem a6S7 (j : Nat) (hj : j < 19) : (checkRow a6 a6Domains a6Hints 7) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a6S7P0 j (by omega) (by omega)
  ·
    exact segmentRange a6S7P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6S8P0 : segment (checkRow a6 a6Domains a6Hints 8) 0 1 = true := by decide +kernel
theorem a6S8 (j : Nat) (hj : j < 1) : (checkRow a6 a6Domains a6Hints 8) j = true := by
  exact segmentRange a6S8P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Complete : Complete a6 a6Domains a6Hints := by
  intro k hk j hj
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a6S4 j hj
  · exact a6S5 j hj
  · exact a6S6 j hj
  · exact a6S7 j hj
  · exact a6S8 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7S7P0 : segment (checkRow a7 a7Domains a7Hints 7) 0 1 = true := by decide +kernel
theorem a7S7 (j : Nat) (hj : j < 1) : (checkRow a7 a7Domains a7Hints 7) j = true := by
  exact segmentRange a7S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Complete : Complete a7 a7Domains a7Hints := by
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
  · exact a7S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8S7P0 : segment (checkRow a8 a8Domains a8Hints 7) 0 1 = true := by decide +kernel
theorem a8S7 (j : Nat) (hj : j < 1) : (checkRow a8 a8Domains a8Hints 7) j = true := by
  exact segmentRange a8S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Complete : Complete a8 a8Domains a8Hints := by
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
  · exact a8S7 j hj
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
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a9S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S5P0 : segment (checkRow a10 a10Domains a10Hints 5) 0 12 = true := by decide +kernel
theorem a10S5 (j : Nat) (hj : j < 12) : (checkRow a10 a10Domains a10Hints 5) j = true := by
  exact segmentRange a10S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10S6P0 : segment (checkRow a10 a10Domains a10Hints 6) 0 6 = true := by decide +kernel
theorem a10S6 (j : Nat) (hj : j < 6) : (checkRow a10 a10Domains a10Hints 6) j = true := by
  exact segmentRange a10S6P0 j (by omega) (by omega)
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
  · exact a10S5 j hj
  · exact a10S6 j hj
  · exact a10S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S5P0 : segment (checkRow a11 a11Domains a11Hints 5) 0 5 = true := by decide +kernel
theorem a11S5 (j : Nat) (hj : j < 5) : (checkRow a11 a11Domains a11Hints 5) j = true := by
  exact segmentRange a11S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S6P0 : segment (checkRow a11 a11Domains a11Hints 6) 0 3 = true := by decide +kernel
theorem a11S6 (j : Nat) (hj : j < 3) : (checkRow a11 a11Domains a11Hints 6) j = true := by
  exact segmentRange a11S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11S7P0 : segment (checkRow a11 a11Domains a11Hints 7) 0 1 = true := by decide +kernel
theorem a11S7 (j : Nat) (hj : j < 1) : (checkRow a11 a11Domains a11Hints 7) j = true := by
  exact segmentRange a11S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Complete : Complete a11 a11Domains a11Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a11S5 j hj
  · exact a11S6 j hj
  · exact a11S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S3P0 : segment (checkRow a12 a12Domains a12Hints 3) 0 2 = true := by decide +kernel
theorem a12S3 (j : Nat) (hj : j < 2) : (checkRow a12 a12Domains a12Hints 3) j = true := by
  exact segmentRange a12S3P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S4P0 : segment (checkRow a12 a12Domains a12Hints 4) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S4P1 : segment (checkRow a12 a12Domains a12Hints 4) 16 6 = true := by decide +kernel
theorem a12S4 (j : Nat) (hj : j < 22) : (checkRow a12 a12Domains a12Hints 4) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a12S4P0 j (by omega) (by omega)
  ·
    exact segmentRange a12S4P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S5P0 : segment (checkRow a12 a12Domains a12Hints 5) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S5P1 : segment (checkRow a12 a12Domains a12Hints 5) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S5P2 : segment (checkRow a12 a12Domains a12Hints 5) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S5P3 : segment (checkRow a12 a12Domains a12Hints 5) 48 2 = true := by decide +kernel
theorem a12S5 (j : Nat) (hj : j < 50) : (checkRow a12 a12Domains a12Hints 5) j = true := by
  by_cases bound : j < 32
  ·
    by_cases bound : j < 16
    ·
      exact segmentRange a12S5P0 j (by omega) (by omega)
    ·
      exact segmentRange a12S5P1 j (by omega) (by omega)
  ·
    by_cases bound : j < 48
    ·
      exact segmentRange a12S5P2 j (by omega) (by omega)
    ·
      exact segmentRange a12S5P3 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S6P0 : segment (checkRow a12 a12Domains a12Hints 6) 0 12 = true := by decide +kernel
theorem a12S6 (j : Nat) (hj : j < 12) : (checkRow a12 a12Domains a12Hints 6) j = true := by
  exact segmentRange a12S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12S7P0 : segment (checkRow a12 a12Domains a12Hints 7) 0 1 = true := by decide +kernel
theorem a12S7 (j : Nat) (hj : j < 1) : (checkRow a12 a12Domains a12Hints 7) j = true := by
  exact segmentRange a12S7P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Complete : Complete a12 a12Domains a12Hints := by
  intro k hk j hj
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a12S3 j hj
  · exact a12S4 j hj
  · exact a12S5 j hj
  · exact a12S6 j hj
  · exact a12S7 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S4P0 : segment (checkRow a13 a13Domains a13Hints 4) 0 2 = true := by decide +kernel
theorem a13S4 (j : Nat) (hj : j < 2) : (checkRow a13 a13Domains a13Hints 4) j = true := by
  exact segmentRange a13S4P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S5P0 : segment (checkRow a13 a13Domains a13Hints 5) 0 4 = true := by decide +kernel
theorem a13S5 (j : Nat) (hj : j < 4) : (checkRow a13 a13Domains a13Hints 5) j = true := by
  exact segmentRange a13S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13S6P0 : segment (checkRow a13 a13Domains a13Hints 6) 0 1 = true := by decide +kernel
theorem a13S6 (j : Nat) (hj : j < 1) : (checkRow a13 a13Domains a13Hints 6) j = true := by
  exact segmentRange a13S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Complete : Complete a13 a13Domains a13Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a13S4 j hj
  · exact a13S5 j hj
  · exact a13S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14S6P0 : segment (checkRow a14 a14Domains a14Hints 6) 0 1 = true := by decide +kernel
theorem a14S6 (j : Nat) (hj : j < 1) : (checkRow a14 a14Domains a14Hints 6) j = true := by
  exact segmentRange a14S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Complete : Complete a14 a14Domains a14Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a14S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15S6P0 : segment (checkRow a15 a15Domains a15Hints 6) 0 1 = true := by decide +kernel
theorem a15S6 (j : Nat) (hj : j < 1) : (checkRow a15 a15Domains a15Hints 6) j = true := by
  exact segmentRange a15S6P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Complete : Complete a15 a15Domains a15Hints := by
  intro k hk j hj
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a15S6 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16S5P0 : segment (checkRow a16 a16Domains a16Hints 5) 0 1 = true := by decide +kernel
theorem a16S5 (j : Nat) (hj : j < 1) : (checkRow a16 a16Domains a16Hints 5) j = true := by
  exact segmentRange a16S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Complete : Complete a16 a16Domains a16Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a16S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17S5P0 : segment (checkRow a17 a17Domains a17Hints 5) 0 1 = true := by decide +kernel
theorem a17S5 (j : Nat) (hj : j < 1) : (checkRow a17 a17Domains a17Hints 5) j = true := by
  exact segmentRange a17S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Complete : Complete a17 a17Domains a17Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a17S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18S5P0 : segment (checkRow a18 a18Domains a18Hints 5) 0 1 = true := by decide +kernel
theorem a18S5 (j : Nat) (hj : j < 1) : (checkRow a18 a18Domains a18Hints 5) j = true := by
  exact segmentRange a18S5P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Complete : Complete a18 a18Domains a18Hints := by
  intro k hk j hj
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a18S5 j hj
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S4P0 : segment (checkRow a19 a19Domains a19Hints 4) 0 3 = true := by decide +kernel
theorem a19S4 (j : Nat) (hj : j < 3) : (checkRow a19 a19Domains a19Hints 4) j = true := by
  exact segmentRange a19S4P0 j (by omega) (by omega)
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
theorem a19S5P3 : segment (checkRow a19 a19Domains a19Hints 5) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P4 : segment (checkRow a19 a19Domains a19Hints 5) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P5 : segment (checkRow a19 a19Domains a19Hints 5) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P6 : segment (checkRow a19 a19Domains a19Hints 5) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P7 : segment (checkRow a19 a19Domains a19Hints 5) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S5P8 : segment (checkRow a19 a19Domains a19Hints 5) 128 11 = true := by decide +kernel
theorem a19S5 (j : Nat) (hj : j < 139) : (checkRow a19 a19Domains a19Hints 5) j = true := by
  by_cases bound : j < 64
  ·
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
  ·
    by_cases bound : j < 96
    ·
      by_cases bound : j < 80
      ·
        exact segmentRange a19S5P4 j (by omega) (by omega)
      ·
        exact segmentRange a19S5P5 j (by omega) (by omega)
    ·
      by_cases bound : j < 112
      ·
        exact segmentRange a19S5P6 j (by omega) (by omega)
      ·
        by_cases bound : j < 128
        ·
          exact segmentRange a19S5P7 j (by omega) (by omega)
        ·
          exact segmentRange a19S5P8 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P0 : segment (checkRow a19 a19Domains a19Hints 6) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P1 : segment (checkRow a19 a19Domains a19Hints 6) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P2 : segment (checkRow a19 a19Domains a19Hints 6) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P3 : segment (checkRow a19 a19Domains a19Hints 6) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P4 : segment (checkRow a19 a19Domains a19Hints 6) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P5 : segment (checkRow a19 a19Domains a19Hints 6) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P6 : segment (checkRow a19 a19Domains a19Hints 6) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P7 : segment (checkRow a19 a19Domains a19Hints 6) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P8 : segment (checkRow a19 a19Domains a19Hints 6) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P9 : segment (checkRow a19 a19Domains a19Hints 6) 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P10 : segment (checkRow a19 a19Domains a19Hints 6) 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P11 : segment (checkRow a19 a19Domains a19Hints 6) 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P12 : segment (checkRow a19 a19Domains a19Hints 6) 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P13 : segment (checkRow a19 a19Domains a19Hints 6) 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P14 : segment (checkRow a19 a19Domains a19Hints 6) 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P15 : segment (checkRow a19 a19Domains a19Hints 6) 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P16 : segment (checkRow a19 a19Domains a19Hints 6) 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P17 : segment (checkRow a19 a19Domains a19Hints 6) 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P18 : segment (checkRow a19 a19Domains a19Hints 6) 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P19 : segment (checkRow a19 a19Domains a19Hints 6) 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P20 : segment (checkRow a19 a19Domains a19Hints 6) 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P21 : segment (checkRow a19 a19Domains a19Hints 6) 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P22 : segment (checkRow a19 a19Domains a19Hints 6) 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P23 : segment (checkRow a19 a19Domains a19Hints 6) 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P24 : segment (checkRow a19 a19Domains a19Hints 6) 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P25 : segment (checkRow a19 a19Domains a19Hints 6) 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P26 : segment (checkRow a19 a19Domains a19Hints 6) 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P27 : segment (checkRow a19 a19Domains a19Hints 6) 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P28 : segment (checkRow a19 a19Domains a19Hints 6) 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P29 : segment (checkRow a19 a19Domains a19Hints 6) 464 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P30 : segment (checkRow a19 a19Domains a19Hints 6) 480 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P31 : segment (checkRow a19 a19Domains a19Hints 6) 496 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P32 : segment (checkRow a19 a19Domains a19Hints 6) 512 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P33 : segment (checkRow a19 a19Domains a19Hints 6) 528 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P34 : segment (checkRow a19 a19Domains a19Hints 6) 544 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P35 : segment (checkRow a19 a19Domains a19Hints 6) 560 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P36 : segment (checkRow a19 a19Domains a19Hints 6) 576 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P37 : segment (checkRow a19 a19Domains a19Hints 6) 592 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P38 : segment (checkRow a19 a19Domains a19Hints 6) 608 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P39 : segment (checkRow a19 a19Domains a19Hints 6) 624 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P40 : segment (checkRow a19 a19Domains a19Hints 6) 640 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P41 : segment (checkRow a19 a19Domains a19Hints 6) 656 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P42 : segment (checkRow a19 a19Domains a19Hints 6) 672 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P43 : segment (checkRow a19 a19Domains a19Hints 6) 688 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P44 : segment (checkRow a19 a19Domains a19Hints 6) 704 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P45 : segment (checkRow a19 a19Domains a19Hints 6) 720 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P46 : segment (checkRow a19 a19Domains a19Hints 6) 736 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P47 : segment (checkRow a19 a19Domains a19Hints 6) 752 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P48 : segment (checkRow a19 a19Domains a19Hints 6) 768 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P49 : segment (checkRow a19 a19Domains a19Hints 6) 784 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P50 : segment (checkRow a19 a19Domains a19Hints 6) 800 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P51 : segment (checkRow a19 a19Domains a19Hints 6) 816 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P52 : segment (checkRow a19 a19Domains a19Hints 6) 832 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P53 : segment (checkRow a19 a19Domains a19Hints 6) 848 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P54 : segment (checkRow a19 a19Domains a19Hints 6) 864 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P55 : segment (checkRow a19 a19Domains a19Hints 6) 880 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S6P56 : segment (checkRow a19 a19Domains a19Hints 6) 896 6 = true := by decide +kernel
theorem a19S6 (j : Nat) (hj : j < 902) : (checkRow a19 a19Domains a19Hints 6) j = true := by
  by_cases bound : j < 448
  ·
    by_cases bound : j < 224
    ·
      by_cases bound : j < 112
      ·
        by_cases bound : j < 48
        ·
          by_cases bound : j < 16
          ·
            exact segmentRange a19S6P0 j (by omega) (by omega)
          ·
            by_cases bound : j < 32
            ·
              exact segmentRange a19S6P1 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P2 j (by omega) (by omega)
        ·
          by_cases bound : j < 80
          ·
            by_cases bound : j < 64
            ·
              exact segmentRange a19S6P3 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P4 j (by omega) (by omega)
          ·
            by_cases bound : j < 96
            ·
              exact segmentRange a19S6P5 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P6 j (by omega) (by omega)
      ·
        by_cases bound : j < 160
        ·
          by_cases bound : j < 128
          ·
            exact segmentRange a19S6P7 j (by omega) (by omega)
          ·
            by_cases bound : j < 144
            ·
              exact segmentRange a19S6P8 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P9 j (by omega) (by omega)
        ·
          by_cases bound : j < 192
          ·
            by_cases bound : j < 176
            ·
              exact segmentRange a19S6P10 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P11 j (by omega) (by omega)
          ·
            by_cases bound : j < 208
            ·
              exact segmentRange a19S6P12 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P13 j (by omega) (by omega)
    ·
      by_cases bound : j < 336
      ·
        by_cases bound : j < 272
        ·
          by_cases bound : j < 240
          ·
            exact segmentRange a19S6P14 j (by omega) (by omega)
          ·
            by_cases bound : j < 256
            ·
              exact segmentRange a19S6P15 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P16 j (by omega) (by omega)
        ·
          by_cases bound : j < 304
          ·
            by_cases bound : j < 288
            ·
              exact segmentRange a19S6P17 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P18 j (by omega) (by omega)
          ·
            by_cases bound : j < 320
            ·
              exact segmentRange a19S6P19 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P20 j (by omega) (by omega)
      ·
        by_cases bound : j < 384
        ·
          by_cases bound : j < 352
          ·
            exact segmentRange a19S6P21 j (by omega) (by omega)
          ·
            by_cases bound : j < 368
            ·
              exact segmentRange a19S6P22 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P23 j (by omega) (by omega)
        ·
          by_cases bound : j < 416
          ·
            by_cases bound : j < 400
            ·
              exact segmentRange a19S6P24 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P25 j (by omega) (by omega)
          ·
            by_cases bound : j < 432
            ·
              exact segmentRange a19S6P26 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P27 j (by omega) (by omega)
  ·
    by_cases bound : j < 672
    ·
      by_cases bound : j < 560
      ·
        by_cases bound : j < 496
        ·
          by_cases bound : j < 464
          ·
            exact segmentRange a19S6P28 j (by omega) (by omega)
          ·
            by_cases bound : j < 480
            ·
              exact segmentRange a19S6P29 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P30 j (by omega) (by omega)
        ·
          by_cases bound : j < 528
          ·
            by_cases bound : j < 512
            ·
              exact segmentRange a19S6P31 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P32 j (by omega) (by omega)
          ·
            by_cases bound : j < 544
            ·
              exact segmentRange a19S6P33 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P34 j (by omega) (by omega)
      ·
        by_cases bound : j < 608
        ·
          by_cases bound : j < 576
          ·
            exact segmentRange a19S6P35 j (by omega) (by omega)
          ·
            by_cases bound : j < 592
            ·
              exact segmentRange a19S6P36 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P37 j (by omega) (by omega)
        ·
          by_cases bound : j < 640
          ·
            by_cases bound : j < 624
            ·
              exact segmentRange a19S6P38 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P39 j (by omega) (by omega)
          ·
            by_cases bound : j < 656
            ·
              exact segmentRange a19S6P40 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P41 j (by omega) (by omega)
    ·
      by_cases bound : j < 784
      ·
        by_cases bound : j < 720
        ·
          by_cases bound : j < 688
          ·
            exact segmentRange a19S6P42 j (by omega) (by omega)
          ·
            by_cases bound : j < 704
            ·
              exact segmentRange a19S6P43 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P44 j (by omega) (by omega)
        ·
          by_cases bound : j < 752
          ·
            by_cases bound : j < 736
            ·
              exact segmentRange a19S6P45 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P46 j (by omega) (by omega)
          ·
            by_cases bound : j < 768
            ·
              exact segmentRange a19S6P47 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P48 j (by omega) (by omega)
      ·
        by_cases bound : j < 848
        ·
          by_cases bound : j < 816
          ·
            by_cases bound : j < 800
            ·
              exact segmentRange a19S6P49 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P50 j (by omega) (by omega)
          ·
            by_cases bound : j < 832
            ·
              exact segmentRange a19S6P51 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P52 j (by omega) (by omega)
        ·
          by_cases bound : j < 880
          ·
            by_cases bound : j < 864
            ·
              exact segmentRange a19S6P53 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P54 j (by omega) (by omega)
          ·
            by_cases bound : j < 896
            ·
              exact segmentRange a19S6P55 j (by omega) (by omega)
            ·
              exact segmentRange a19S6P56 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P0 : segment (checkRow a19 a19Domains a19Hints 7) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P1 : segment (checkRow a19 a19Domains a19Hints 7) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P2 : segment (checkRow a19 a19Domains a19Hints 7) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P3 : segment (checkRow a19 a19Domains a19Hints 7) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P4 : segment (checkRow a19 a19Domains a19Hints 7) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P5 : segment (checkRow a19 a19Domains a19Hints 7) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P6 : segment (checkRow a19 a19Domains a19Hints 7) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P7 : segment (checkRow a19 a19Domains a19Hints 7) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P8 : segment (checkRow a19 a19Domains a19Hints 7) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P9 : segment (checkRow a19 a19Domains a19Hints 7) 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P10 : segment (checkRow a19 a19Domains a19Hints 7) 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P11 : segment (checkRow a19 a19Domains a19Hints 7) 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P12 : segment (checkRow a19 a19Domains a19Hints 7) 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P13 : segment (checkRow a19 a19Domains a19Hints 7) 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P14 : segment (checkRow a19 a19Domains a19Hints 7) 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P15 : segment (checkRow a19 a19Domains a19Hints 7) 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P16 : segment (checkRow a19 a19Domains a19Hints 7) 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P17 : segment (checkRow a19 a19Domains a19Hints 7) 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P18 : segment (checkRow a19 a19Domains a19Hints 7) 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P19 : segment (checkRow a19 a19Domains a19Hints 7) 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P20 : segment (checkRow a19 a19Domains a19Hints 7) 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P21 : segment (checkRow a19 a19Domains a19Hints 7) 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P22 : segment (checkRow a19 a19Domains a19Hints 7) 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P23 : segment (checkRow a19 a19Domains a19Hints 7) 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P24 : segment (checkRow a19 a19Domains a19Hints 7) 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P25 : segment (checkRow a19 a19Domains a19Hints 7) 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P26 : segment (checkRow a19 a19Domains a19Hints 7) 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P27 : segment (checkRow a19 a19Domains a19Hints 7) 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P28 : segment (checkRow a19 a19Domains a19Hints 7) 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P29 : segment (checkRow a19 a19Domains a19Hints 7) 464 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P30 : segment (checkRow a19 a19Domains a19Hints 7) 480 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P31 : segment (checkRow a19 a19Domains a19Hints 7) 496 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P32 : segment (checkRow a19 a19Domains a19Hints 7) 512 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P33 : segment (checkRow a19 a19Domains a19Hints 7) 528 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P34 : segment (checkRow a19 a19Domains a19Hints 7) 544 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P35 : segment (checkRow a19 a19Domains a19Hints 7) 560 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P36 : segment (checkRow a19 a19Domains a19Hints 7) 576 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P37 : segment (checkRow a19 a19Domains a19Hints 7) 592 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P38 : segment (checkRow a19 a19Domains a19Hints 7) 608 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P39 : segment (checkRow a19 a19Domains a19Hints 7) 624 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P40 : segment (checkRow a19 a19Domains a19Hints 7) 640 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P41 : segment (checkRow a19 a19Domains a19Hints 7) 656 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P42 : segment (checkRow a19 a19Domains a19Hints 7) 672 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P43 : segment (checkRow a19 a19Domains a19Hints 7) 688 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P44 : segment (checkRow a19 a19Domains a19Hints 7) 704 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P45 : segment (checkRow a19 a19Domains a19Hints 7) 720 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P46 : segment (checkRow a19 a19Domains a19Hints 7) 736 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P47 : segment (checkRow a19 a19Domains a19Hints 7) 752 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P48 : segment (checkRow a19 a19Domains a19Hints 7) 768 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P49 : segment (checkRow a19 a19Domains a19Hints 7) 784 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P50 : segment (checkRow a19 a19Domains a19Hints 7) 800 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P51 : segment (checkRow a19 a19Domains a19Hints 7) 816 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P52 : segment (checkRow a19 a19Domains a19Hints 7) 832 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P53 : segment (checkRow a19 a19Domains a19Hints 7) 848 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P54 : segment (checkRow a19 a19Domains a19Hints 7) 864 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P55 : segment (checkRow a19 a19Domains a19Hints 7) 880 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P56 : segment (checkRow a19 a19Domains a19Hints 7) 896 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P57 : segment (checkRow a19 a19Domains a19Hints 7) 912 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P58 : segment (checkRow a19 a19Domains a19Hints 7) 928 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P59 : segment (checkRow a19 a19Domains a19Hints 7) 944 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P60 : segment (checkRow a19 a19Domains a19Hints 7) 960 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P61 : segment (checkRow a19 a19Domains a19Hints 7) 976 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P62 : segment (checkRow a19 a19Domains a19Hints 7) 992 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P63 : segment (checkRow a19 a19Domains a19Hints 7) 1008 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P64 : segment (checkRow a19 a19Domains a19Hints 7) 1024 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S7P65 : segment (checkRow a19 a19Domains a19Hints 7) 1040 11 = true := by decide +kernel
theorem a19S7 (j : Nat) (hj : j < 1051) : (checkRow a19 a19Domains a19Hints 7) j = true := by
  by_cases bound : j < 528
  ·
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
              exact segmentRange a19S7P0 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P1 j (by omega) (by omega)
          ·
            by_cases bound : j < 48
            ·
              exact segmentRange a19S7P2 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P3 j (by omega) (by omega)
        ·
          by_cases bound : j < 96
          ·
            by_cases bound : j < 80
            ·
              exact segmentRange a19S7P4 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P5 j (by omega) (by omega)
          ·
            by_cases bound : j < 112
            ·
              exact segmentRange a19S7P6 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P7 j (by omega) (by omega)
      ·
        by_cases bound : j < 192
        ·
          by_cases bound : j < 160
          ·
            by_cases bound : j < 144
            ·
              exact segmentRange a19S7P8 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P9 j (by omega) (by omega)
          ·
            by_cases bound : j < 176
            ·
              exact segmentRange a19S7P10 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P11 j (by omega) (by omega)
        ·
          by_cases bound : j < 224
          ·
            by_cases bound : j < 208
            ·
              exact segmentRange a19S7P12 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P13 j (by omega) (by omega)
          ·
            by_cases bound : j < 240
            ·
              exact segmentRange a19S7P14 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P15 j (by omega) (by omega)
    ·
      by_cases bound : j < 384
      ·
        by_cases bound : j < 320
        ·
          by_cases bound : j < 288
          ·
            by_cases bound : j < 272
            ·
              exact segmentRange a19S7P16 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P17 j (by omega) (by omega)
          ·
            by_cases bound : j < 304
            ·
              exact segmentRange a19S7P18 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P19 j (by omega) (by omega)
        ·
          by_cases bound : j < 352
          ·
            by_cases bound : j < 336
            ·
              exact segmentRange a19S7P20 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P21 j (by omega) (by omega)
          ·
            by_cases bound : j < 368
            ·
              exact segmentRange a19S7P22 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P23 j (by omega) (by omega)
      ·
        by_cases bound : j < 448
        ·
          by_cases bound : j < 416
          ·
            by_cases bound : j < 400
            ·
              exact segmentRange a19S7P24 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P25 j (by omega) (by omega)
          ·
            by_cases bound : j < 432
            ·
              exact segmentRange a19S7P26 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P27 j (by omega) (by omega)
        ·
          by_cases bound : j < 480
          ·
            by_cases bound : j < 464
            ·
              exact segmentRange a19S7P28 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P29 j (by omega) (by omega)
          ·
            by_cases bound : j < 496
            ·
              exact segmentRange a19S7P30 j (by omega) (by omega)
            ·
              by_cases bound : j < 512
              ·
                exact segmentRange a19S7P31 j (by omega) (by omega)
              ·
                exact segmentRange a19S7P32 j (by omega) (by omega)
  ·
    by_cases bound : j < 784
    ·
      by_cases bound : j < 656
      ·
        by_cases bound : j < 592
        ·
          by_cases bound : j < 560
          ·
            by_cases bound : j < 544
            ·
              exact segmentRange a19S7P33 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P34 j (by omega) (by omega)
          ·
            by_cases bound : j < 576
            ·
              exact segmentRange a19S7P35 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P36 j (by omega) (by omega)
        ·
          by_cases bound : j < 624
          ·
            by_cases bound : j < 608
            ·
              exact segmentRange a19S7P37 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P38 j (by omega) (by omega)
          ·
            by_cases bound : j < 640
            ·
              exact segmentRange a19S7P39 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P40 j (by omega) (by omega)
      ·
        by_cases bound : j < 720
        ·
          by_cases bound : j < 688
          ·
            by_cases bound : j < 672
            ·
              exact segmentRange a19S7P41 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P42 j (by omega) (by omega)
          ·
            by_cases bound : j < 704
            ·
              exact segmentRange a19S7P43 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P44 j (by omega) (by omega)
        ·
          by_cases bound : j < 752
          ·
            by_cases bound : j < 736
            ·
              exact segmentRange a19S7P45 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P46 j (by omega) (by omega)
          ·
            by_cases bound : j < 768
            ·
              exact segmentRange a19S7P47 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P48 j (by omega) (by omega)
    ·
      by_cases bound : j < 912
      ·
        by_cases bound : j < 848
        ·
          by_cases bound : j < 816
          ·
            by_cases bound : j < 800
            ·
              exact segmentRange a19S7P49 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P50 j (by omega) (by omega)
          ·
            by_cases bound : j < 832
            ·
              exact segmentRange a19S7P51 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P52 j (by omega) (by omega)
        ·
          by_cases bound : j < 880
          ·
            by_cases bound : j < 864
            ·
              exact segmentRange a19S7P53 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P54 j (by omega) (by omega)
          ·
            by_cases bound : j < 896
            ·
              exact segmentRange a19S7P55 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P56 j (by omega) (by omega)
      ·
        by_cases bound : j < 976
        ·
          by_cases bound : j < 944
          ·
            by_cases bound : j < 928
            ·
              exact segmentRange a19S7P57 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P58 j (by omega) (by omega)
          ·
            by_cases bound : j < 960
            ·
              exact segmentRange a19S7P59 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P60 j (by omega) (by omega)
        ·
          by_cases bound : j < 1008
          ·
            by_cases bound : j < 992
            ·
              exact segmentRange a19S7P61 j (by omega) (by omega)
            ·
              exact segmentRange a19S7P62 j (by omega) (by omega)
          ·
            by_cases bound : j < 1024
            ·
              exact segmentRange a19S7P63 j (by omega) (by omega)
            ·
              by_cases bound : j < 1040
              ·
                exact segmentRange a19S7P64 j (by omega) (by omega)
              ·
                exact segmentRange a19S7P65 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P0 : segment (checkRow a19 a19Domains a19Hints 8) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P1 : segment (checkRow a19 a19Domains a19Hints 8) 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P2 : segment (checkRow a19 a19Domains a19Hints 8) 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P3 : segment (checkRow a19 a19Domains a19Hints 8) 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P4 : segment (checkRow a19 a19Domains a19Hints 8) 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P5 : segment (checkRow a19 a19Domains a19Hints 8) 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P6 : segment (checkRow a19 a19Domains a19Hints 8) 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P7 : segment (checkRow a19 a19Domains a19Hints 8) 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P8 : segment (checkRow a19 a19Domains a19Hints 8) 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P9 : segment (checkRow a19 a19Domains a19Hints 8) 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P10 : segment (checkRow a19 a19Domains a19Hints 8) 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P11 : segment (checkRow a19 a19Domains a19Hints 8) 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P12 : segment (checkRow a19 a19Domains a19Hints 8) 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P13 : segment (checkRow a19 a19Domains a19Hints 8) 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P14 : segment (checkRow a19 a19Domains a19Hints 8) 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P15 : segment (checkRow a19 a19Domains a19Hints 8) 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S8P16 : segment (checkRow a19 a19Domains a19Hints 8) 256 16 = true := by decide +kernel
theorem a19S8 (j : Nat) (hj : j < 272) : (checkRow a19 a19Domains a19Hints 8) j = true := by
  by_cases bound : j < 128
  ·
    by_cases bound : j < 64
    ·
      by_cases bound : j < 32
      ·
        by_cases bound : j < 16
        ·
          exact segmentRange a19S8P0 j (by omega) (by omega)
        ·
          exact segmentRange a19S8P1 j (by omega) (by omega)
      ·
        by_cases bound : j < 48
        ·
          exact segmentRange a19S8P2 j (by omega) (by omega)
        ·
          exact segmentRange a19S8P3 j (by omega) (by omega)
    ·
      by_cases bound : j < 96
      ·
        by_cases bound : j < 80
        ·
          exact segmentRange a19S8P4 j (by omega) (by omega)
        ·
          exact segmentRange a19S8P5 j (by omega) (by omega)
      ·
        by_cases bound : j < 112
        ·
          exact segmentRange a19S8P6 j (by omega) (by omega)
        ·
          exact segmentRange a19S8P7 j (by omega) (by omega)
  ·
    by_cases bound : j < 192
    ·
      by_cases bound : j < 160
      ·
        by_cases bound : j < 144
        ·
          exact segmentRange a19S8P8 j (by omega) (by omega)
        ·
          exact segmentRange a19S8P9 j (by omega) (by omega)
      ·
        by_cases bound : j < 176
        ·
          exact segmentRange a19S8P10 j (by omega) (by omega)
        ·
          exact segmentRange a19S8P11 j (by omega) (by omega)
    ·
      by_cases bound : j < 224
      ·
        by_cases bound : j < 208
        ·
          exact segmentRange a19S8P12 j (by omega) (by omega)
        ·
          exact segmentRange a19S8P13 j (by omega) (by omega)
      ·
        by_cases bound : j < 240
        ·
          exact segmentRange a19S8P14 j (by omega) (by omega)
        ·
          by_cases bound : j < 256
          ·
            exact segmentRange a19S8P15 j (by omega) (by omega)
          ·
            exact segmentRange a19S8P16 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S9P0 : segment (checkRow a19 a19Domains a19Hints 9) 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S9P1 : segment (checkRow a19 a19Domains a19Hints 9) 16 11 = true := by decide +kernel
theorem a19S9 (j : Nat) (hj : j < 27) : (checkRow a19 a19Domains a19Hints 9) j = true := by
  by_cases bound : j < 16
  ·
    exact segmentRange a19S9P0 j (by omega) (by omega)
  ·
    exact segmentRange a19S9P1 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19S10P0 : segment (checkRow a19 a19Domains a19Hints 10) 0 1 = true := by decide +kernel
theorem a19S10 (j : Nat) (hj : j < 1) : (checkRow a19 a19Domains a19Hints 10) j = true := by
  exact segmentRange a19S10P0 j (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19Complete : Complete a19 a19Domains a19Hints := by
  intro k hk j hj
  change k ≤ 10 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact False.elim (Nat.not_lt_zero _ hj)
  · exact a19S4 j hj
  · exact a19S5 j hj
  · exact a19S6 j hj
  · exact a19S7 j hj
  · exact a19S8 j hj
  · exact a19S9 j hj
  · exact a19S10 j hj
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
theorem a1D0 : Slice true (roots a1) (target a1) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 67, flipInput 3] ++ fixRows 4 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D1 : Slice true (roots a1) (target a1) (repeatWord 18374966859414961920) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 67] ++ fixRows 0 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D2 : Slice true (roots a1) (target a1) (repeatWord 281470681808895) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, flipInput 3] ++ fixRows 16 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1D3 : Slice true (roots a1) (target a1) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 84, flipInput 2] ++ fixRows 0 32)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a1Bound : Lower true (roots a1) (target a1) 7 := by
  have ready : Ready a1 a1Domains (asRow a1Pos) (asRow a1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a1D0 (safeCons a1D1 (safeCons a1D2 (safeCons a1D3 (safeNil a1))))
  exact frozen ready a1Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2D0 : Slice true (roots a2) (target a2) (repeatWord 7378697629483820646) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 1] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2D1 : Slice true (roots a2) (target a2) (repeatWord 6149008514797120170) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2D2 : Slice true (roots a2) (target a2) (repeatWord 12297829381041378645) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 1, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2D3 : Slice true (roots a2) (target a2) (repeatWord 14757226376558555955) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67] ++ fixRows 0 0 ++ identifyRows 1 4 false)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2D4 : Slice true (roots a2) (target a2) (repeatWord 3689348817318890700) 4 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2D5 : Slice true (roots a2) (target a2) (repeatWord 281474976645120) 4 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 4 5 true)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a2Bound : Lower true (roots a2) (target a2) 6 := by
  have ready : Ready a2 a2Domains (asRow a2Pos) (asRow a2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a2D0 (safeCons a2D1 (safeCons a2D2 (safeCons a2D3 (safeCons a2D4 (safeCons a2D5 (safeNil a2))))))
  exact frozen ready a2Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 16, 18), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3D0 : Slice true (roots a3) (target a3) (repeatWord 1085102592571150095) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, swapRows 67, flipInput 4] ++ fixRows 4 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a3Bound : Lower true (roots a3) (target a3) 5 := by
  have ready : Ready a3 a3Domains (asRow a3Pos) (asRow a3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a3D0 (safeNil a3)
  exact frozen ready a3Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18), (inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 0, 16), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4D0 : Slice true (roots a4) (target a4) (repeatWord 71777214294589695) 4 :=
  signedSlice (ms := ([swapRows 33] ++ fixRows 8 0)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a4Bound : Lower true (roots a4) (target a4) 5 := by
  have ready : Ready a4 a4Domains (asRow a4Pos) (asRow a4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a4D0 (safeNil a4)
  exact frozen ready a4Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 33, 41), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5D0 : Slice true (roots a5) (target a5) (repeatWord 18446744069414584320) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 84, flipInput 3] ++ fixRows 0 32)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a5Bound : Lower true (roots a5) (target a5) 5 := by
  have ready : Ready a5 a5Domains (asRow a5Pos) (asRow a5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a5D0 (safeNil a5)
  exact frozen ready a5Complete (by decide +kernel) (by decide) [(inputs.getD 2 zero, 40, 44), (inputs.getD 3 zero, 32, 40), (inputs.getD 4 zero, 32, 48), (inputs.getD 5 zero, 0, 32)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D0 : Slice true (roots a6) (target a6) (repeatWord 6149008514797120170) 7 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D1 : Slice true (roots a6) (target a6) (repeatWord 12297829381041378645) 7 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D2 : Slice true (roots a6) (target a6) (repeatWord 281474976645120) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 67, flipInput 1] ++ fixRows 0 0 ++ identifyRows 4 5 true)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D3 : Slice true (roots a6) (target a6) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([swapRows 33] ++ fixRows 2 0)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D4 : Slice true (roots a6) (target a6) (repeatWord 1085102592571150095) 6 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D5 : Slice true (roots a6) (target a6) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 82, swapRows 84, flipInput 1, flipInput 4, flipInput 5] ++ fixRows 1 0)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D6 : Slice true (roots a6) (target a6) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, flipInput 2, flipInput 5] ++ fixRows 16 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D7 : Slice true (roots a6) (target a6) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 33, swapRows 50, swapRows 83, swapRows 84, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 0 16)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D8 : Slice true (roots a6) (target a6) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 33, swapRows 50, swapRows 83, flipInput 0, flipInput 1] ++ fixRows 32 0)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D9 : Slice true (roots a6) (target a6) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, swapRows 84, flipInput 2] ++ fixRows 0 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D10 : Slice true (roots a6) (target a6) (repeatWord 7378697629483820646) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, swapRows 84, flipInput 2, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D11 : Slice true (roots a6) (target a6) (repeatWord 6510615555426900570) 5 :=
  signedSlice (ms := ([swapRows 81, swapRows 83, swapRows 84, flipInput 1, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D12 : Slice true (roots a6) (target a6) (repeatWord 6148820867675914240) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33] ++ fixRows 1 16)) (base := roots a0) (G := (target a0)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a0Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D13 : Slice true (roots a6) (target a6) (repeatWord 1431655765) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 33 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6D14 : Slice true (roots a6) (target a6) (repeatWord 281470681743360) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 16 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a6Bound : Lower true (roots a6) (target a6) 9 := by
  have ready : Ready a6 a6Domains (asRow a6Pos) (asRow a6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a6D0 (safeCons a6D1 (safeCons a6D2 (safeCons a6D3 (safeCons a6D4 (safeCons a6D5 (safeCons a6D6 (safeCons a6D7 (safeCons a6D8 (safeCons a6D9 (safeCons a6D10 (safeCons a6D11 (safeCons a6D12 (safeCons a6D13 (safeCons a6D14 (safeNil a6)))))))))))))))
  exact frozen ready a6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7D0 : Slice true (roots a7) (target a7) (repeatWord 4294967295) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 83, flipInput 1, flipInput 3] ++ fixRows 32 0)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a7Bound : Lower true (roots a7) (target a7) 8 := by
  have ready : Ready a7 a7Domains (asRow a7Pos) (asRow a7Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a7D0 (safeNil a7)
  exact frozen ready a7Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8D0 : Slice true (roots a8) (target a8) (repeatWord 18446462603027742720) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 83, flipInput 1, flipInput 3] ++ fixRows 0 16)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a8Bound : Lower true (roots a8) (target a8) 8 := by
  have ready : Ready a8 a8Domains (asRow a8Pos) (asRow a8Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a8D0 (safeNil a8)
  exact frozen ready a8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9D0 : Slice true (roots a9) (target a9) (repeatWord 18446462603027742720) 7 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67, flipInput 2] ++ fixRows 0 16)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a9Bound : Lower true (roots a9) (target a9) 8 := by
  have ready : Ready a9 a9Domains (asRow a9Pos) (asRow a9Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a9D0 (safeNil a9)
  exact frozen ready a9Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 44, 60), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D0 : Slice true (roots a10) (target a10) (repeatWord 7378697629483820646) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 50, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D1 : Slice true (roots a10) (target a10) (repeatWord 6172840429334713770) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 50, flipInput 1, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D2 : Slice true (roots a10) (target a10) (repeatWord 12297735558912431445) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 50, swapRows 67, flipInput 1, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D3 : Slice true (roots a10) (target a10) (repeatWord 12297829381041378645) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 50, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D4 : Slice true (roots a10) (target a10) (repeatWord 14714328930390887475) 6 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 50, flipInput 0, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D5 : Slice true (roots a10) (target a10) (repeatWord 3689517697150995660) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, flipInput 0, flipInput 3] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D6 : Slice true (roots a10) (target a10) (repeatWord 3689348817318890700) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 50] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D7 : Slice true (roots a10) (target a10) (repeatWord 281470681808895) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 16 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D8 : Slice true (roots a10) (target a10) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, flipInput 3] ++ fixRows 0 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D9 : Slice true (roots a10) (target a10) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, swapRows 84, flipInput 0, flipInput 1, flipInput 4] ++ fixRows 32 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10D10 : Slice true (roots a10) (target a10) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a10Bound : Lower true (roots a10) (target a10) 8 := by
  have ready : Ready a10 a10Domains (asRow a10Pos) (asRow a10Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a10D0 (safeCons a10D1 (safeCons a10D2 (safeCons a10D3 (safeCons a10D4 (safeCons a10D5 (safeCons a10D6 (safeCons a10D7 (safeCons a10D8 (safeCons a10D9 (safeCons a10D10 (safeNil a10)))))))))))
  exact frozen ready a10Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D0 : Slice true (roots a11) (target a11) (repeatWord 6149008514797120170) 7 :=
  signedSlice (ms := ([swapRows 33, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 4 true)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D1 : Slice true (roots a11) (target a11) (repeatWord 18374687579166474495) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, flipInput 1] ++ fixRows 0 0 ++ identifyRows 3 4 false)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D2 : Slice true (roots a11) (target a11) (repeatWord 281474976645120) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 67, flipInput 1] ++ fixRows 0 0 ++ identifyRows 4 5 true)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D3 : Slice true (roots a11) (target a11) (repeatWord 3689348814741910323) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 50] ++ fixRows 2 0)) (base := roots a2) (G := (target a2)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a2Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D4 : Slice true (roots a11) (target a11) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 66, swapRows 67, flipInput 1, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 1 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D5 : Slice true (roots a11) (target a11) (repeatWord 71777214294589695) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 67] ++ fixRows 8 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D6 : Slice true (roots a11) (target a11) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 0 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11D7 : Slice true (roots a11) (target a11) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([swapRows 81, swapRows 82, swapRows 83, swapRows 84, flipInput 1, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a11Bound : Lower true (roots a11) (target a11) 8 := by
  have ready : Ready a11 a11Domains (asRow a11Pos) (asRow a11Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a11D0 (safeCons a11D1 (safeCons a11D2 (safeCons a11D3 (safeCons a11D4 (safeCons a11D5 (safeCons a11D6 (safeCons a11D7 (safeNil a11))))))))
  exact frozen ready a11Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 16, 24), (inputs.getD 4 zero, 8, 24), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D0 : Slice true (roots a12) (target a12) (repeatWord 1085102592571150095) 6 :=
  signedSlice (ms := ([flipInput 0, flipInput 1] ++ fixRows 4 0)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D1 : Slice true (roots a12) (target a12) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, flipInput 2] ++ fixRows 0 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D2 : Slice true (roots a12) (target a12) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, swapRows 84, flipInput 2, flipInput 4] ++ fixRows 32 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D3 : Slice true (roots a12) (target a12) (repeatWord 7378697629483820646) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, swapRows 84, flipInput 2, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D4 : Slice true (roots a12) (target a12) (repeatWord 12297735558912431445) 5 :=
  signedSlice (ms := ([swapRows 84, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D5 : Slice true (roots a12) (target a12) (repeatWord 6148914692668172970) 5 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D6 : Slice true (roots a12) (target a12) (repeatWord 3689517697150995660) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 84, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D7 : Slice true (roots a12) (target a12) (repeatWord 14757395256390660915) 5 :=
  signedSlice (ms := ([swapRows 16, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 5 false)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12D8 : Slice true (roots a12) (target a12) (repeatWord 4294901760) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 32 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a12Bound : Lower true (roots a12) (target a12) 8 := by
  have ready : Ready a12 a12Domains (asRow a12Pos) (asRow a12Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a12D0 (safeCons a12D1 (safeCons a12D2 (safeCons a12D3 (safeCons a12D4 (safeCons a12D5 (safeCons a12D6 (safeCons a12D7 (safeCons a12D8 (safeNil a12)))))))))
  exact frozen ready a12Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D0 : Slice true (roots a13) (target a13) (repeatWord 1085102592571150095) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 4 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D1 : Slice true (roots a13) (target a13) (repeatWord 4294967295) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 84, flipInput 2] ++ fixRows 32 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D2 : Slice true (roots a13) (target a13) (repeatWord 18446744069414584320) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 81, swapRows 67, swapRows 84, flipInput 1, flipInput 3] ++ fixRows 0 32)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D3 : Slice true (roots a13) (target a13) (repeatWord 6172840429334713770) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 83] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D4 : Slice true (roots a13) (target a13) (repeatWord 14714328930390887475) 5 :=
  signedSlice (ms := ([swapRows 32, swapRows 82, swapRows 83, flipInput 2] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13D5 : Slice true (roots a13) (target a13) (repeatWord 16711935) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 40 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a13Bound : Lower true (roots a13) (target a13) 7 := by
  have ready : Ready a13 a13Domains (asRow a13Pos) (asRow a13Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a13D0 (safeCons a13D1 (safeCons a13D2 (safeCons a13D3 (safeCons a13D4 (safeCons a13D5 (safeNil a13))))))
  exact frozen ready a13Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14D0 : Slice true (roots a14) (target a14) (repeatWord 18446744069414584320) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 67, swapRows 84, flipInput 0, flipInput 2, flipInput 3] ++ fixRows 0 32)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a14Bound : Lower true (roots a14) (target a14) 7 := by
  have ready : Ready a14 a14Domains (asRow a14Pos) (asRow a14Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a14D0 (safeNil a14)
  exact frozen ready a14Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15D0 : Slice true (roots a15) (target a15) (repeatWord 1085102592571150095) 6 :=
  signedSlice (ms := ([swapRows 32, swapRows 50, flipInput 3, flipInput 4] ++ fixRows 4 0)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a15Bound : Lower true (roots a15) (target a15) 7 := by
  have ready : Ready a15 a15Domains (asRow a15Pos) (asRow a15Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a15D0 (safeNil a15)
  exact frozen ready a15Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 0, 4), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16D0 : Slice true (roots a16) (target a16) (repeatWord 18446462603027742720) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, flipInput 2] ++ fixRows 0 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a16Bound : Lower true (roots a16) (target a16) 6 := by
  have ready : Ready a16 a16Domains (asRow a16Pos) (asRow a16Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a16D0 (safeNil a16)
  exact frozen ready a16Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 33, 49), (inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17D0 : Slice true (roots a17) (target a17) (repeatWord 6148914691236517205) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 1 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a17Bound : Lower true (roots a17) (target a17) 6 := by
  have ready : Ready a17 a17Domains (asRow a17Pos) (asRow a17Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a17D0 (safeNil a17)
  exact frozen ready a17Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18D0 : Slice true (roots a18) (target a18) (repeatWord 3689348814741910323) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 65, swapRows 67, swapRows 84, flipInput 3, flipInput 5] ++ fixRows 2 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a18Bound : Lower true (roots a18) (target a18) 6 := by
  have ready : Ready a18 a18Domains (asRow a18Pos) (asRow a18Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a18D0 (safeNil a18)
  exact frozen ready a18Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 0, 8), (inputs.getD 4 zero, 12, 28), (inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D0 : Slice true (roots a19) (target a19) (repeatWord 12297829381041378645) 9 :=
  signedSlice (ms := ([swapRows 48, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 5 false)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D1 : Slice true (roots a19) (target a19) (repeatWord 3689348817318890700) 9 :=
  signedSlice (ms := ([swapRows 49, swapRows 50, swapRows 67, swapRows 84, flipInput 4, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 5 true)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D2 : Slice true (roots a19) (target a19) (repeatWord 71777218556133120) 9 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 3 5 true)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D3 : Slice true (roots a19) (target a19) (repeatWord 18446462598732906495) 9 :=
  signedSlice (ms := ([swapRows 67, flipInput 5] ++ fixRows 0 0 ++ identifyRows 4 5 false)) (base := roots a6) (G := (target a6)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a6Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D4 : Slice true (roots a19) (target a19) (repeatWord 18446462603027742720) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 16)) (base := roots a7) (G := (target a7)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a7Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D5 : Slice true (roots a19) (target a19) (repeatWord 4294967295) 8 :=
  signedSlice (ms := ([] ++ fixRows 32 0)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D6 : Slice true (roots a19) (target a19) (repeatWord 6148914692668172970) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 5 true)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D7 : Slice true (roots a19) (target a19) (repeatWord 14757395256390660915) 8 :=
  signedSlice (ms := ([swapRows 16, flipInput 5] ++ fixRows 0 0 ++ identifyRows 1 5 false)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D8 : Slice true (roots a19) (target a19) (repeatWord 17361393124654452495) 8 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 84, flipInput 4] ++ fixRows 0 0 ++ identifyRows 2 4 false)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D9 : Slice true (roots a19) (target a19) (repeatWord 17361641477348724495) 8 :=
  signedSlice (ms := ([swapRows 82] ++ fixRows 0 0 ++ identifyRows 2 5 false)) (base := roots a8) (G := (target a8)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a8Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D10 : Slice true (roots a19) (target a19) (repeatWord 18374966855153418495) 8 :=
  signedSlice (ms := ([swapRows 16, swapRows 81, swapRows 83, flipInput 1] ++ fixRows 0 0 ++ identifyRows 3 5 false)) (base := roots a9) (G := (target a9)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a9Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D11 : Slice true (roots a19) (target a19) (repeatWord 1085102592571150095) 8 :=
  signedSlice (ms := ([] ++ fixRows 4 0)) (base := roots a10) (G := (target a10)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a10Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D12 : Slice true (roots a19) (target a19) (repeatWord 18446744069414584320) 8 :=
  signedSlice (ms := ([swapRows 50, swapRows 83, flipInput 3] ++ fixRows 0 32)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D13 : Slice true (roots a19) (target a19) (repeatWord 6172840429334713770) 8 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 84, flipInput 3, flipInput 4] ++ fixRows 0 0 ++ identifyRows 0 3 true)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D14 : Slice true (roots a19) (target a19) (repeatWord 12297735558912431445) 8 :=
  signedSlice (ms := ([swapRows 48, swapRows 67, flipInput 3] ++ fixRows 0 0 ++ identifyRows 0 4 false)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D15 : Slice true (roots a19) (target a19) (repeatWord 14714328930390887475) 8 :=
  signedSlice (ms := ([swapRows 16, swapRows 49, flipInput 4] ++ fixRows 0 0 ++ identifyRows 1 3 false)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D16 : Slice true (roots a19) (target a19) (repeatWord 3689517697150995660) 8 :=
  signedSlice (ms := ([swapRows 33, swapRows 84] ++ fixRows 0 0 ++ identifyRows 1 4 true)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D17 : Slice true (roots a19) (target a19) (repeatWord 1085102596360827120) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 2 5 true)) (base := roots a11) (G := (target a11)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a11Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D18 : Slice true (roots a19) (target a19) (repeatWord 72056494543077120) 8 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 3 4 true)) (base := roots a12) (G := (target a12)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a12Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D19 : Slice true (roots a19) (target a19) (repeatWord 6148914691236517205) 7 :=
  signedSlice (ms := ([swapRows 64, swapRows 65, swapRows 66, swapRows 67, flipInput 1, flipInput 2, flipInput 3, flipInput 4, flipInput 5] ++ fixRows 1 0)) (base := roots a13) (G := (neg (target a13))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a13Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D20 : Slice true (roots a19) (target a19) (repeatWord 3689348814741910323) 7 :=
  signedSlice (ms := ([] ++ fixRows 2 0)) (base := roots a14) (G := (target a14)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a14Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D21 : Slice true (roots a19) (target a19) (repeatWord 281470681808895) 7 :=
  signedSlice (ms := ([] ++ fixRows 16 0)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D22 : Slice true (roots a19) (target a19) (repeatWord 4294901760) 7 :=
  signedSlice (ms := ([swapRows 32, swapRows 49, swapRows 66, swapRows 83, flipInput 1, flipInput 3] ++ fixRows 32 16)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D23 : Slice true (roots a19) (target a19) (repeatWord 7378697629483820646) 7 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 1 true)) (base := roots a15) (G := (target a15)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a15Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D24 : Slice true (roots a19) (target a19) (repeatWord 6149008514797120170) 7 :=
  signedSlice (ms := ([swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 2] ++ fixRows 32 0 ++ identifyRows 0 4 true)) (base := roots a1) (G := (neg (target a1))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a1Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D25 : Slice true (roots a19) (target a19) (repeatWord 17298308644996116495) 7 :=
  signedSlice (ms := ([swapRows 16, swapRows 33, swapRows 66, swapRows 67] ++ fixRows 0 0 ++ identifyRows 2 3 false)) (base := roots a13) (G := (target a13)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a13Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D26 : Slice true (roots a19) (target a19) (repeatWord 71777214294589695) 6 :=
  signedSlice (ms := ([] ++ fixRows 8 0)) (base := roots a16) (G := (target a16)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a16Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D27 : Slice true (roots a19) (target a19) (repeatWord 18374966859414961920) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 8)) (base := roots a17) (G := (target a17)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a17Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D28 : Slice true (roots a19) (target a19) (repeatWord 3689348813882916864) 6 :=
  signedSlice (ms := ([swapRows 33, swapRows 67, swapRows 84, flipInput 0, flipInput 2, flipInput 3] ++ fixRows 2 32)) (base := roots a2) (G := (neg (target a2))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a2Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D29 : Slice true (roots a19) (target a19) (repeatWord 6510615555426900570) 6 :=
  signedSlice (ms := ([] ++ fixRows 0 0 ++ identifyRows 0 2 true)) (base := roots a18) (G := (target a18)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a18Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D30 : Slice true (roots a19) (target a19) (repeatWord 6124988953138320640) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 67, swapRows 84, flipInput 4] ++ fixRows 1 8)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D31 : Slice true (roots a19) (target a19) (repeatWord 1431655765) 5 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, flipInput 1, flipInput 3] ++ fixRows 33 0)) (base := roots a3) (G := (target a3)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a3Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D32 : Slice true (roots a19) (target a19) (repeatWord 6148914689804861440) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 83, swapRows 84, flipInput 1, flipInput 2, flipInput 4] ++ fixRows 1 32)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D33 : Slice true (roots a19) (target a19) (repeatWord 3689292520605548544) 5 :=
  signedSlice (ms := ([swapRows 83, flipInput 3] ++ fixRows 2 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D34 : Slice true (roots a19) (target a19) (repeatWord 858993459) 5 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 0, flipInput 2, flipInput 4] ++ fixRows 34 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D35 : Slice true (roots a19) (target a19) (repeatWord 16557098929935) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, flipInput 0, flipInput 1, flipInput 5] ++ fixRows 20 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D36 : Slice true (roots a19) (target a19) (repeatWord 1085086035472220160) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, flipInput 3] ++ fixRows 4 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D37 : Slice true (roots a19) (target a19) (repeatWord 252645135) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, swapRows 84, flipInput 0, flipInput 1, flipInput 4] ++ fixRows 36 0)) (base := roots a4) (G := (neg (target a4))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a4Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D38 : Slice true (roots a19) (target a19) (repeatWord 1085102592318504960) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 83, swapRows 84, flipInput 3] ++ fixRows 4 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D39 : Slice true (roots a19) (target a19) (repeatWord 71776119077928960) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, flipInput 2] ++ fixRows 8 16)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D40 : Slice true (roots a19) (target a19) (repeatWord 71777214277877760) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 83, swapRows 84, flipInput 2] ++ fixRows 8 32)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D41 : Slice true (roots a19) (target a19) (repeatWord 4278255360) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 33, swapRows 50, swapRows 83, flipInput 0, flipInput 1] ++ fixRows 32 8)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D42 : Slice true (roots a19) (target a19) (repeatWord 65535) 5 :=
  signedSlice (ms := ([swapRows 33, swapRows 82, swapRows 84, flipInput 2] ++ fixRows 48 0)) (base := roots a4) (G := (target a4)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) a4Bound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D43 : Slice true (roots a19) (target a19) (repeatWord 281470681743360) 5 :=
  signedSlice (ms := ([swapRows 16, swapRows 81, swapRows 67, swapRows 84, flipInput 1, flipInput 3] ++ fixRows 16 32)) (base := roots a3) (G := (neg (target a3))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a3Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D44 : Slice true (roots a19) (target a19) (repeatWord 18446462598732840960) 5 :=
  signedSlice (ms := ([swapRows 80, swapRows 33, swapRows 50, swapRows 67, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 0 48)) (base := roots a5) (G := (neg (target a5))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a5Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D45 : Slice true (roots a19) (target a19) (repeatWord 6148820867675914240) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 33 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D46 : Slice true (roots a19) (target a19) (repeatWord 1095216660735) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 56 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D47 : Slice true (roots a19) (target a19) (repeatWord 16711935) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 56 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D48 : Slice true (roots a19) (target a19) (repeatWord 1426085120) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 33 8)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D49 : Slice true (roots a19) (target a19) (repeatWord 1431633920) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 33 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D50 : Slice true (roots a19) (target a19) (repeatWord 6148820866244280320) 4 :=
  signedSlice (ms := ([swapRows 32, swapRows 33, swapRows 83, swapRows 84, flipInput 1, flipInput 2] ++ fixRows 1 48)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D51 : Slice true (roots a19) (target a19) (repeatWord 16557098926080) 4 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 20 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D52 : Slice true (roots a19) (target a19) (repeatWord 252641280) 4 :=
  signedSlice (ms := ([swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 36 16)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D53 : Slice true (roots a19) (target a19) (repeatWord 255) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 56 0)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19D54 : Slice true (roots a19) (target a19) (repeatWord 1095216660480) 4 :=
  signedSlice (ms := ([swapRows 82, swapRows 83, swapRows 84, flipInput 0, flipInput 1] ++ fixRows 24 32)) (base := roots a0) (G := (neg (target a0))) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (lowerNeg a0Bound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a19Bound : Lower true (roots a19) (target a19) 11 := by
  have ready : Ready a19 a19Domains (asRow a19Pos) (asRow a19Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs
      decide +kernel
    · exact safeCons a19D0 (safeCons a19D1 (safeCons a19D2 (safeCons a19D3 (safeCons a19D4 (safeCons a19D5 (safeCons a19D6 (safeCons a19D7 (safeCons a19D8 (safeCons a19D9 (safeCons a19D10 (safeCons a19D11 (safeCons a19D12 (safeCons a19D13 (safeCons a19D14 (safeCons a19D15 (safeCons a19D16 (safeCons a19D17 (safeCons a19D18 (safeCons a19D19 (safeCons a19D20 (safeCons a19D21 (safeCons a19D22 (safeCons a19D23 (safeCons a19D24 (safeCons a19D25 (safeCons a19D26 (safeCons a19D27 (safeCons a19D28 (safeCons a19D29 (safeCons a19D30 (safeCons a19D31 (safeCons a19D32 (safeCons a19D33 (safeCons a19D34 (safeCons a19D35 (safeCons a19D36 (safeCons a19D37 (safeCons a19D38 (safeCons a19D39 (safeCons a19D40 (safeCons a19D41 (safeCons a19D42 (safeCons a19D43 (safeCons a19D44 (safeCons a19D45 (safeCons a19D46 (safeCons a19D47 (safeCons a19D48 (safeCons a19D49 (safeCons a19D50 (safeCons a19D51 (safeCons a19D52 (safeCons a19D53 (safeCons a19D54 (safeNil a19)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  exact frozen ready a19Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots := roots a19
def fullWord := target a19
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38979.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩, ⟨.or,[2,6]⟩, ⟨.and,[1,7]⟩, ⟨.or,[1,2]⟩, ⟨.or,[9,3]⟩, ⟨.and,[0,10]⟩, ⟨.or,[8,11]⟩, ⟨.and,[3,9]⟩, ⟨.and,[0,5]⟩, ⟨.or,[13,14]⟩, ⟨.and,[4,15]⟩, ⟨.or,[12,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38979
open PEqualNP.Outside.L_meta_38979 in
theorem PEqualNP.Outside.L_meta_38979 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := solve a19Bound

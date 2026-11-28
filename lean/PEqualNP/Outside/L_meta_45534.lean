import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45534.Model
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

private theorem observeNeg (w : Sig) : observe (neg w) = inv (observe w) := by
  funext r
  exact bit_neg r w

private theorem invTwice (w : Wire Row) : inv (inv w) = w := by
  funext r
  simp [inv]

private theorem signAvailable {bank : List (Wire Row)} {w : Wire Row} (h : Available true bank w) :
    Available true bank (inv w) := by
  rcases h with yes | ⟨b, rfl⟩ | ⟨_, no⟩
  · exact Or.inr (Or.inr ⟨rfl, by simpa only [invTwice] using yes⟩)
  · exact Or.inr (Or.inl ⟨!b, rfl⟩)
  · exact Or.inl no

def freeWordSigned (roots : List Sig) (w : Sig) := freeWord roots w || freeWord roots (neg w)

private theorem freeWordSigned_ok {roots w} (h : freeWordSigned roots w = true) :
    Available true (roots.map observe) (observe w) := by
  simp only [freeWordSigned, Bool.or_eq_true] at h
  rcases h with yes | no
  · exact freeWord_ok yes
  · have av : Available true (roots.map observe) (observe (neg w)) := freeWord_ok no
    simpa only [observeNeg, invTwice] using signAvailable av

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
    exact hL p bank reach (by simpa only [observeNeg, invTwice] using signAvailable available)

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

end PEqualNP.Outside.L_meta_45534.Model

namespace PEqualNP.Outside.L_meta_45534
open PEqualNP.Outside.L_meta_45534.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat) × List (Sig × Nat) × List Move

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

def cuts (g : Atlas) := g.2.2.2.2.2.2.2.1
def sliceDomain (g : Atlas) (j : Nat) : Sig := ((cuts g).getD j (one,0)).1
def sliceBound (g : Atlas) (j : Nat) : Nat := ((cuts g).getD j (one,0)).2

def projectChoices (raw : List Sig) (v bits : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let a := raw.getD (v &&& 15) zero
    let b := raw.getD ((v >>> 4) &&& 15) zero
    let choice := ((v >>> 8) &&& 3, a, b)
    let later := projectChoices (raw ++ [choiceVal choice]) (v >>> 10) (bits >>> 1) n
    if bits &&& 1 == 1 then choice :: later else later

def deadTest (g : Atlas) (ws : List Sig) (k i hint : Nat) : Bool :=
  let j := hint % 16 - 1
  let d := sliceDomain g j
  let cs := projectChoices (roots g) (record g k i) (hint >>> 4) (top g-k)
  (makePool true d (roots g) cs).any (fun pool => poolCut true d (sliceBound g j) k cs.length pool ws)

def mirrorSteps (g : Atlas) : List Move := g.2.2.2.2.2.2.2.2

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) (mirrorSteps g) then ws.map (movedWord (mirrorSteps g).reverse) else ws

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
    (if h != 0 then decide (h % 16 - 1 < (cuts g).length) && deadTest g vs k i h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 128 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      (tip g k i % 16 - 1 < (cuts g).length) → Slice true (roots g) (target g) (sliceDomain g (tip g k i % 16 - 1)) (sliceBound g (tip g k i % 16 - 1))

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

end PEqualNP.Outside.L_meta_45534

namespace PEqualNP.Outside.L_meta_45534
open PEqualNP.Outside.L_meta_45534.Model
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



def s0a0K3 : Nat → Nat
  | 0 => 0x24263d39b3e548190094a0c349c70442700a74e0c3a01a9c4274e2d3a344988a70428497309d3850c74f164e9c9274ea2600a180ac202d90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0

def s0a0K4 : Nat → Nat
  | 0 => 0xc06a0e73048aab0510b30c0cb840160a47a68a0c1a218c01900ca0fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0

def s0a0K5 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s0a0N (k : Nat) : Nat :=
  match k with
  | 3 => 39
  | 4 => 24
  | 5 => 1
  | _ => 0

def s0a0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0a0K3 (i*26) 26
  | 4 => packedAt s0a0K4 (i*15) 15
  | 5 => packedAt s0a0K5 (i*4) 4
  | _ => 0

def s0a0H (_k _i : Nat) : Nat := 0

def s0a0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0a0K3 (1068+((h/9+packedAt s0a0K3 (1014+(h % 9)*6) 6) % 54)*7) 7
  | 4 => packedAt s0a0K4 (390+((h/6+packedAt s0a0K4 (360+(h % 6)*5) 5) % 31)*6) 6
  | 5 => packedAt s0a0K5 (5+((h/1+packedAt s0a0K5 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a0Pos : Nat → Bits
  | 0 => 0xfffd6b5aefdfbf7ffeb5ad77efdfbfff
  | 1 => 0xaaa6d6b5da74e9d5536b5aed3a74eaa9
  | 2 => 0xd4cb9ce71cb972ea65ce738e5cb97532
  | 5 => 0x713ffffb122448389ffffd8912241c4
  | _ => 0

def s0a0Neg : Nat → Bits
  | 0 => 0x7e0000001c38703f0000000e1c381f8
  | 1 => 0xe800c631da3468f4006318ed1a347a00
  | 2 => 0xf00318c61c3870f8018c630e1c387c00
  | 5 => 0x3ffffe000000001fffff000000000
  | _ => 0

def s0a0Atlas : Atlas := ⟨5, rawDecor 39 s0a0Pos s0a0Neg, 0xeaeaeaeaa8a8a8a8, s0a0N, s0a0R, s0a0H, s0a0I, [], []⟩

def s0a1K2 : Nat → Nat
  | 0 => 0x42550e31
  | _ => 0

def s0a1K3 : Nat → Nat
  | 0 => 0x1535552405f31ec63d4c6e98d531
  | _ => 0

def s0a1K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s0a1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | 3 => 5
  | 4 => 1
  | _ => 0

def s0a1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a1K2 (i*26) 26
  | 3 => packedAt s0a1K3 (i*15) 15
  | 4 => packedAt s0a1K4 (i*4) 4
  | _ => 0

def s0a1H (_k _i : Nat) : Nat := 0

def s0a1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a1K2 (27+((h/1+packedAt s0a1K2 (26+(h % 1)*1) 1) % 2)*2) 2
  | 3 => packedAt s0a1K3 (79+((h/1+packedAt s0a1K3 (75+(h % 1)*4) 4) % 9)*4) 4
  | 4 => packedAt s0a1K4 (5+((h/1+packedAt s0a1K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a1Pos : Nat → Bits
  | 1 => 0x257f257f5555257f257f5555257f257f
  | 2 => 0x4bc94bc9f0f04bc94bc9f0f04bc94bc9
  | 3 => 0xfe92fe92aaaafe92fe92aaaafe92fe92
  | 5 => 0x90249024ffff90249024ffff90249024
  | _ => 0

def s0a1Neg : Nat → Bits
  | 1 => 0x3f003f0000003f003f0000003f003f
  | 2 => 0x3c003c0f0f003c003c0f0f003c003c0
  | 3 => 0xfc00fc000000fc00fc000000fc00fc00
  | 5 => 0xffff00000000ffff00000000
  | _ => 0

def s0a1Atlas : Atlas := ⟨4, rawDecor 46 s0a1Pos s0a1Neg, 0xffccffccfcc0fcc0, s0a1N, s0a1R, s0a1H, s0a1I, [], []⟩

def s0a2K2 : Nat → Nat
  | 0 => 0x62888808840a5418ca350f218d43082950420
  | _ => 0

def s0a2K3 : Nat → Nat
  | 0 => 0x6664266616366656037196d32de43b4877106c20
  | _ => 0

def s0a2K4 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def s0a2N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 6
  | 4 => 1
  | _ => 0

def s0a2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a2K2 (i*26) 26
  | 3 => packedAt s0a2K3 (i*15) 15
  | 4 => packedAt s0a2K4 (i*4) 4
  | _ => 0

def s0a2H (_k _i : Nat) : Nat := 0

def s0a2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a2K2 (108+((h/1+packedAt s0a2K2 (104+(h % 1)*4) 4) % 10)*4) 4
  | 3 => packedAt s0a2K3 (95+((h/1+packedAt s0a2K3 (90+(h % 1)*5) 5) % 17)*4) 4
  | 4 => packedAt s0a2K4 (5+((h/1+packedAt s0a2K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a2Pos : Nat → Bits
  | 0 => 0x5d7f5d7f55555d7f5d7f55555d7f5d7f
  | 2 => 0xf3c9f3c9aaaaf3c9f3c9aaaaf3c9f3c9
  | 3 => 0xfc12fc12f0f0fc12fc12f0f0fc12fc12
  | 5 => 0xa2a4a2a4ffffa2a4a2a4ffffa2a4a2a4
  | _ => 0

def s0a2Neg : Nat → Bits
  | 0 => 0x3f003f0000003f003f0000003f003f
  | 2 => 0xf3c0f3c00000f3c0f3c00000f3c0f3c0
  | 3 => 0xfc00fc00f0f0fc00fc00f0f0fc00fc00
  | 5 => 0xffff00000000ffff00000000
  | _ => 0

def s0a2Atlas : Atlas := ⟨4, rawDecor 45 s0a2Pos s0a2Neg, 0xfafafafaaaa0aaa0, s0a2N, s0a2R, s0a2H, s0a2I, [], []⟩

def s0a3K2 : Nat → Nat
  | 0 => 0x426320c020d030043808010
  | _ => 0

def s0a3K3 : Nat → Nat
  | 0 => 0x118b2b02333302f185c30dc41b083b087410
  | _ => 0

def s0a3K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s0a3N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | _ => 0

def s0a3R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a3K2 (i*26) 26
  | 3 => packedAt s0a3K3 (i*15) 15
  | 4 => packedAt s0a3K4 (i*4) 4
  | _ => 0

def s0a3H (_k _i : Nat) : Nat := 0

def s0a3I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a3K2 (80+((h/1+packedAt s0a3K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | 3 => packedAt s0a3K3 (94+((h/1+packedAt s0a3K3 (90+(h % 1)*4) 4) % 12)*4) 4
  | 4 => packedAt s0a3K4 (5+((h/1+packedAt s0a3K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffff
  | 1 => 0xdfab6adb7edfab6adb7edfab6adb7edf
  | 3 => 0xf5f4bd2fd7f5f4bd2fd7f5f4bd2fd7f5
  | 5 => 0x2afffff4a92afffff4a92afffff4a92a
  | _ => 0

def s0a3Neg : Nat → Bits
  | 0 => 0xbf06c1b6fdbf06c1b6fdbf06c1b6fdbf
  | 1 => 0x4fa92a493e4fa92a493e4fa92a493e4f
  | 3 => 0xf0f03c0fc3f0f03c0fc3f0f03c0fc3f0
  | 5 => 0xfffff00000fffff00000fffff00000
  | _ => 0

def s0a3Atlas : Atlas := ⟨4, rawDecor 43 s0a3Pos s0a3Neg, 0xaa88aa8888008800, s0a3N, s0a3R, s0a3H, s0a3I, [], []⟩

def s0a4K2 : Nat → Nat
  | 0 => 0x9b20310c421d031043808410
  | _ => 0

def s0a4K3 : Nat → Nat
  | 0 => 0x328983333313202f18dc31dc43b087d887810
  | _ => 0

def s0a4K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s0a4N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | _ => 0

def s0a4R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a4K2 (i*26) 26
  | 3 => packedAt s0a4K3 (i*15) 15
  | 4 => packedAt s0a4K4 (i*4) 4
  | _ => 0

def s0a4H (_k _i : Nat) : Nat := 0

def s0a4I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a4K2 (81+((h/1+packedAt s0a4K2 (78+(h % 1)*3) 3) % 5)*3) 3
  | 3 => packedAt s0a4K3 (94+((h/1+packedAt s0a4K3 (90+(h % 1)*4) 4) % 13)*4) 4
  | 4 => packedAt s0a4K4 (5+((h/1+packedAt s0a4K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a4Pos : Nat → Bits
  | 0 => 0xef9ce737bdef9ce737bdef9ce737bdef
  | 1 => 0xffffffffffffffffffffffffffffffff
  | 2 => 0xbde739cef7bde739cef7bde739cef7bd
  | 5 => 0x52fffff94a52fffff94a52fffff94a52
  | _ => 0

def s0a4Neg : Nat → Bits
  | 0 => 0xe78c63139ce78c63139ce78c63139ce7
  | 1 => 0x7b318c6def7b318c6def7b318c6def7b
  | 2 => 0x9cc6318e739cc6318e739cc6318e739c
  | 5 => 0xfffff00000fffff00000fffff00000
  | _ => 0

def s0a4Atlas : Atlas := ⟨4, rawDecor 39 s0a4Pos s0a4Neg, 0xc8c8c8c880808080, s0a4N, s0a4R, s0a4H, s0a4I, [], []⟩

def s0a5K2 : Nat → Nat
  | 0 => 0x982320c020d030043808010
  | _ => 0

def s0a5K3 : Nat → Nat
  | 0 => 0x33331330b3331a282f185c30dc41b083b087410
  | _ => 0

def s0a5K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s0a5N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | _ => 0

def s0a5R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a5K2 (i*26) 26
  | 3 => packedAt s0a5K3 (i*15) 15
  | 4 => packedAt s0a5K4 (i*4) 4
  | _ => 0

def s0a5H (_k _i : Nat) : Nat := 0

def s0a5I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0a5K2 (80+((h/1+packedAt s0a5K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | 3 => packedAt s0a5K3 (94+((h/1+packedAt s0a5K3 (90+(h % 1)*4) 4) % 16)*4) 4
  | 4 => packedAt s0a5K4 (5+((h/1+packedAt s0a5K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a5Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffff
  | 1 => 0xb7adeb7adeb7adeb7adeb7adeb7adeb7
  | 2 => 0x5dd775dd775dd775dd775dd775dd775d
  | 3 => 0xeafabeafabeafabeafabeafabeafabea
  | _ => 0

def s0a5Neg : Nat → Bits
  | 0 => 0x6f1bc6f1bc6f1bc6f1bc6f1bc6f1bc6f
  | 1 => 0x93a4e93a4e93a4e93a4e93a4e93a4e93
  | 2 => 0x1cc731cc731cc731cc731cc731cc731c
  | 3 => 0xe0f83e0f83e0f83e0f83e0f83e0f83e0
  | _ => 0

def s0a5Atlas : Atlas := ⟨4, rawDecor 15 s0a5Pos s0a5Neg, 0xa880a880a880a880, s0a5N, s0a5R, s0a5H, s0a5I, [], []⟩

def s0a6K3 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s0a6N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def s0a6R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0a6K3 (i*4) 4
  | _ => 0

def s0a6H (_k _i : Nat) : Nat := 0

def s0a6I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0a6K3 (5+((h/1+packedAt s0a6K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a6Pos : Nat → Bits
  | 0 => 0x66dddb775d9766dddb775d9766dddb77
  | 1 => 0xbdb776dda6e9bdb776dda6e9bdb776dd
  | 3 => 0x4fc8bf22f93e4fc8bf22f93e4fc8bf22
  | 5 => 0xf9222488fffff9222488fffff9222488
  | _ => 0

def s0a6Neg : Nat → Bits
  | 0 => 0x600cc0330d83600cc0330d83600cc033
  | 1 => 0xdb336cc00000db336cc00000db336cc
  | 3 => 0xfc03f00f03c0fc03f00f03c0fc03f00
  | 5 => 0xf0000000fffff0000000fffff0000000
  | _ => 0

def s0a6Atlas : Atlas := ⟨3, rawDecor 43 s0a6Pos s0a6Neg, 0xeecceeccaa88aa88, s0a6N, s0a6R, s0a6H, s0a6I, [], []⟩

def s0a7K3 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s0a7N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def s0a7R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0a7K3 (i*4) 4
  | _ => 0

def s0a7H (_k _i : Nat) : Nat := 0

def s0a7I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0a7K3 (5+((h/1+packedAt s0a7K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0a7Pos : Nat → Bits
  | 0 => 0xe75e75e75e75e75e75e75e75e75e75e7
  | 1 => 0x3db3db3db3db3db3db3db3db3db3db3d
  | 2 => 0x78e78e78e78e78e78e78e78e78e78e78
  | 3 => 0xc2fc2fc2fc2fc2fc2fc2fc2fc2fc2fc2
  | _ => 0

def s0a7Neg : Nat → Bits
  | 0 => 0x63063063063063063063063063063063
  | 1 => 0xc30c30c30c30c30c30c30c30c30c30c
  | 2 => 0x70c70c70c70c70c70c70c70c70c70c70
  | 3 => 0x80f80f80f80f80f80f80f80f80f80f80
  | _ => 0

def s0a7Atlas : Atlas := ⟨3, rawDecor 15 s0a7Pos s0a7Neg, 0xeac8eac8eac8eac8, s0a7N, s0a7R, s0a7H, s0a7I, [], []⟩

def s0K2 : Nat → Nat
  | 0 => 0x18e5b6c2604120a0510997e154210830c42a0122baa842106008680205645483008010
  | _ => 0

def s0K3 : Nat → Nat
  | 0 => 0x66a51bc3c0be1178646ea3de5e20e040a0d3e767c5353314c78ede2578b533c50043c1ee961a791281e178f1a823a4237c7001e0764bcb0f3f616123671d34b9175b6628640b2ef17097839a3c78540624d9075378f13bc0c8021a192214382008040210a918c0a0450000f83292242424242420056424242429442429442940000539693948200424282c2828264028242000082424242940034c1910001020000a323343482540002d09509cf6050842c2960dd54210b308a9861c14210b3088d861c14210a30c89601c14210a308a9861c14210830c29651c14210830a88845486050830a89805954210830a8b86dc14210830a89861c1421083088d861c1421083098b861c14210830c8a861c14210830c89861c14210830989861c14210830889861c14210830c8b651c14210830c89651c14210830a888050a6110830945821c55254430c8a641c14288430e41515486048430c88641c14208430d0970d50420c220b098510a400c220b21801914214520d08721c1540c020d0970551620c020d0b405d7420c020d0b70553420c020d0b70552210c020d08425d4400c020988845c8400c020d09545c8400c02082d86dd54210b10d0a531c14210b10b0b85508420c310d0a75508420c310c29601d54210910e096014d4210910a24815954210810ca0641c14208410c92609d3218c010cc0205d8210c010c51651c5620c010c4976548520c010d0974548520c010859861d5420c010950815d4420c010d0975508420c0109c38758b210c010cc3215d8210c0109c0825d8210c010cc0625d8210c010d8074508210c010c24715915208010e80215903008010e09645483008010b40815483008010
  | _ => 0

def s0K4 : Nat → Nat
  | 0 => 0x8845e73d95428422eb9ecaa14211ddc56510a10c5ecaa10850862d655084284354b0284214211e5d66010a108b8e6b2e65086a46450821842abb8aa518421355d8218c210aaee2a9061084d5760843084317292c810421a90856408210c5ac8a90410862f64993524432cb00a6212214b9d54210910a58eaa10848862e65508424431632a8421221c3d4d4210910e18a6a1084886a960508424432c29cc0212219a14a60109108d8e532e648845f739943244237b94ca192218d584540c910c68a93086488654539843244332294c219221b20c26214c10c9ca6b10a60864d535885304364182c429821179ce61d48108bae730ea40862e525905204237bb2a4290218b5915214810c9ac6a90a40846e72996420433210acb21021591c552908108eaeb30c840845e73195420422eb98caa10211b5c865508108eaea30a840866552185420423cba8c0a10211d1c56510810c5ecaa10840862d6550842042d43828421021179ce65cc810cb06132e6408475759873204368184c399021960c2650c810cc842b2864086b250993210431b284c9908219358d5208410ccacaa1042086a46450821042f038284108216c9d321cc010b2ce990c60084d57608630042aaba84318021965d6608c010b64e990860087c33208430043e01904218021555d6610c010ca8cab0860085c47258430042cb3a64218021745c3210c0109aaec108600855575084300432d32aca1802196195650c010cb2cab1060085d37158830042e838ac418021365d8520c010b34e829060085997414830043a4a90a418021749c6420c010ba2e3210600855b7550830042ac3aa841802174dc5420c010ba0e2a10600855a7510830042acba88418021e2508420c010ab6eb308600855875984300432cb2cc218021745da610c010ba6eb30860085d1759843004369b2cc218021b4596610c010ba4e530860086d37658430042e9bb2c218021d4dd5610c010ba6eab0860087c37258430043e0392c218021741c9610c010b80e4b0860085d376c8430042e8bb64218021d45d7210c010ba2eb908600879274c8430042e93a64218021649d3210c010f22e990860085d074c8430043e13164218021f058b210c010ba4e310860084da76084300426cbb04218021f0484210c010ba6ec10860086d2760843004368bb04218021745d8210c010ba6ea10860085d17508430042e93a04218021741d0210c010f84e410860085d27208430043e1b104218021f0188210c010f84a410860087c15208430043e12104218021f0508210c010acaea10c4008659650c220043693086110021b45843088010f8042184400862e52590200435210ac8100218b5915208010ac8e2a90400847575984200432cb286010021a69903008010d32c81804008749520c020043693086010021f00843008010
  | 1 => 0x4148317316a9a0a418b58b54d0520c9cc429e829064d6214f4148333310a3a0a419958851d0520a58eaa14829062e6550a4148392a10a320a410f1d0655052087ee9328829045f73994414830eb1ea820a41179d66310520c3ea9318829061c5498c414832ba8cc620a4117dd853105208baec298829062c655084148354b028420a419598c5110520caac62888290666621444148332b10a220a41c95085110520c70a9300829067051980414823a38ccb98a4117dce650c5208eee3328629062e621503148316b10a818a411d5d8510c520cccc4288629066562144314822f398c2aa041175cc6155020c6a8230aa81052e72d85540828f398c2aa041475cc6155020a58e430aa810635611855408297390c0aa0418b1886055020c5aa8b14861062e745974208316ba2cba10418b10565d0820c5e80b2e841062d405974208317bb2a9a10414bdd954d0820c5ec0aa6841062d605534208316aa4c3a10411b5c965d0420c5cc4aa6821062e5458b4108316aa2c5a08418b5516290420a5aeba14821043c74d954108316aa6c4a08411b1c96510420c5e84b28821061d635504108316312a820841879526310420c3aa9318821062e625533108316aa2c5988411bdd95488420c5cc8aa4421062f7655221083163b2a910841c9dc55488420e48e2aa4421072661552210831730aa9108418bd815488420c5ac0aa4421046f7558a4008316aa2c5200411b5c96510020c5884b2880104ac7458840083172a2c4200418b5516210020c3cc12a4601054c725523008386212a918041c31c9548c020e1cc4aa4601070d62552300838610aa91804187981548c020e1e40aa4601070d2055230082a6bae8518041c3553428c020e1aa910c601062e625503008394902a8180418b551620c020e34c12a0601061e60950300838d884a818041531c9540c020e1884aa06010749205503008386392a818041c3989540c020e1842aa0601071b70550300838c382a818041c6981540c020c3cc0aa0601070f20550300838d102a818041c6481540c020e1a40aa0601070920550300838d882a818041c3551620c020b92e0b10601054d75d083008386aa6841804172dc3420c020f1681a10601070d5488430082e5b844218041565d4400c020b92e42006010788421003008236392cb216211b5cb6550b10cb6c129a858865a5318142c4237bb2a4216214bdd54210b10a5aeaa10858862e6550842c431632a8421621c394d4210b10e1aa6a1085885a87050842c432c182cb99621175cd650cb10cb060b2865884757598432c4368184c2196219694e600c7108baeb318438845d7694c21c432dbb2ca18621561c5650c310cb0c2b28618855b7550830c42ac3aa8418621569d4420c310ab2ea21061887894210830c432cb2cc218621369d8210c3109b2ec10861
  | 2 => 0xc021061361c16294430d94a1b12a21864e50d89510c365886c4a8861b20436254430c9cea312a2186c571189510c365280c4a8861939406254430d9620312a2186c610189510c364080c4a8861171d95254430aa8e2a92a2184d970597210c34d284c9908618794264c8430d3621326421869610993210c34c084c990861a394964c8430d1c42b26421868c21593210c34d282c9908618794164c8430d3620b26421869810593210c267bb2a590861a359152c84309b6eb30642184d975983210c365294c190861b254a60c8430d944330642186c821983210c267b92cb10861369c364884309b2e1b2442184cf7650a210c3473228510861721c142884309aaed28c421865465546210c2e2392a310861d1d4951884309b6e1b2a42184ce76949210c2663b2a490861d154552484309b6ea30242184d975181210c365290c090861b25486048430da4a230242186d151181210c369908c090861b28846048430da04230242186c821181210c266392ca10861931496508430c9ee4b28421864c72594210c327212ca1086193c856508430cac42b28421865521594210c32690aca10861171c16508430c9840b2842184db70590210c26c382c810861935954208430d18c8a1042185c870508210c22f398c2aa641175cc6155320c9ca6b10879052e74d9542c83173228528e419398a53d0720c9ca6b16839064d5358b41c8333314a3a0e418b9954290720cb6c129a839065a5318141c822eb9aca20e41175d663107208beed298839045d7694c41c8237baac420e41c950a51107208bae6b28639064e5358831c822f39cc3aa441175ce61d5220958e8b28851062d76d504288296bb6a821441ca9c35410a20c5ec1aa0851062d60d504288317aa4c221441561c1639462087ee8b2c831043c745944188237b92ca20c412b1d16508620c58c9aa0431046f7655021882b3b8aa810c418b1944290220a9aeba14611070f5410a308822f3b4a318441175da518c220a9aeb10c61104cd7608630882a6bae8418441e2503420c220e1ea821061105c970108308822f3b4a218441175da510c220a9aeb10861104cd7608430882acbac8018441e210a400c22087ae930ea89045e73987544822eb9cc3aa241479ce61d5120a3ae730ea89052f725875448317ba4cb212418b1d26590920c5c8132c849062c409964248327184cb21241930c26590920acae5320a2905567319051482aab98c828a41595c86414520ae2e0320a2905657218c51482b33908628a41595c84314520acce1210a2905647090851483932048428a41c91024214520e8c61210a290744309085148393ba28428a41c9d914214520e48c8a10a2907637050851482b33828428a41d81c14214520ac8e0a10a290727405085148392a028428a41d18c14214520e8860a10a29046c72997
  | 3 => 0x8c6350842b1ce630a842158d731854210b52b08c2a10854bdd76050842b1ce7b02842158d73d814210b94a86c0a10854b5d46050842e52a030284214af751814210b16ba8c0a10852b5d4605084285aea302842162f501814210b55280c0a1085aa5406050842c5aa0302842162f7650a5110b163b28528885c9dc54294442e48e2a14a2217266150a5110a9638285288858b58142944428bce730ca02145d739865010a1eba0c2aa665954c46155332caa6330ca1996583098650cca1eba0c0aa065960c261940329aae630a8598e2f6550842cc716b2a84216630f9d0605483187ae8302a418c7575185420c697baa84210634b5d5421083187ae8302a990d1e73d8154c868eb9ec0aa6434b9c860553218deeab148790e2d5458a43c871b2a4c221e431bdc96590e21ccca2b2c8510c6d7598242887172a0c0a1443b20c260cca21ccca2b286510ec8309803288697baa8520c438b5954290621cb4e1304a610c6c72596430872729ac4218431d5d66110c218daea3028410e2c541814208673b8ac999043b20c260cc821c9aa6b148210caf7650a410862eb9aca2084317dda53104218baed2988210e2c6550841086d2b8a84208439394d620c421d8a62b106210d5a70d8e50086ad380c7280434bdd54210b30a5aeaa1085985a87050842cc354b0284216618d54664c8730c6cc928e439864e6354821cc22f3a8c2a1461175d46150a30d1eeca10851858f76508428c347b2a8421461a35954210a30b18e0a10851868f60508428c346b028421461a350a6110a30c3ca1326431869610993218c34710ac990c61a308564c8630d1cc8a14431864e42594218c22e382ca10c61930816508630c9acaa10431868c64508218c236b90c2a9061954c461548308b8e6b2c841845e73d95420c23cba8c0a1061171cd6510830c5ecaa10841862d65508420c2d43828421061aa58142108308f2eb300841845c73597210c317292c9908611bdd952c8430c5ac8a96421847975983210c22e39acb108611bdc965884308bce7b2a421847975181210c22eb9aca10861171cd65084308d8e4b28421864f32594210c326192ca10861361c1649483099ce530ca41868c42592420c26bb8acaa1061351c56550830998eca92841864c65549420c2c63a2a4a1061179d461508308baea30a84184da76181420c364900c0a106136dd460508309b2ea30284186ca72181420c365290c0a1061b25486050830d3484302841869842181420c26d388c0a1061365c16510830d1eeca10841858f76508420c347b2a8421061a35954210830f16e0a10841878870508420c2c63828421061621c14210830d1ec0a10841878a60508420c3c4b028421061a35814210830d12c0a10841878a50508420c3872828421061a350a61108309b6eb30084184d975980420c26d38c
  | 4 => 0x40707b0002180001400c2a02a808006154500270002c83903b00e0f4000001f800c2e881012038019c00fc9cc02005670000670171cc00c0602600072c600170d85a42b8503a4780e4bf6098000078030000ade700c648394771fc0988b8058015446dc022757fe1a80680c0101b00200302a83cad80b2620f04f84d6ee134018b04e02a8688f6048374e88021ec068000fb0d40040c1791f40fc5b94c02220c4902d0020800583a018000099590e23500088700a0200016500e198000d102c01c15a2d00e000010110561883702900a240b800001600c0600f0101081d0130580fc608ea0560140000100014c2381a0760fc23913020244f700604a0084a87a022014038d90224d8150010d6028958050060180211c08a0000906605801c348000000100380301800c2e0350040d8260230660000d8190d402c0181001c070070460aa164008310120242d93400c160028210000100f00c06403c1f0850a80a8000380be0780801d01e18c0006300e050000ea00620c0103500600004003004034028010a04004620113100c43a200c51224511144448a244440000000100420a042e1c3142450210006100400706018840020303088a31508541840a0c2854510195c20c0850010185a2000000e02103001408000530e1010a100004c9932c50a1400502e1040808208000420208200000410304040820694a0028509800a14b0500091010288000a9500020050a0000000008450a4285870800204000c384993284f0e1264c994000b0e1264c994264f0e1264c0000204a00264c980044cb002814a2504002d30204000004c993a84c9944a50a532852981280800028002810a88304018424204000800a000000214281041e2078508000060c11688581a404000800400142000920004012000414080621c3a244891220e01887041d207850a1428509200010a107850a142840e207881e2070c000020406880001a185001a100a3103800c02881a310381881c281101003108211221188216c58a1228508003081800800104022d4420600100162c00b000010242840044248083428409242a34524285080000012100a346102490a1244908051a309242850a10004000028400100019112204000000f0a100c200a812a10a8500001012a0010200000150014082080210446501000400214001c10700002610108004a20688300142150b44a850210000a210a220414086041c18208000042a08a95280c1d1845000000001010155a0146000020008091828c01100000004600023000000082060a30445180688caa3008d1b4008c023008db00468da00685402368d1a000409b34468eab46801a00050c0430010a00040618000000548bce730ca12145d739865090aac382c628a858b9db6550842a5cedb2a842152e71d954210a96b86caa1085a35
  | 5 => 0x3e1f65460060faa43d332ecd66da519cb0b42015097552005bc21966ca0dc322a9064c1a6b9790301026a58e9c020ae7a74ae92ed48608f14433b40874f9983e51705683b0f18fae61b4aa541c75aa2a664f44487f46c6eacf4dd0253734b8bd36571098d68bd55dee5e7f9368885324c81a2a2ea8130374f22319b3de5cc6851bc677580aa27b2a90ce3c4ea5866865a3a99e09862c5ea2e6390505204969c466a41f04a8592672d09f430ce54386f47edbb11748ec099bcc43869f1bed4870b000410ec8fc8b57c2171eaf814226157b3b1c51c87449dc099d81ab130ba43d616b7a6609f1e8de06bab1838e2d3c49200ea2623c53798fda450aa9346819f34489c670dfb9d11e6a8fea8643a54961868074a58ef54875d389de5481de8c03f4901262a081bc36c688c9fa9e3aed915992d3a13226d3d649a8920d2954b50115480435d3e0db0231200e40634a184190e88f23c2b88a143c75a70653d483ff19a1f0ff1cb231bd8cf1670ed1ead47a882d5c1f53c005e3f90e0952b10d81f090258858082b0b6d1d91e57cf458c4f21bd2a5f720355eece882f247c09e212189863ea0446f27829e2520c602bfd960ae85469e9136b0c71a2582d3199359581b026e8147d84452e289d22bc420f2a182ad426f660bb7f06ad427f25917439800880038149439b373482998b770ccf0480bba5806565319f83c33903172910dc5553951b02ade4c236e692a4a03c2fc8bc9d1d92de5a94c3b50204827e86f9dd3ecf92fc8314d85a38e0f5410639e69e03442ad3c15ab4a0343412ed3179c3a3f2114b74c754cfa825bb7160229a44e6250029cccc57706d6818701d12e22f248268bb8f1c16192f21fe26f0120ed6222a4d3309d5aa0230d64e61167971a4991e5708295b3b1e7043da5bbb11c8ad45f532122f7d522d63b4091408b29b29ba55138850411d49a996a8a147a090a06ddb62fb840c819d9a63210fd3f239670df23c3e329d2788a42fa683682b39e7ba625de99b9970ac9d878728ec030c24220078ae2367b6d0c713e66662fc8d2d7457379e90746de1b23113e44c7553ac6438d119a284e4827015f85c594310df4125eae4c4d20413879e7b12c73872d6740e736865493175c7511aa52639e855279d285ccea7e33268f1256c8d937afc22d4d20a890a5449c92d2f84a85b94535e952c919404581a147c86c4e205165abb0b2a850c4b601e90a24c00aa14df1dcfd23b4ae376b31754a434ae354ea21a243358611c38ec211d4583786391fadf20b38479b72223468bb31a0a71c8f70190bb1d01f8f02907f97c9094ed3c4b5afe5c2d25c3cdd1d31417ebaf9a91c189ba85aa6014005f72426c5608859afc9889af4f6c2900bcd35ab69ae8fd1760b574245880c98c34d5a18a369c2b75e25127cb5e5f4038060420040080e00b10d23
  | 6 => 0x26092122438849e718a16a76c17c522cef700dba70f92edc305a066dc14a4e74c04b9a08ea99f3900b4a09c6da86e5089b8265881133a8014a0233486e05363e877e651a7a9f2190b21b4c155934cf4327464062a01e4070ff949a1a86eb9638aab9a3158e280f719409ed50a4a41091610084cc51ad0475e9029768c08ee62069c7313c89e922839b09d1b0b073d86752750e3e2dd00ab425b8cfe4016d4622f0f6a6d4e3255adb16496d81542c60dc5e0b828c3bef84b04b95460d9af86a99a7ae7a12f41b1a9e806520d5215139079ec364727371283d128283eee94c916603ae0d70246108808cc8228c07251a9a2a00420b418442c988f9bd896c2da20bbe141520da1a42c40010890f3f06b0b6250514c91e32c54bc3e427bfa6a72caa4255a8eed8149faa024cc4927d350c88af0d46804e5260d6504ec9002348f2608fa2bb3b8b05a336e632179b33b94d1451ac2e4600bc2374221f8d59831cda9041e51973746d4a8f36854e528644c05173827513189694d14d1c7767f0395487415222a18f0aeab854d4818ca692208ea595223d94fa9018124aa1a90b2ea42f66c53bcf545ca90aca4232f697135328d0060a216435c4b6db50f4024fe632a4548537522a421f584a6415ba63460484a4b492ea40e99567ce0c9e2208a40c49e382c5687887b8b73710752044547114460b965baf002310d52234a083e97ae0524c37e57310ce70e00b2971a8a9c40e4c25fcd04e4fe257a5f56cf88fb2204af32a1c9ab4ce991c8d1862a40a8b3808d71540352825464dbcacf3300852b1dd384d5652b396793a05302ea90ca2831353350563e4c64440d23d17c0b120a2430e4794c14732e28c
  | _ => 0

def s0K5 : Nat → Nat
  | 0 => 0x542042f46150810bed8142042f860508109fd94420427e65108109f594420427c6510810eb508420427f65cc8109f997320427d65cc8109f197320435e53cc810d754f32042f661cc810bd587320427f650c8109f994320427d650c8109f194320427f650c4109f594310435e530c410d754c31042fa600c410be580310437565c8410bd59721043b664c8410bd99321042b664c8410ed59321042f464c8410ddd4b210437552c8410bdd8321042f560c8410fc943210437650c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f65084109f59421042de6308410b758c210436e5208410db54821043e52108410be98021042f96008410dd59421042f565084109d59421042f66408410bd19021043d66308410f558c21043e66208410bd98821043775208410f994821043e55208410dd54821043e64208410f950821043e73208410f90c821042f76008410fc98021043f16008410bd58021043f25008410dd940210437965cc010be59730042fa63cc010ded4f300437953cc010bed8730042f961cc010fc947300437a51cc010fcc8730043f021cc010d7d96300435e658c010d7596300435c658c010d7d4a300435e528c010d754a300435c528c010f598630043d5618c010d794630043d7218c010f508630042de608c010b6982300435e508c010f5c4230043da108c010f644230043d5108c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bd98430042f5610c010f64c03004379650c010be5943004279650c010f698c30042fa630c010ded4c30043da530c010f654c3004379530c010f6cc830043da320c010f64c830043d8320c010bed8430043f2610c010fc58430042f9610c010fc944300437a510c010f6cc430043da310c010f64c430043d8310c010fcc8430043f0210c010d7d94300435e650c010d7594300435c650c010d7d48300435e520c010d7548300435c520c010f598430043d5610c010d794430043d7210c010f508430043da600c010b7980300435e500c010f6c8030043d9200c010f5c4030043da100c010f644030043d5100c010f6994300435a650c010f65943004359650c010f6d8830043da620c010f658830043d8620c010f6d4830043da520c010f654830043d8520c010f690830043d9420c010f610830043db610c010f698430043d2610c010f658430043d1610c010f618430043da510c010f4944300435a510c010f6c8430043d3210c010f688430043d9210c010f608430043d0210c0109fd96200427d6588010db94a200436d5288010bd98620042f56188010f908620043d830880109fd94200427e65080109f594200427c6508010af99020042bd6408010db948200436d5208010bd98420042f56108010f908420043d83008010
  | 1 => 0x435f2014d10d7880534435d2014d10d7080534435f1014d10d6c40534435e1014d10d7440534435c1014d10d6040534427e64d49109f593524427f63d49109f98f524427d63d4910db58b524427d62d4910db8cb524436d32d49109f987524427d61d49109f187524436f21d4910db487524427e60d49109f583524427c60d4910d78c3524435c30d4910dbc83524436d20d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436d43d4910dbd87524436e61d4910db587524436c61d4910dbd07524436e41d4910db507524436c41d4910dbcc7524436e31d4910db4c7524436c31d4910dbd83524436e60d4910db583524436c60d4910dbd03524436e40d4910db503524436c40d4910dbcc3524436e30d4910d38c3524436d30d4910db0c3524434c30d4910dbc43524436e10d4910db443524436c10d4910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436d4314910dbd84524436e6114910db584524436c6114910dbd04524436e4114910db504524436c4114910dbcc4524436e3114910db4c4524436c3114910dbd80524436e6014910db580524436c6014910dbd00524436e4014910db500524436c4014910dbcc0524436e3014910d38c0524436d3014910db0c0524434c3014910dbc40524436e1014910d9840524436d1014910db040524436410149109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910d7d4c424435c5310910dbd48424436c5210910eb50842442fa6010910be580424427f65cc9109f997324427d65cc9109f197324433f54cc910cf153324435f53cc910d714f324436f52cc910db14b324427f650c9109f994324427d650c9109f194324433f540c910cf150324435f530c910d714c324436f520c910db14832442f6610c910bd584324427d6594c10d7d4e530435e5314c10d754c53042ee6214c10bb588530427e64d48109f593520427f63d48109f98f520427d63d4810dd987520427e61d4810de983520427e60d48109f596520436f52948109fd95520427f64548109f191520427f63548109f58d520427c6354810dbd89520436e3254810db4c9520427f61548109f585520437461548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db948520436d52148109fd96420427e65908109f596420427c6590810db94a420436d5290810bd98642042f561908109fd95420427e65508109f595420427c6550810db949420436d5250810bdd8
  | 2 => 0x53ccb10d754f32c427f650cb109f99432c427d650cb109f19432c435e530cb10d754c32c42f6610cb10bd58432c427e650c7109f59431c435e530c710d754c31c43d5310c710be98031c42f9600c7109f59621c435e5388710d754e21c436e5288710db54a21c42fa6088710be58221c42de6308710b758c21c435e5308710d754c21c436e5208710db54821c42fa6008710be58021c4379650c310be59430c43da630c310f6d4c30c437b530c310f694c30c43d9530c310de54c30c4359530c310f614c30c43db320c310f68c830c43d9320c310f60c830c42fb610c310be58430c43db310c310f68c430c43d9310c310f60c430c43d9650c310d659430c42d9650c310f6d8830c43da620c310f658830c43d8620c310f6d4830c43da520c310f654830c43d8520c310f690830c43d9420c310f610830c43db610c310f698430c43d9610c310f618430c43db210c310f688430c43d9210c310f608430c427f6454a109f191528427f6354a109f58d528427c6354a10dbd8952843776154a109fd8552842776154a10ddc85528436f2154a10db485528427f6590a109f996428427d6590a109f196428436e5290a10db54a42842f66190a10bd586428427f6550a109f995428427d6550a109f195428436e5250a10db54942842f76150a10bd185428427f6510a109f994428427d6510a109f19442843ad4210a10bdd8442842fa6010a10be580428427f65cca109f997328427d65cca109f197328435f53cca10d714f328436e52cca10db54b32842f661cca10bd587328427f650ca109f994328427d650ca109f194328436e520ca10db54832843756508610bd59421842f66408610bd19021843d66308610f558c21843e66208610f9d4821843775208610dd54821843e45208610f990821843e54208610f9cc821843e43208610bdd8021842f560086109f98e508427e61942109f98250843771094210de84250843791094210dd442508435e658c210d7596308435f528c210d794a308435d528c210d714a30843d6618c210f5586308435d518c210f5c8630843d4218c210f6c4230843d7108c210f5442308427e650c2109f594308435e530c210d754c30842f6610c210bd584308435e650c210d7594308435f520c210d7948308435d520c210d714830843d6610c210f5584308435d510c210f5c8430843d4210c210f698030843db100c210f5c4030843d5100c2109f596208436e5288210db54a20842f66188210bd58620843e42188210af99020842bd6408210db948208436d5208210bd98420842f56108210f9084208435f6214d10d7988534435d6214d10d7188534435f6114d10d7984534435d6114d10d7184534435f2114d10d7884534435d2114d10d7084534435f6014d10d7980534425e6014d10d7580534435c6014d1097180534
  | 3 => 0x420bb98a41082ed6290420ebd0a410827f65504209f595410827c6550420cf951410833d5450420bbd8941082ec6250420bed8141082f860504209fd94410827e65104209f594410833e5410420cf55041082de6310420b758c41082ec6210420ebd08410827f65cc4209f997310827d65cc420cf953310833d54cc420d794f310835d53cc420bb98b31082ed62cc4209fd94310827e650c4209f594310833e540c420cf550310836d6588420bb59621082ee6488420bb192210836f5488420eb95221083ad5488420db552210832d5488420db94e210836c5388420f998621082ee6188420dbd46210836d5188420bbd8221082ed6088420fa942210827e64940209f592500827f63940209f98e500827d6394020dbd0a500836c4294020db886500836c2194020dec82500836f2094020db482500837820940209fd96400827d6590020cf952400833d5490020bb98a40082ed6290020eb10a400827e65100209f594400827c6510020bb98840082ed6210020eb108400835f658c020d7996300835d658c020d7196300835f548c020e7952300835e548c020c7952300839d548c020d7552300831d548c020d715230083ce628c020f358a300835e528c020f3d0a30083cc428c020d7946300835d518c020f388630083cc218c020b7982300835e508c020f3c8230083da208c020f648230083cd208c0209fd94300827e650c0209f594300827c650c020cf950300833d540c020d794c300835d530c020bb98830082ed620c020fa480300835f650c020d7994300835d650c020d7194300835f540c020e7950300835e540c020c7950300839d540c020d7550300831d540c020d715030083ce620c020f3588300835e520c020f3d0830083cc420c020d7944300835d510c020f388430083cc210c020f698030082de600c020d794030083db400c020f610030083cf200c020f688030083d9200c020f348030083c9200c020f6c40300835f6294f10d798a53c435d6294f10d718a53c435f6194f10d798653c435d6194f10d718653c435f2194f10d748653c435f6094f10d798253c435d6094f10d718253c435f2094f10d788253c435d2094f10d708253c435f1094f10d784253c435d1094f10d704253c427f6454b109f19152c427f6354b109f58d52c427c6354b10dbd8952c427f6054b10d78c152c435c3054b10dbc8152c436d2054b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10d794e42c435d5390b10dbd4a42c436c5290b109fd9542c427e6550b109f59542c427c6550b10d794d42c435d5350b10dbd4942c436c5250b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10d794c42c435d5310b10db94842c436d5210b10eb50842c427f65ccb109f99732c427d65ccb109f19732c435e
  | 4 => 0x9080514827e65d05209f597414827c65d0520cfd53414833c54d0520d7d4f414835c53d0520bb98b41482ed62d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e41483ad4290520ddd46414837451905209fd95414827e65505209f195414833f5450520cf151414835f5350520d714d41483775150520dd145414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520d7d4c414835c5310520bb98841482ed6210520eb50841483775110520dd14441482fa6010520be580414827e65cc5209f597314827c65cc520cfd53314833c54cc520d7d4f314835c53cc520ddd47314837451cc5209f994314827d650c5209f194314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd144314833f6395020cf98e540833d6395020cf18e540833f6295020cf98a540833d6295020cf18a540833f3295020cf8ca540833d3295020cf0ca540833f6195020cf986540833d6195020cf186540833e3195020cf4c6540833f2195020cf886540833d2195020cf086540833f6095020cf982540833d6095020cf182540833f3095020cf8c2540833d3095020cfc82540833e2095020cf482540833c2095020cfc42540833d1095020cfd91540827f63550209f58d540827c6355020cfd0d540833d43550209fd89540827e62550209f589540836c62550209f189540826c6255020cf909540836c4255020cf109540832c42550209fd85540827c6155020db085540836f2055020db481540833f6355020cf98d540833d6355020cf18d540833f6255020cf989540833d6255020cf189540832c6255020cfcc9540833e3255020cf4c9540833c3255020cfd85540833e6155020cf585540833c6155020cf8c5540833d3155020cfc85540833e2155020cf485540833c2155020cb085540833f6055020cf981540833d6055020cf181540833f3055020cf8c1540833d3055020cfc81540832f2055020cf881540833d2055020cb481540833c2055020cfc41540833d10550209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20bb98a43082ed6290c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20db59742082ed65d08209b59742083ae64d0820bb993420836f54d0820eb95342083ad54d0820db553420832d54d0820bb98742082ef60d0820bb58342083ea50d0820ebd0342083ad40d08209f992510827d64944209fd8e510827e63944209f58e510827e6294420dd98651083763194420dd4c651083772194420dd086510827d60944209fd97410827e65d04209f597410833e54d0420cf55341082ee62d0420bb58b410827f65904209f996410827d6590420cf952410833d5490
  | 5 => 0x544833f3015120cf8c0544831e3015120cf4c0544833c3015120c70c0544833f2015120cf880544832e2015120cf480544833c2015120cb080544833f1015120cf840544833d1015120cf040544835f6414d20d7990534835d6414d20d7190534835f6214d20d7988534835d6214d20d7188534835f4214d20d7908534835d4214d20d7108534835f6114d20d7984534835d6114d20d7184534835f2114d20d7884534835d2114d20d7084534835f6014d20d7980534835d6014d20d7180534835f4014d20d7900534835d4014d20d7100534835f2014d20d7880534835d2014d20d7080534835f1014d20d7840534835d1014d20d7040534827f6590d209f996434827d6590d209f196434833f5490d20cf152434835f5390d20d714e434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c43482ee6210d20bb588434836e6590920bb996424826e6590920bb59242483af5490920db95242483ac5490920db152424832c5490920f3d4e42483cc5390920f9d4642483e45190920bb98242482ec6090920fad42424836f5090920eb90242483ce3090920f30c2424826c6550920ebd9142482ef6450920ebd51424836e5450920eb151424836c5450920cb15142483cf5350920f314d42483e75150920f914542483eb6050920bb98142483e86050920bb18142483eb5050920dbd4142483af4050920eb50142483ce3050920f30c1424837764d4520dd993514837564d4520dd193514837763d4520dd98f514837563d4520dd18f514837743d4520dd90f514837543d4520dd10f514837762d4520dd98b514837462d4520ddd0b514837642d4520dd50b514837442d4520ddccb514837632d4520dd4cb514837432d4520ddd83514837660d4520dd583514837460d4520ddd03514837640d4520dd503514837440d4520ddcc3514837630d4520d58c3514837530d4520dd0c3514835430d4520ddc83514837620d4520dd483514837420d45209f990514827d64145209fd8c514827e63145209f58c514836e4214520db50851483766114520dd8c451483753114520dd884514837521145209f580514827c6014520d78c0514835c3014520db880514836c2014520ddc4051483751014520ddd9051483766414520dd59051483746414520ddd8c51483766314520dd58c51483746314520ddd0c51483764314520dd50c51483744314520ddd8851483766214520ddd0851483764214520d990851483754214520d950851483744214520ddcc851483763214520dd4c851483743214520ddd8051483766014520dd58051483774014520dd90051483754014520dd10051483773014520dd8c051483563014520dd4c051483743014520d50c051483772014520dd88051483662014520dd48051483742014520d
  | 6 => 0x2dd6394620ddd46518827e64946209f592518827f6394620d798e518827e63946209798e518835d63946209f58e518825d63946209f58a51883762194620dd48651882bf6454620af19151883775154620dd145518827f65d06209f997418827d65d0620bb98b41882ed62d06209fd96418827e65906209f59641882ee6290620bb58a41883af42906209fd95418827d65506209f19541882ef6250620bb189418827f65106209f994418827d6510620cf15041882de6310620b758c41883af4210620be98041882f960106209fd97318827e65cc6209f597318835f53cc620d714f31882ee62cc620bb58b318827f650c6209f994318827d650c6209b59621882ee6488620bb192218836f5488620db552218836e5388620db14e218836f5188620f994621883e55188620db54621882ef6088620fa98221883e96088620bb582218836e5088620db59421882ed6508620bb99021882ec6408620dbd50218836d5408620f398c21883cd6308620db94c218836c5308620f998421883e75108620dbd44218836d5108620f914421882ef6008620bb58021883ea50086209f59640882ee6290220bb58a40883ac4290220d7996308835d658c220d7d52308835e548c220d755230883ce628c220f358a308835d528c220f3d0a30883cc428c220d7946308835d518c220f388630883cc218c220f6c8230883cf208c220f3482308827d650c220d794c308835d530c220bb98830882ed620c220d7994308835d650c220d7d50308835e540c220d755030883ce620c220f3588308835d520c220f3d0830883cc420c220d7944308835d510c220f388430883cc210c220f698030883da400c220f650030883db200c220f3c8030883cd200c220f6c40308833d64d51209f593544827f63d51209f98f544827d63d5120cfd0f544833d43d51209f98b544833f42d5120cf50b544827e61d51209f587544827d60d5120cfd03544833d40d5120d78c3544835c30d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833e62d5120cf58b544833c62d5120cfccb544833e32d5120cf4cb544833c32d5120cfd87544833e61d5120cf587544833c61d5120cf8c7544833d31d5120cfc87544833e21d5120cf487544833c21d5120cfd83544833e60d5120cf583544833c60d5120cfcc3544833e30d5120c78c3544833d30d5120cf0c3544831c30d5120cfc83544833e20d5120cf483544833c20d5120cfc43544833e10d5120cf443544833c10d5120cfd8c544833e6315120cf58c544833c6315120cfd88544833e6215120cf188544833f3215120cf8c8544833d3215120cf0c8544833f6115120cf984544833d6115120cf184544833e3115120cf4c4544833f2115120cf884544833d2115120cf084544833f6015120cf980544833d6015120cf180
  | 7 => 0x408430b7190210c2de6208430f3d48210c3cc5208430f3908210c3cd4208430b7984210c3cf2108430f5884210c3d52108430f3484210c2df6008430b7980210c2dd6008430f6940210c35e5008430cfd9154c827f63553209f58d54c827c6355320cf90954c833c42553209fd8554c827c61553209fd8154c833f4055320cf50154c835e3055320d70c154c835f6494f20d799253c835d6494f20d719253c835f6294f20d798a53c835d6294f20d718a53c835f4294f20d790a53c835d4294f20d710a53c835f6194f20d798653c835d6194f20d718653c835f2194f20d788653c835d2194f20d708653c835f6094f20d798253c835d6094f20d718253c835f4094f20d790253c835d4094f20d710253c835f2094f20d788253c835d2094f20d708253c835f1094f20d784253c835d1094f20d704253c827f6590f209f99643c827d6590f20d794e43c835d5390f209fd9443c827e6510f209f59443c827c6510f20d794c43c835d5310f20bb98843c82ed6210f20dbd9542c82ef6550b20ebd9142c83af5450b20db95142c83ac5450b20db15142c832c5450b20f394d42c83cd5350b20bb18142c83af4050b20f38c142c83cc3050b209f99251c827d64947209fd8e51c827e63947209f58e51c836e4294720db50a51c83766194720ddc8651c83742194720d78c251c835c3094720db88251c836c2094720ddc4251c837510947209fd9741c827e65d07209f59741c835e53d0720d754f41c82ee62d0720bb58b41c837651d0720dd54741c827f65907209f99641c827d6590720cf95241c833d5490720d794e41c835d5390720eb50a41c827f65507209f59541c827c6550720d794d41c835d5350720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82de6310720b758c41c835e5310720d754c41c82ee6210720bb58841c83ad4210720dd94441c837551107209fd9731c827e65cc7209f59731c835e53cc720d754f31c827f650c7209f99431c827d650c720d794c31c835d530c720bb98831c82ed620c7209fd8f548827e63d52209f58f548827e61d52209f587548837a60d5220dbc83548833f5495220cf152548833c5455220cfd91548827f63552209f58d548827c63552209fd89548833f4255220cf509548827f61552209f185548836f2055220db481548835f5394e20d714e538827f6590e209f996438827d6590e209f19643882ee6290e20bb58a438827f6510e209f994438827d6510e209b597428836f54d0a20eb95342883ad54d0a20db55342882ee61d0a20bbd8342883ea60d0a20fa58342882ed60d0a20db94342883af40d0a20db59442882ed6510a20eb99042883af5410a20dbd50428832f5410a20db55042883ac5410a20bb98442882ef6010a20bb58042883ea5010a20b798e5188
  | 8 => 0x30be983210c2f960c84309fd96210c27e65884309f596210c2df6388430b798e210c2dd6388430b718e210c3cf3288430f30ca210c3765188430dd546210c27f65484309f595210c27c6548430b7d8d210c2de6348430b758d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c2df6308430b798c210c2dd6308430b718c210c36c5208430f3cc8210c3cc3208430b7596520c2de6494830b7592520c3cf5294830d7d4a520c3cc5294830b7986520c2dd6194830f6942520c35e5094830b7d95520c2df6454830b7191520c3cf5254830d7949520c3cc5254830d7149520c2df6154830b7185520c35f5154830f6941520c35e5054830b7d96420c2de6590830b7596420c2dc6590830b7592420c2de6290830f394a420c3cd5290830e7d0a420c2de6190830b7586420c2df6090830b7982420c2dd6090830f6942420c35e5090830f3c82420c2df6550830b7995420c2dd6550830b7195420c3ce5250830f3549420c39e4250830b7d85420c2dc6150830f6d81420c2df6050830b6d81420c2dd6050830f6181420c2dc6050830b6181420c3da5050830d7941420c2df6510830b7994420c2dd6510830b7194420c2de6210830f3908420c39d4210830e3508420c2de6110830b7584420c2df6010830f6980420c2de6010830b6980420c3d96010830b7580420c2d96010830f6940420c35e5010830b7596510c2de6294430b758a510c3d75194430d7d46510c3d45194430f6182510c3da5094430d7942510c2df6554430f3d89510c2df6254430b3d89510c3cc6254430b7189510c2cc6254430d7d49510c35d5254430f5d45510c35e5154430f5145510c35c5154430d5145510c3d86054430f6941510c35e5054430b7d97210c2de65c8430b7597210c2dc65c8430e7993210c2de64c8430a7993210c39d64c8430b7593210c29d64c8430b7193210c3ce52c8430f354b210c2df60c8430f6983210c2de60c8430b6983210c3d960c8430b7583210c2d960c8430f6943210c35e50c8430b7d96210c2de6588430b7596210c2dc6588430b7d92210c2de6488430b7592210c2dd6288430f3d4a210c3cc5288430f390a210c3cd4288430b7986210c3d65188430f5546210c3d72188430f3c86210c2df6088430b7982210c2dd6088430f6942210c35e5088430b7d95210c2de6548430b7595210c2dc6548430b7d91210c2de6448430b7591210c2dc6448430f3949210c3cd5248430f5945210c3d55148430f5c85210c3ce2148430f6d81210c2df6048430b6d81210c2dd6048430f6181210c2dc6048430b6181210c3da5048430d7941210c2df6508430d7994210c2de650843097994210c35d6508430b7594210c25d6508430b7194210c2df6408430b7990210c2dd6
  | 9 => 0x94842cc36d5210b30eb50842cc2fa6010b30be58042cc27e62947309f58a51cc3766194730ddcc651cc37431947309f58251cc35e3094730d70c251cc3771094730dd44251cc27f65c87309f99721cc27d65c8730af99321cc2bd64c8730dd94721cc37551c8730be98321cc2f960c87309fd9621cc27e65887309f59621cc36e5288730db54a21cc27f65487309f59521cc27c6548730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc36e5208730db54821cc3765108730dd54421cc2df6590a30b7996428c2dd6590a30b7196428c3ce5290a30f354a428c39f4290a30b7986428c2dd6190a30b7d82428c2de6090a30b7582428c3cf2090a30b7d95428c2de6550a30b7595428c2dc6550a30f3949428c3cd5250a30e7909428c2df6150a30b7185428c2df6050a30b7581428c2dc6050a30b7d94428c2de6510a30b7594428c2dc6510a30f3908428c39d4210a30e3508428c2de6110a30b7584428c2df6010a30b7980428c2dd6010a30b7d97218c2de65c8630b7597218c2dc65c8630e7993218c2de64c8630a7993218c39d64c8630b7593218c29d64c8630b7193218c2df60c8630b7983218c2dd60c8630b7d96218c2de6588630b7596218c2dc6588630b7d92218c2de6488630b7592218c3ce5288630f354a218c3ce4288630f350a218c3d72188630f3c86218c2df6088630b7982218c2dd6088630b7d95218c2de6548630b7595218c2dc6548630b7d91218c2de6448630b7591218c2dc6448630f5c85218c3ce2148630b7d81218c2dd6048630b7181218c2df6508630d7994218c2de650863097994218c35d6508630b7594218c25d6508630b7194218c2df6408630b7990218c2dd6408630b7190218c3ce5208630f3548218c3ce4208630f3508218c3cf2108630f5884218c3d52108630f3484218c2df6008630b7980218c2dd6008630d7982508c35a60942309fd91520c27c64548309fd8d520c27e63548309f58d520c27c63548309718d520c36f6254830dbcc9520c35e3254830db0c9520c35c32548309fd85520c27c6154830d7cc5520c35d31548309fd96420c27e65908309f596420c2df6390830b798e420c2dd6390830b718e420c36e5290830db54a420c27f65508309f595420c27c6550830b7d8d420c2de6350830b758d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c2df6310830b798c420c2dd6310830b718c420c3ad4210830be980420c2f960108309fd8e510c27e63944309798e510c27d63944309f98a510c27d6294430dd986510c3773194430d7cc6510c35d3194430dd0c6510c27f65c84309f997210c27d65c8430af993210c2bd64c8430b7d8f210c2de63c8430b758f210c2dc63c8430db94b210c36d52c84
  | 10 => 0x44867d63d5121cfd0b544873d42d51219f587544873f41d5121cf507544876e21d5121db087544867e60d51219f583544867f6590d219f996434867d6590d219f196434873f5490d21cf15243486ee6290d21bb58a43486f66190d21bd586434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434867e64141219f590504867f63141219f98c504867d63141219f58450487772114121db88450487742114121db084504877a6014121de88050487792014121de84050487791014121cfd91540867f63550219f58d540867c63550219f989540867c6255021cf909540873c42550219fd81540867c6055021d7d92530875e6494c21d7592530875c6494c21d7d8a530875e6294c21d758a530875c6294c21d7d0a530875e4294c21d750a530875c4294c21d7d86530875e6194c21d7586530875c6194c21d7d06530875d4194c21d7c86530875e2194c21d7486530875c2194c21d7d82530875e6094c2197982530875d6094c21d7182530875f2094c21d7882530875d2094c21d7082530875e1094c21d7442530867f6590c219f996430867d6590c219f196430875e5390c21d754e43086ec6290c219fd94430867e6510c219f594430867c6510c21d794c430875d5310c21bb98843086ed6210c21bd98443086f56110c21dbd9542086ef6550821ebd9142086ef6450821ebd51420876e5450821eb151420876c5450821cb15142086ec6350821f394d42087cd5350821bbd8542086ed6150821f994542086ec6050821db541420876d65cc821bb59732086ef64cc821bb59332087ce63cc821bb98f320876f53cc821f394f32087cd53cc821db54f320874d53cc821bbd8732086ed61cc821f994732087cf31cc821f34c732086ee60cc821f38c3320867e64944219f592510867f63944219f98e510867d6394421db90a510876d4294421dbcca510876c3294421ddc86510876f2194421db486510877421944219fd96410867d6590421cf952410873d5490421d794e410875d5390421bb98a41086ed6290421eb50a410867e65104219f594410867c6510421d794c410875d5310421bb98841086ed6210421eb50841087e521104219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421f54c4310867e64940219f592500875f63940219fd8e500867e63940219f58e500875c63940219f98a500877a6094021dec82500877820940219fd9152cc27c6454b30dbd8952cc36f3254b30db0c952cc27f6154b309f18552cc27f6054b309f58152cc35e3054b30d70c152cc36f2054b30db48152cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b309fd9542cc27d6550b309f19542cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30db
  | 11 => 0x3c2195321cfd8254c873e6095321cf58254c873c6095321cf8c254c873d3095321cfc8254c873e2095321cf48254c873c2095321cfc4254c873e1095321cd84254c873d1095321cf04254c873f64553219fd8d54c867d63553219f18d54c873f4355321cf50d54c873e4255321cf10954c867f6155321cfd0554c873d4155321db88554c876c21553219fd8154c867c6055321cfd8d54c873e6355321cf58d54c873c6355321cfd8954c873e6255321cf18954c873f3255321cf8c954c873d3255321cf0c954c873f6155321cf58554c873c6155321cfcc554c873e3155321cf4c554c873c3155321cfc8554c873e2155321cb88554c873d2155321cf08554c872c2155321cfd8154c873e6055321cf58154c873c6055321cf8c154c873d3055321cfc8154c873e2055321cf48154c873c2055321cfc4154c873e1055321cf44154c873c10553219fd9643c867e6590f219f59643c873e5490f21cf55243c86ee6290f21bb58a43c867f6510f219f99443c867d6510f219f19443c873e5410f21cf55043c86f66110f21bd58443c867e64943219f59250c867f63943219f98e50c867d6394321db88650c876c2194321de98250c877b2094321de08250c877a1094321de44250c867f63d52219f98f548867d63d5221dd987548867e60d52219f583548873f5495221cf152548873c5455221cfd91548867f63552219f58d548867c6355221cfd0d548873d43552219fd89548873f4255221cf509548867f60552219f181548875f5394e21d714e538867f6590e219f996438867d6590e219f196438875e5390e21d754e43886f66190e21bd586438867f6510e219f994438867d6510e21bb98843886ed6210e21db59642886ed6590a21db952428876c5490a21bb98e42886ef6190a21bb58642887e65190a21bb982428876d5090a21dbd9542886ef6550a219bd9542887af6450a21eb951428876e5450a21cb95142887ad5450a21db15142886ec6350a21f9d8542886ef6150a21bb58542887e46150a21db94542886ec6050a21db541428876d65cca21bb597328866d65cca21bbd9332886ed64cca21dbd4f32887ce53cca21f354f328876d53cca21bbd8732887e661cca21f958732886ed61cca21db94732887cf31cca21f34c732886ee60cca21f38c3328876d650ca21bb59432886ef640ca21bb59032887ce630ca21dbd4c328876d530ca21bbd8432886ed610ca21f994432886ee600ca21f38c0328867d6590621bb98a41886ed6290621eb50a418867d650c621d794c318875d530c621bb98831886ed620c621ded42508867e64942219f592508867f63942219f98e508867d63942219f58a50887772194221dd086508877a2094221de48250886df6354221b718d508877b5054221de141508873d64d51219f593544867f63d51219f98f5
  | 12 => 0x94042de9825010b7b2094042de0825010b3f64553329f18d54ccb3e4355332cf10d54cca7f62553329f58954ccb3f4255332cf50954cca7f61553329f18554ccb5f3155332d74c554cca7f60553329f18154ccb5e3055332d70c154cca7e64947329f59251cca7e63947329798e51cca7d6294732dd98651ccb773194732d7cc651ccb5d3194732dd0c651ccb762194732dd48651cca7e60947329f58251ccb5e3094732d70c251cca7e64943329f59250cca7e6394332d718e50cca7d6294332d78ca50ccb5c32943329f98650cca7d6194332d7cc650ccb5d3194332de98250ccb7b3094332de0c250ccb5c3094332d60c250ccb7a2094332de48250ccb3f64550329fd91540ca7e63550329f18d540cb3e4355032cf10d540ca7e62550329f189540cb3e4255032cf109540ca7f61550329f185540cb6c21550329fd81540ca7c6055032d78c1540cb5c30550329f992510ca7d64944329f98a510cb766194432ddcc6510cb743194432ddc86510cb7421944329f982510ca7d6094432d78c2510cb5c30944329f992500ca7d6494032d718e500ca7e6294032d7cca500cb5d32940329f986500ca7d6194032db086500cb7a6094032decc2500cb783094032d70c2500cb583094032dec82500cb7820940329fd9152cc67c6454b31dbd8952cc76f3254b31db0c952cc67f6154b319f58552cc76f2154b31db48552cc67f6054b319f18152cc75e3054b31d70c152cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc6de6350b31b758d42cc76e5250b31db54942cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31eb50842cc75c63943319f98a50cc67d6294331d7cca50cc75d32943319f58650cc75e3194331d70c650cc77a6094331decc250cc7783094331d70c250cc7583094331de84250cc77910943319fd91520c67c64548319f98d520c67c6354831dbd89520c76f3254831db0c9520c75f3154831d74c5520c67f60548319f181520c75e3054831d70c1520c67f65908319f996420c67d6590831cf952420c73d54908319fd95420c67d65508319f195420c6df6350831b718d420c6f76150831bd185420c67f65108319f994420c67d6510831db948420c76d5210831eb508420c67f63940319f98e500c67d6394031d718e500c67e62940319f58a500c75f3194031d74c6500c77a6094031decc2500c7783094031d70c2500c7583094031cfd8e54c873e6395321cf58e54c873c6395321cfd8a54c873e6295321cf58a54c873c6295321cfcca54c873e3295321cf4ca54c873c3295321cfd8654c873e6195321cf58654c873c6195321cfcc654c873e3195321cf4c654c873c3195321cfc8654c873e2195321cf48654c87
  | 13 => 0x5420910424410425514550c38d14550800950005420820800008c08d58c08c02060411430c20830c31030031000030031c31070c01030030030021430030631070031030031005035945140c30d40d40005020850910830824518e40234510a30020820411410030418e40230230a30110820841070030000040000d41451450d10c30c30c30910420810820820820820831880450420b1c430c30c30820820820870001f10311f1c430c30c30c30c3c710c2082082082082c42c42082082084104131131131c430c30c30c30c3c710c2082082082082c42c420820820820820021081a10001021c20210071020021210001000020800850000451c4080084000045004003051151000188045047007007004206041147c710c31c20800004440040001040000c01c70041c30020040001001400051410031000040811410020c00d60030d45020830c20841d40020820111000c00940825945140c35140145000140945020c30804410420c20800014510409009114420000800828c20830414450400d10510424415510554515435550c20a34515400230411409009000020004510820828c20910400550005400000000008c00230150820a30008c00030c41c00c00031c31000040000d4033e4255242cf1095490b2c42552429fd8e5190a7e63946429f58e5190a7e6294642cfd0a5190b3d4294642dd9865190b764194642dd5065190b763194642dd4c65190b772194642dd0865190a7e60946429f5825190a7f63942429f98e5090a7d63942429f98a5090a6e6294242dbd0a5090b6c42942429f9865090a7d6194242db0865090b7a6094242de9025090b794094242dec825090b6f2094242de0825090a7e6514d42d794c5350b5d5314d42dd9475150b7551d4542b798c5150add6314542dd5445150a7f6314542d798c5150a7e63145429798c5150b5d63145429f58c5150a5d63145429f5885150b762114542dd4845150a7e60145429f5805150ade63d4142b758f5050b7a50d4142de5435050b7950141429fd8c5050a7e63141429f58c5050a7d6214142cf9085050b3c42141429f9845050a7d6114142de8805050b792014142ebd954210b2f6550842abd954210baf6350842eb98d4210bad6350842eb18d4210baf5350842eb94d4210bad5350842eb14d4210baf6150842eb9854210bad6150842eb1854210baf5150842eb9454210bad5150842eb1454210bae3150842eb4c54210baf6050842eb9814210bad6050842eb1814210aac6050842ebd414210bae5050842eb5414210b2d5050842eb1414210bae3050842eb4c14210a7f63944429f98e5110a7d6394442db90a5110b3d4294442cb50a5110b766194442ddc865110b7421944429f9825110a7d6094442db0825110a7f63940429f98e5010a7d63940429f9865010a7d61
  | 14 => 0x411411441c20041400450540000818420441c58538610c50000011414c40000871400450459650030031414c11441c00c20041400450541255055801545004e18540161541544c01618541405005140140130800a18620050050005130000820800008615050145145000130940005020a18535001531618611530004d40050134c54c54e18531404d35804c00135000930004c20a18401401405804e59400140005130800a18404d31404d35800004d34d30820930008615141455000145160144e55140004d45130800a18420411441030020820821451451044441041041451451041040910820820820820820820821420050450800850440008848868a28a28a28a28862011411000841020820820830800211000032020062008400030808420060801800110211000000c30801411420050440011410031e21c61c70411421c70c08a24451470051071470025961d60025960848840041d60165800821004471880401450010421c70000c70c70041c81c01070000c71c41870060115800831c00451071470025961c09650c71c30871c21040161000041259441c30c70821041070114409804510800008c00020820450441c10409800000800008c0011002082082082045071c441c70030820820b1031207907907c71908000231c641c7902082082c42c420820820820820b11b11869241f1c64186186c719071e40820820b10b10820820820820820821451451511641e41e41451459071e40910820820820820820820820800852060450800850060451071220078a28861a28a28a28a28a28a21841228a21868a28a28a21e28a28a28a20c30c3c43c43c40c400c30c7907907c71902082082082082c42c420820820862011410000b1c471c20820820820800000310310310310079079001c0907c719020820820820b10b10820820820820020c01a10041c30000882068400030020c02068400c00021801804610041c00c00020020c00011430000850000451070c0c46c46104122131c44186186c711041048868868b1c62122122884041171c440841020841041030048a2c48c40122104104c71100208031c441041048888808b1c628848a2122885100106204005100106016100104104116000082122886201141084c711040831001801002040062040000031062001020061001800111160c40000050440051000000045961041000251041030c20841880450471071020821071862040241001040240514419249809000244510809008c09020829020850414400050440021410649249809000249000809008c09114420800a40820821451458c54458e3091082082082082082206041142082082084080086200862880087080862882004080080844000142002141102002141003041141440084021107002011021100002
  | 15 => 0x8800a00f00481500c00050028024000000000803c00000002803744c8126000010c0ae00a00000980380050e70004026003001808001400201100440ec12904304f8000004006800400e0000030010056012012019400400000580d001000301f801000800604c807000c027002802001e037002004818c1c1000003803a00103d8000004000015800403c00b00a820400009600f800400400b00000040b40081ac00400161a90bd00dc00001f0d68374a9200105f004400000a03d000c00203900e00240241c700d000005e0080178000098012007800c056000020802000201300100f0000009000007000c019018030c07c003014808000201600400a400002e01f003800200e001808c0e6047000067000615b010034000412c014000002201504d80300141ae01e804c0000d9013000802e00703580f80f00a5104101141104104208c711040020450441261000c41082044840454470c04470401450010461c70020111c21c11411a49000c71c4004c47c40c44c440071c0104104c710071c0004104884c710450441001041000840450400c41041618610411c70c01610808451888440458538611c70028451888640619000c58458611451c71048618610411040c01020211462011218441000a11462050448400c41218451441081838610410c30808451030050440001c31411070c01030050401441c58418430e18451430c81a18458618e10808451050062001c50450c01050040000610631078e11618451711b1184104104c711030c30c3c710c30c30c61861b1c441041030c30c30c1045c711040c30c30c2031231004104131c440c30c3c710c30c30c30c0208031c441041030c30c50c01881001430031800031880450430c31040c30450470021c61c7041171c431c70804451470051410031470041c40061950c31008860c31071861c65470c31c40220510550015510435550c48d10111001001010430c40111041c00450441c71880450439241c74400870c30450471c30c30c30020c00c52061070030c00c50060451880450430c39030c71c30c40411430c41020051451441118c41041231511638e31231051401451041048e31440041411051001050440000c01041041841045441030c40225445401110444410430c48d10111880450441c71030c31071862008440001001008440000c50414450440111880011410031041081828610c00418420821020062001c20801020040000021070a18418420820c20000000c00870801070030820040801411000038418418615004c20028a10610618544c00820210610545000130800a10610535804c00130800a10610405808610005130800a10610404d35934c20808610415210015160148615004d45130800810481818418421618615030058441400450541000071
  | 16 => 0xc05e005039000808200208e80540000fe000182800004404a87b401a01d17d869c00000b000000003010d03d022c19e00800480b80040000af803801e0a502f0eac17a002018832802e013064808c01235304b00c84ee00413081e400a014017066001a001000010c00c0010000080116006000000401235b00b01a8e1e001154007447001603c00001f600401280d0394040004862c05400b1230218000004034030c0120d806487fc29c00009a80c007601700001b80c802c0020034004277002806847e01002b80002dc0020338000022029003805022e000019005803c000015800000234c001000822201006180402e80740ea018c01a00b05f801414a00a000826009a03106c000c08400211d06341ba0030010148004003012972804a01016a8068038000010801832204d00c0118006205020883400801103381cc0e802d003005411803402811a000000000f82a405200a0c4800000637201380e003c01500680c4000006002007c00000e039804c19401424e80000023f528280f833001002b80300000db019800010c1d80940010056019003825402800123a001000400500101a403a04419207301e2026064815401808400000c406801900e800402e0000010050014002013006820c00500d000013400d001121000424806f02b801a00001400200780e5028812404e08701b013001a05c0048000214000017804000400700300a800018900500180206600050088028006015804c00c02a00000a012403405780a404c0040008520018004004001811200900280800a801d00600ac6d407c0620008026000064823c02c0140bd00400480d700080000001f4005800000a0110018054004015014001c01201100183a40080cf00181600b601301208bc0080060b709900f6001004802002600000c809c0104fd01f003c10e01f01d832c0960fa006004000a000020810c06802401880f4008007000004407000300203240020da00a000400003c00702e000a0840050284060007042809800000102f002c14202a01680500060f500580502740e500f000053001900006840420310000104000003033003c1060220380004040084000800000008501a00000220000020000010128000008009200300580ac07000f00600d80440da0020030000004000909401225f00000140320dd00280fc00201001f8000000000011813000e00000981a41e20040268c6c008000008804029000100381700100770dd8050054020001800000c00d008807402605900680c009a07f000007000018b001802c06400000001f00ec02900000080da08b0008c7c88c00001d031400009802c007000201c00b804806800b06c800034402500a000401c0031968030004003005006c002121000801843e00200b029400400000080040fe006004012c000070
  | 17 => 0x544b37b9e2449b4b5c21dba69f7a86a95ebe51b6a84251042e8267f127e2886b9e15ec9f03d6bf112657816b2ef624e5a6d4c6dea0545b48ec8f3e1f338c5753221b24ac7ca693abae50546a186fb304c3d0dd6a1b8c22188dc6c8b13b50d44c84b0771cf3d9d4a1a9be38baafb128b53c7bc9d72632c34d966925f348c2ed8ad0fa5712d7bcb8846f7d53db626a27a6ed81e534b1f12814decddf297810ce98fb0aea33318f4f20a7876fb5e669eb0d5a5ac7a4ae2cd22f848d034a3376b24148364493329aecc0094963434ddaa836006a4509ac000201883204242dc002000c2a400020401191104ce176000c0320b00ed00006a837b404800118208201201047cc00000b8b4401e000049019c00000019a8b402800003e800040ee123140008c58a00018b82b400858d00b00040fc17603e008477655d0ab006c20006501704440be06a4a1811000286555a809c0080360020aa43d61de46a00b82fa00300509740120f6012820ca6e02d124cb7419415d07e800004004355f00000001600298af806603a0000084bfc0150008038168638094846807a00201b004c01401301197280242b702b807801e0060009fa400808300d811428a01127a2058b5e162003803c08c0ad061006416600123d0000e4c0020ec00001ca1f0002801c0765ad0f4801c05000b006000956600000480001c24980109a9800404a00180240f2089010000c004557000001801000402b802800600800100e400800601f10f40ce004001927808a02300b011802400b00211cc018007058001c0821e2026003029e04d0af00582862d0012808c3ec672042000000874406d00c00cc3d10e6086009800719180000f032c026897493e0e303c81940006e80a380c80000f400704f00060370a480d40ac6a500580740020b5000800854801700100580201e007f005400027600b0004010007000103032403306a00000000002ce003803200c13206a801c00d000895404254900082140580000120274d5401804f000009802607d00941300071fb05b80300070040038efa0cf033803000e00519400002b005501d8588160039124000000000017c00000000df009811811806a1388020a98a7001586e80043d700b000019a38741e8e34244000001804800000100f0000084010000017802e00e0ea83bc51e00003b80283ec01600080401b411e00383880000021d78440ac0000036000c016003007000c09c0850610d0416c0072b280401c01280258a4800c0420ba00441941700a480f40021a10a680101560070ad802c00001e017811001a1db053005807202b00080087fe09305f013414801304880080b80c90008aa451840b005806c03008209600481420032c9800049200c0a106903c404900685b80040a100080740040c807700140aa01e004884002c01408a837
  | 18 => 0x71d2c78e5470a665683702b60569982b565282fe57aea7a7092e3e7e88ce1cd8b08fce2e14614e56d3919702ad831feedc6293329daba5f103e00c9685450908c9fcc80c367029a19f1e8fa38717599b24789804fec1275c6497baa851d3d800f360abb93ce1fb4c851cf1d44209d3cd7ce09495355d69c23765112dcf176cfa745b492680ab78bb1383bc0da23d1d596f07067db4c1ada494b438bcdc7b69de33dcae6b68c4239629091094410488a9df7861d756c2b2ad86646691d4660b4a1afb259df1b3206af8630c52f8e5c40a722366d810cc7ca14892c9e2d16809d2018d2a9e6d4a0504ba4ec0ce0c410741b65d46c6321590a8e92d10759a248e3ad1d637ccdd3e452e2dc11799387ba5ae9f0520149cb694e9dcb478276520d270ee9f9c5d2e685d6d22e48942b0f26fb690640dae1d20e8bc24d30c7a596355ac4823e5c8cb95cc2df16ec1d7251c228849533182e6db512185a9dd26c591214d3aace45e4b6e0ac05401c9c970cf95a79d9b45da34f8815d4e0a1d2ef15993bc1de73f738b3ac50386435d7da7801680b15ab65e40b12aa484d8822b68a671320584612ba611daeafcfe9673a73d1889135663a51142db93e5177268ad85ae5b36e96cf826ee15f829d26da7c5af0a9cc2d4eec3606071c31a3db496140d210221856df32b21626393972a4b692299ffc817772c9e1b6ad722edc5b6a908ae4880ce55f4a3912444240e50ae43e5b4aa00acf6172656da5118b694206090754529aaf1fd6571678d5eada4f3b4323625742d91a34100c4525fe2af3bada0ce95270827aa5efed6c6d6ecbcf522a9540c0dee63a4981d6c060207a31086ada524665ab059a03289307cd7a39638c0c6d7425565c23959f25dba184a2044f502c0af4579e5519140b844bc100006e80474e6e850f1d8f69349f7b3f044fc63cdcf5f87f308cdd8abc048d55ac73116732d2ad27fcb4014535c567ed152679f1cca45d1459d6668048fd4ed9cfcc6a772b5cb844664a58765db491031723d347248387a31418432384afd4479465c16cfd4843be5ede5935873ef98f641eb3d29bc6045eb9ad26e18a9219a3f2cc0faee3a8ee9fc8c34405b503b663e8ab169cc702a20d366523ac971b342aee9345796ac05eaa01a3069388dabbea1fe915a70265899cb4596fdaac2b87270fdca228c602389b4271b10182812a301fc631366416a8d6d160867055d0e64f0236b4ee5547e5359940d9ac8f389d1431468e4042e9795d34c6b92d4f6933b1ba0cd35a8cfc59d35c0a11d24d0a223013e490a269ee9ee19b46c55ec0f59340fd9b59051a1b516f20f8879d133b81ebcedc38c32d0230bd987ada523e42208c43564104badf822fc097c1688ab046a134fe0b9e5eeb6188c693283b09c2e2c468ca8b370e197829786d32cd4d32e2f99628f491958
  | 19 => 0x445d8377a6c06920461eec32e4fab174400dbac96154cc5253758ca4347c10d0f03155a7aa3ab5aa6b5c1a191805c5e8afe0d1b6144dfb7490ca3e01a00b44ea68bf8b2ca453f618a135c9642e3699520cbddd7e04ab4840614e2d3219f29f2646290acc343c7ee35c93b18381f89ca6f813f4bbed9919551b264d55d58e0656bfa9b43da0a2ea4296aaac14f247d5b613613090ea71032fa3766d0d839ca213cb08f4b9aa8b1891108e68034f8cdaa51ad408e69f936a7d5cc89e744400911aa82c6b37364ab90a700172cb873d6272e32ed4d5997c7f909b1089206c2271384b01842606f0c4157da144308374544b2bb84f52816106c29ae8814e0f6005114b81178ff422e105c5504020eb4e3641aecd3144d29830ab83974ff25c52cd43934f0b1126690fd36197a8092b94c7594238757955e09f70d5ae92049c8ae105b611089349b66e72e8164a55014286a871f45586bcf6ea80c57a4db99a42d37d88441e537c78978317da98906c0f149549712c50c9c9a0e9c1865f43430364f2f03743c06bd1920c8a22e4571332f19f1a9a35df11fa62060f53181b542cbde01f92054ae05d6cc49155c4f28dfcaeb2e8e82c4447ed23e6a70975a92573dfba3f3178069823500e9518fca5ea4864af453037842892889c8de252262d23516a63ee32b9a2d9931a88bfd8f16c4f920d9c7ee41f58d8f5c4bd98e719643bdca57d5d4994203580663ba5426cddb545344eb2a905e8e04f3ce755d132d6bf00b4fc2b41b30092a01334d45d347c71568e9311d1e45abe930b9b3c10a7c862888722aa8bd2acb2ea224f1116ec070b025a542fb06de0f1e06ebbf7a5662755ce523942627c53f37cd81ca066a9b1d66b93d35070799e816044c51e752643de1b6adcdcbd6823ea076eda4eb54050394578201436a6845e45460f8501a4c8af58590c92cf80cab6901d1ff03ce26cba5cef5014483418a2fa2da52a403c428fcd692ced1582e0d33187e6b904de1d918982093e22263cd10d764a1b32dda2c27a056d1f2db5d541a698be050edcd16a5b01d884140c4a33da5150a3720045c549dc2a0b6753f2ce6b28d5bac590b926627d5d402eb5ba23f2c2cee741ec3418cad5c101a9a4c48b9f834c7a98e123b0bccbcd8ad15c204bb4ed1ed18338a50d7288912fd84183ae21883daead00f3509565b18a512a6a23c2a884725da529254a7ee427dca0ea444a846f79a24fed53b06c11fcb6af3c8e7b58d48c7520623351316a083641add3d2e74789bf603b93a106429de37872f9099dc6a221992cf4159e491e88b82d250ae71c927c65658c0819e5c799650475878b7f9fa832f648099a218fd1777539ab72a5e817a43e0dd55521855d9b86badaf51c859e8d0bac9a584b7469101d2cc440d3343199bb27aec4da9fc161e027767dc46d13e16282d5a1
  | 20 => 0xc8d8203459d9f442cef7c1f8a98209d29c3b6520d4783c01ed457d0466cd4ec37269e478308c2e9672cb4f59343c86f827d86423b6b6a14d8990dfc9c86ff159ba15dc294e5fa272568d69211328501e2240a811975a684df56c2478830cbf0989fc2d536466df141cc088b56633a1c2f81429de37ee41315982125f5c08bffad5aa903dac955f1bd420372ae59d261d6334a78fe3c590d942958a281551eef856309b69345e877015b856e3267cb3f5cba61bf93ad0d8690f8467c1a8a860f425daabcd4b4a999f4d466310bd012731f1212b04a4fa466520aa500cd2e08cd5396b3bfb8a3c0873ac25f81403f0aa1a261946f0d352c691f0afe75f99fbcd38dbc8cdb4fc8a6598138a4a6248ed492fc05cf852069c8b4bc39831f11041caa9e9941ad91b98694464815a213db3ba66244964e62163b7b4891e120b68394211c297128053a87848900f7d4ca7916b193d2315d305d2a094932678655349b690820ebc93ed9a05870ee65a4fe8368020614c3b6ce8a6d828056d08e8383c3325055d1bb917a360c0350e3e61448b5042d604b7016693862ea2c8d0f060539c23aa424cc0400190657e5a18ec95d9b7719f284cca9516a64947a50a052baeaaf882cc0c246b56aa041db3382c68550d74ea650ba128ec71910afab4261033465345c4d8cfff7660e028accb3693c9251ad6c757332094330227cd1fa815860c36a0b8cc943b66b42f14d596a26a5be61786a988a4b821596aee22dc6e671f3033ea9bccd6a21062f94bd88d43784a1de69fa7df9df4074d3caa76618721b8b4077ddcd6d12b34661c5a4e0049a2117a08638c33069a96dab1ec08afd3b7a4468dc55e9ce9f6aa5f5f70bb4ff87201341df868abbb2fbd46901830c7d6c0b43b0e22387d69a32958a2d050ae14415d77319ea726acd3d112d1026126ae71cda78535f8d0d52cc4464b5c285e8f8b2fd5fb3bdd2d213b701ad6071aca5376bcce484b65a27adc87512943305ad9c68df8146125d3f84ff8e3c45ab3631d5ef012dda262027e43ea2ccf0e79ab375686274885d4d84f2c1e950152025cb0683ac558dcd09510739b8b4efb471002f21c00b0aa493ca752342763abbc00c5916a21970facd20756118d858400654c1c5d6f237584c4398c93d9a9a2a448329527953da25627c39c02cac37499b5bcd44db1c70d822d6f90ef01044d88883e7676165a8c8fa0333b534ec53325bf00296b089c9ba290345a14ea7b6d98a5461ece31012ac1e4b49e26daf7067addd27329d8c2b0ca54e9fad3c40e31b14899b953c994ea46c0a86e147ad62250936746553501ec1e323a01e18254387d20926b28db183d4b0d9d0c503a346ba69659619b4ba249c78d5cb1a118951aa9e91f6e304916777cc46aff564578393110b1b18f997755f72f61bdda8414514e7fcd0f15f03
  | 21 => 0xfb06ad07d008911f78d5549c523101b608b6160ed7010916a52a94a530b7d66ec0ffb3831c67c13122a4a1257a96c51159ce467541539e55f053070015c09c1e98a808b4188531e3375d4462973b2e62f535d593e8b63152a40d4d1e34e0cce9404dcbb4a98e4a306450ba3149148d9e0531f359f913e859bad25e54ce6a1309a3a531c5b01d14a9ec3a8ff5af5a94547a5d8e3852926552244b68b2b363f4d40e002d6e9f983f50c11c1a3aa2aea1f03e0c59b49dc90203d6aab138b33d65587418896b84a4409d5f33bfb578fee1c8ff5964016598485471b55695469ce2aa4bfdaf47f86d14241494981a12c4281525e212104b5e30ad509aa7ac29e112774b73ec856c4192ce3804d5e132a53ec4e657ca7b2092b2b370104d87ab8074b6cfabf1380f992c133284b71b05443ae58b61f6698569187ca7320b0cae7cc9128f710d906e1b87a4152c02b07faf125b4b3731e4649ee68915624553434810d4d86b4e616fc5807a213585fedf71bc05aed92bce14dd93a5143a4583d689086d7033921f47f85f89419da9f530ea594bb0c0b6d967182428ee11ad5d12435adaa658a5cd04eff18d178cbec1280282e63226b5d4a92e4039153e6a34379d9a960d7bb5f0fb261530c6120e5ca2c60b7dbdafd406a97a09a36cf5023bac5970211a51028282098021201b943a25043f49ffb11694cdc1abda7c6d5c73b8eb18c01a0493840417cbd2c8e0e093720230125c08e5a9d8ff18a8ba40f7ac7e8622ff441b46a11ed7c12f21027c043b1066b55017335dc668beb37c020e090073012f0a6e8a829f8d0761fc7af7e90db99d8edb8cd258a278f2807a3cae42b3ac88f50d189ed13ad981e8544dd4b35a3a62bc4ac69e9bd1b7b2743c8bf9443f2b891d2afaa3f3ee148a794524755a5aa53c3ea26a6e4280145ecfb28a2ddcee86cca928ed003b403994bbc893c31ba251b2c5f508661586706d0960a0ba29c3b29a881418bcac52e95493502228a308903e9ab0d3e50e20bf995cf907123420d4ebcfac826a9f8a13d0128219bfa3fe667999c8b16a30e28bd5cfc82b00094c0ebe454acd3b39bf52d551038ca488df25edada9c1f3f216e18adc5676002bcdddcb0ce9930483ab58bba05b1fcecb9612b2a3818170ba6a3b2108b8a3909528b322e61a24a391c1ff953a44d3a768f4f39456b5be43acad4b314d86ae31a8c5db44125542ae625b0be84816c618c6aa960a85324ee8448fb4dd9590fd050d7382a30b208ac34526002c4ad983e0051ab0a09ac0553aaae3013791d090c752381935cc9ca4067f9a0fd471304425a34dca4d901b2236602ce992a24cc5a630776420f5202a6fd22bc2dc64414854396a6262eed51b8874edcced6a8a82e4f2c6960002e91824922b54e88df84da0062e1212ccde13f31ba810f292545450c990e61703
  | 22 => 0xd7912c6a10a99bc9e2a5299aa52781bca3b51e64f5278002a608c65a302f9da068c79d6c4d523baa98393488914d1ce37a7334daa965c3105d7e23918f622a3a273dba2912923c208213600de478b3ace4cbea866c7f55d8f9f149bc8054324d2820c11db8f5c96e588158a768935d55860a1fca59256067e4b9714300a52c8b813158d044ad02223d2aabe80e623db2223d8a747b11ff58cd0826cd1b582fc20a443d6bc70404063f8ec47b8dba028964a620c729a03b059328ff88194561fad034283e0d38c7a94be55b66f24295da3de99a06f9b60d6780e09fe92a05dd69a2ec8424454fe8daa802499caa638360c9b8a4a443834a81b0b7c8319e80d7518709d54b3e2904b2ec639b26d4d80b456a2dd64aca352b29d2a0f0ee8288b792782e8892f54f5a7102a95aa5ecb9a52c1370524fc6ad29541a0cf2f409a630b92aa6e1a89091aa0de7e202c32629bd567903d3e4a84ebe90bb8e25f855a25e39a1140a4c452c245240c4ca7f84fc3403d093bb4847111f90d455112d03b00b234e93308ef2faa2ca78ec4b7bc4035d186187c4c67a72433b94f4e422f51a640c28ed8096b45afdab18bc67d3c404a01641213548a7a87ac538d940c64007089162369272e4e50e50384b0a434f723f90f485b4cd2c5d3e726a3920556ccc848273a41dd5c61e25027d106a2bf9c49c4c5a002c38f3c7cd56c785bd4b6a2a12ea9b0b452032b8e8c8293495c8d543a11a00df19d63a2a3401b6bba24b83091400791a5135e940092022e681d4c606a2d604e8711d7601048358685ad4c61defd6aa22e9e1c9a8bb304e416d2ae0106182ae809b5b207926c8d8e90e624d5bd3ae8c71a627bd3c25d813485d59eeb615f04cfcf3688c6c9d564a143c459ed7092ee3ac16cc79e4e10dc2ba283c7124b2218ba2a93b5ff13f809cf4800f64918448e54ca381b4ae7dea4b96a4128e288e61945461a480ce32848617d64075e52e296732a71de5b204a9093549850d9be4968b236485ce3913e704a60d667697c05025dc5e6b65b91059066f99f2c1600a1e1040104cf6c9178e2570c35c55554a9f764054e2b2999123c4e785b8847595ed41a10d626d0068f1c92da5d490b49f656089542e86e824d5f7e11c9ded862208f958fd06758168de3b6d16c84a715895a1f996470c3a623d89080488b520bab74ae01ce0d4a6645b16f18ee0b454528cc862103a57faf6022993b6963f8d51955b5d97d4398e3562564f32e1e9753158353e8ceee53a49ea01229ea0a54d9492a4c3237fd0b294dd4da2e817180112d073d56f26724764192d214cd5ad160888d4d0fc014695e9af0614a0c242d41a8e471306381e693730e0e826a6f0f1523071b40b2da1799cc488c2a3f60971a5b4dc6479b407fb24b515180cbbcb898541a583a7579a9720b576502c8be1a3162c
  | 23 => 0x30b88d9c38831e883b132b7db091a26d4d9a9104cdc2d6877550a31844cb69e3b41615ee944db00d1e84caef4d4344550a943d631162ad00bf59e06bc4f44d2056d25ba4c4a32a02084a938f605be47d0df1eb111cdec6d5c32e8488a977e986524f65a78a5252884d5287dd39116ed199f1a6e4ab71f597d303c59c6c3703cb64d9c34160d25187955b02c70dfabae473b542959fd0eba6582d527892cc93d991d2cb047ac90f90c794445d880c61d65cb97a42c43d4b1a4d3903a2615b893f1a50b1f11799dbf38592d6cadfad2867840c1445b299fc27b94084f04651403fa87017494be09907559f4c2838b9e64cef34e0121ac4642b6e94285e022748a8e829c8aae43c9db2f7c6fa2bb85f02ba814a0796dd56c1d905246ba1e65e153e56105b2a246587a350c96012dd5894915a4cc483ae87fe7bc84d0601e00da2d8711a845c39ab643cb03eab6e11020e8e9ce905fd9daa559ca9583b488109ac4cb96cc194d5449d18dbbd51ca123c340bc2c8a085a3f705bd6191a92f844fd620df41e32b5c28b45d4401c6e8bc6bd8031ff8e611cca394ae9a6679e4ad8e94cd0d76b080d3a20c2b1a769c942e701f5f0ce1167d650206b8f19272254433bb206b6222389574d5d1d39153245bd304c5025a3093323599227f59781f79ce15cc4b4a554e1443661c9a6446a5ca87cf1e35f9d10ee6f026313f8190655265c1cb57eafcca643ff43fa9863dba144a9b2f910d8afa6aed866dba75ab9ac8da460cb8f9e75740f9ac9ebc3fa60fa648b7863831a0cb22fcbcc87ba3b2d2e116224546d3054278ef06c5b59520b1b26349c6464b364b3802c93644a13192b4aae3ed10c95521bd0af020c06c9908529d65d9e02f8ebb0fd7785c14cfaef8e041a462a9209eed1ce11c2b1e11e9331d707b0c7e94d986c4e1bc50974bb3b5458f6404718d0ea8a93a62c2f4c53b5969402a695394587b019d103359fa32472273f21e08cb172c1c06224017663b0db295b2aaab2e6627544eaa2884b5a5626f67c32048d03c8dfd4a3eb32155982b363169ad45d376ce74f17ca3d30ba59c1e959ff55e7ac22795dad8aaedd639dfcbc6411356643503c14d09decab5e6580cf0c210b67a94109c2a4a3635a58e148ac7941f4ee60ec01a98dbe821bc39e597846e83cc054940dbd9e610e8ee0c9e8353ad5f154c1dd473e2f6cf3215325070148c12226487e7cc2eb8e8157a94f34cd895335821588d27237edae6dd441ce5ada0b255b3ed999993d282f493bdc9ba5a72ef39e86da706d7c45128b17a50643be4575e4292b1ac18b2c96fc375db90c1dcdbf9b9515db8e5c718bae08632a677ce0601bce7c08f295984deb68a8a950df0f4000ff5ae88023f50a0d205e195c940a5715b882f48ad50cea0ae6094f8faa588c9e64d44986d4ffb056d5de462022465
  | 24 => 0x1485026615380548d9e0a7d297898caa0d5f59654c1ca9932f841c4ba85ac1301e006ce036a4a94d920db4a8a7d13c71e326087c0a8483b43ba2479186bbcb4c950d5821f3070b2f36d2c0cb5a5af3a114baba7144b7b4d3f05e4fb3e197df5358f22c8583a01c0c3b6063009c744e4c3e78c70b1095b48b8734756dbc01a90411492bfb149ced23a0897980c561a6b90fa6fd44caa3b959e7af5618a435124c71a33fa004e81146009a4f1114ae16eacfa1542f26032351a4b139e2990cc5b2800489d8496b436784d79ba4b48d0957fa156d3adf90b40ef8eeb08b184db4a472ea7b6944091a080e167a00a2a85b4836c2bc3be3aa7c62c75588e8eae22f922c66f650617b11721cb2fe4eb953cb448fb13b14fa90c511b3d57733a56b4b5fc5ee60da3e00e14565063c2c7e21ed6d2ad89eaaae11e138536c06002961e426f10224987bfa0d8729431b691cdc62361c8df5b48b356581aa0a5dc910852b1b656c04c404085b491d0ce0b694f29cf96d2a08d064f033f6120c27d25b3885e3d17ead499c52da5428384349a8adfc611569a3759f85de1ca709da123308977613f40732f6c46907b9a3876275837664947ae1714de1d4a75a84d9fee4e457830985b9a1cab6b690c589d56d264bb4a57262c4433d3012dc7dc63edb4858046b55ac309df93a07d940005aebc43be87cada531a82257a11c4b861e91ead0886df323443c624a1656558205dc85e9b234147036d238c3d9061d4eb90e1fdda9e77898f9ab59a6fc921025bd7fc91437f50e48ad119309554001cab70acd5ca7d54015d621305b0e142875b4a2f116b40f11826b28f7691d03e526bb77ad2b7aa6ee767eaba1a4202b457ba61622356391c4a693b20022a89ca0cd25b04ed2ccd90a4a26a652ba1ea51b585cbf8d1cccbb69308243741427c14f66332cf06628052e10036d43e523a2501ace0f76acc1278ce4b243c07e63358f663b6ad62474fad90c8f227a052c2ad3361fcca3445d1397ee0ac13bf6d285e5b491d744b06e25fcff500c4c1880196e60a3b4bae03364c0af701495569d3a401630bc2fa71900a00268d5b78db2edc3816a6a82f9e64f6d2b692ae44434f43249099072a5c91437ae16c6564f253fa06e682921a0a4ece845b4c311e8a36d27004cd655200a08f2feeda47050f2a886da46c02743dc00acc432a2b9711506af5382bfa55f59d07f06624189400445b49c7d4d6b1d0d1a07043a89125458eeefb5a3d8ca944a4903b0790fb27e4a060965e6334c40da68cf3f460036c46a7aa2af9c2814e92c2f3152bbfeda55fc5ab8e125a44671ffa410f8852a6ba0d66604a285df8c366316d22d9a7516ccbd683f5b488b2bf0677213ada4e6a316db4a016fd662c819a6a810a8bb059662e675b4d193aa2e0297965b48b5c97a96899e46f46e5670cfd532
  | 25 => 0xd90d2b1f0d269f516e67b07089c1630851968de65358a56ccc093ee164d4a84494c2aa78aae3118c4e91c2c6b058b45c514b4b13276c21d329492a8cb60cb56968369ec451a14a069509ae88381abc0a456408e81c41e97972b94fbcaa0aa64d496d7482516b034d9536c559b9b05f2fa1633975dde84a43d0d1d18da8f875ebd393a09315b181a9b46c2550ec7fe8ccd7d41e103ece41705dc4af149ed6437750e88fc3b38adcc9647f1cd5739be20814d261e0182750e0eb220561604729259b76a76498934d4fe4d50de08fb9cd2a5a2365ca9ed6370f0a4e18b5683e58b2f21d353ff2de491cf44e3e7ff54a12ea564cef8c9d76a258a48668bfc9f90b926975a7d19841560530be4826870fc21ee50e7220634b84cbd51c3c648cc418d2a16f29fddea59509f26ba5da6a0610a612530f6a9b321a9f361b0850a78c9b01c78c4c4719f26f084538296f6b983cc547aab813a4fd36da9aa99e05f28e850322e2d308c150d2c09192d4854c901749c828f248285f30fe17d82ac48e22d146317b07c45d52b922408fa48647a04c8bcb050cd4a75a52259218c12a2ac102a6d365619ab686d6acd59ccc198f7c50b0a60b998bb0a0a589be81df454a9e31b085d13498b0ae5bd0793923cf92346e4a87997fd9b09551692bac2e55a3b29494d1ca54a6fb417127d4d06e15535c0259c113d2bcaeafaf97216f644f3a45c821d95a7662877ab38baad4302f17ea68819e8dfdadd11286922544a6d66cb100c3c88ebd2b06eb4561fbf101934be4cdbc1002d91ca8bf24c8362209d4c4e65b4a26ad51205a2f036b4b9c41a5ed55946b400365603c199d06084d5041c5abe5635287df16b509f3afddaaa59448ecff63bf3813ce21b8ae1186a961374c3656f7e151860661f18d7988e31902498499644a4b2e6b2d584abe9736ce26de29afe1ae0d2dc9a071231f3b252484e29b73a8453ebc883e90865b019442321c09dc3959bf931012c5b737ac5a65847353b091491a2f0887e2c91f58a27248935d5d32d663b2b75a08ee20ea134cf7f5d568dab8aa2c87f48fc63892164c51742d45d41e80553798d0037167945ded0c5ca141035a0e8a6ab0d40ac1203a24e41ec02d358457a3abd0553138a9d9b50b21e760600cdf5cd9b174c099110c27a1608f27354788601628294286904147215b14735c9ba9f221fa23cc3304583cf5cb8c2de6148403f13d93981306a485da95669b7f22c9e50d1ca541ab4630abfa963c0e89fcb2042c12d85f716c24a53c1f756d0a11cf7c79aec6317541100ab034c626b25835f75d55476a0e02b80f2ca9f946d35fe3b41ce4e641d799847c48939dd8dae8404248a50ab4324a40a5a4dea0353017e3a2c0fdaf2da381d95e6c59976408a91620125b69eccca253e4e6ccb8716114aec3448fa669d0b3318460c9d273
  | 26 => 0x79a0a3ca8807cc80398a02128b5bd608196d43c098a15448df8c28f6b349842730f833c01de0a917457b23d0e125af1bb4f71fa76d234855a06e94b37cf0b96746adcb690540f154043702ac8c6c34a7f8070c93b3d6aa889e1c586425f952f0b7251a59e50ee7156d2344353957e33839926911be329965892e119098ac8c41cf784ca16b257e2209c43d3a03d0ccac36b09b71c3c1249d7cb9d79a2a018528fd48eb830342d71e20e808398e69ecd2d7901a00eae895d666488062ab1174e3e5e7189ad4cb94b48ca8300b0528e87e3503d92bc4448a6b64522eddb0d8f2ae2df173266e7fb524897d62a1f423b885f6b03f02565a228405bea532bfd14534b8c71b16dcc04d2e016e06a43269d41d04aa850c0aca24e2db7ba444d25cca0855bce08
  | _ => 0

def s0K6 : Nat → Nat
  | 0 => 0xa417451483fe82907f90520fea0a41fc41483fe62907f8c520fe98a41fc31483fe42907f88520fe90a41fc21483fe80907f90120fea0241ff30483fc6090778c120fe98241fc30483b860907fc8120fd90241fe20483dc40907fd5020bfaa041fe540837ca8105f950209f2a041fd540837aa8105f550209eaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107f54c20bea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041ef42083fc84107f50820fe21041ec42083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041de30083fa60107f0c020ee18041ff20083de40107f88020fd10041fd20083f240107b48020ffa9e217f53c43fca7887794f10bf29e215e53c43faa7887754f10bea9e215d53c43f8a7885f14f10ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ff21621fd42c43f885887fccb10ff19621fd32c43f865887fcc710ff18e21fd31c43f863887fc8710ff10e21fd21c43f843887fcc310fd98621fe30c43bc61887f4c310fe18621f830c43b86188760c310ff90621fe20c43fa41887f08310ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ff98c21fe31843fa63087f0c610ff90c21f721843fc43087f48610fe10c21f421842fca1087fcc210ff18421de30843fa61087f0c210ee18421ff20843fc41087f48210fe10421ff10843f621087dc4210ffa9a21df53442fea68857d4d10ff29a217e53443faa6885f54d10fe29a21dc53442f8a6885714d10ffa9221ef52442fea4885bd4910ff292217e52443faa4885f54910fe29221ec52442f8a4885b14910ff21221fd42443f884887fcc910ff19221fd32443f864887fcc510ff18a21fd31443f862887fc8510ff10a21fd21443f842887fcc110ff18221de30443fa60887f0c110ee18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021fe42043fa84087f10810ff99021fe32043fa64087f0c810bf28821ff31043fc62087f4c410fe18821ff21043ee42087f88410fe90821fc21043e842085f94010ff98021fb30043fc6008778c010fe98021fc30043f06008770c010ec18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043f220087d44010
  | 1 => 0xc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421fa90843ed21087fea010ff94021bf28043fd50086faa010ff14021ff18043fd30086fca7987fd4b30ff296617e52cc3faa5985f54b30fe29661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc2faa1987f8c330fd18661de30cc3fa61987e4c330efa9461de528c3baa5187714a30ef21461dd428c3b8851877d4630ef28c61dd518c3b8a31877c8630ef10c61dd218c3b843185794230bf29861ff520c3fca4185f94830fea90617d520c3f8a4187f90830fea1061fc420c3fe641877cc830ff19061de320c3fa6418774c830fe19061dc320c3fea2187f94430bf28861fd510c2faa2187f14430ff98861df310c3fc6218778c430fe98861dd310c3f86218770c430ff90861fe210c3fa42187f08430bf28061ff300c3be60187f8c030fd18061fd300c3f26018774c030efa9061de520c3baa4187714830ef21061dd420c3b8841877d4430ef28861dd510c3b8a21877c8430ef10861dd210c3b842187794030ed280615e500c3fea9907f95320bf2a641fd54c82faa9907f15320be2a641ff53c82fea7907f94f20ef29e417e53c82bca7907f54f20eea9e417d53c82baa7907f14f20be29e41ff43c83fc87907f50f20fe21e41ff42c83fc85907b90b20fea1641ed42c83f885907fccb20ff19641fd32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83fc43907f48720fe10e41ff40c83fe61907f8c320ef18641fd30c83f86190770c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9107fd4e20bfa9c41fe53882fca7107f54e20bea9c41fc53882f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441ef42883fc85107f50a20fe21441ec42883fe65107f8ca20fe99441fc32883fea3107f94620bf28c41fd51882faa3107f14620ffa0c41fe41883fa83107f10620ff98c41fe31883fa63107f0c620ff90c41fe21883dc43107f48620fe10c41ec21882fca1107fd0220ff20441ff30883fc6110778c220fe98441fc30883b861107fc8220fd90441ef20883fea8906fd5120bfaa2413f54483fca8905f95120feaa2417d54483f8a8906f15120be2a2413c54483fea69077d4d20bfa9a415f53483fca6905f94d20fea9a417d53483f8a6907714d20be29a415c53483fe86907f90d20fea1a41fc43483fe84907f90920f721241fd42483da84907f10920ff99241fe32483fa64907f0c920ffa8a41f751482fea2905dd4520ff28a41fd51483f8a2907d14520be28
  | 2 => 0xcbdc6599778cb32fe99665ed32ccbfea3997f94732bf28e65fd51ccafaa3997f14732ff18e65fd31ccbba63997fd4332ff286657e50ccbfaa1995f54332fe28665fe30ccbbc61997f4c332ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29865ff430cbfc86197f50c32fe218657e520cbfe84197f90832fea1065fc420cbfe641977cc832ff19065ee320cbfa64197b4c832ee99065ff510cbfca2195f94432fea88657d510cbf8a2197f8c432fe98865ff500cbfca0195f94032fea80657d500cbf8a0197f8c032ef18065fd300cafca798ffd4b31ff296637e52cc7faa598df54b31fe29663fe42cc7fa8598ff10b31ff99663df32cc7fc6598ff4cb31ee99663fc32cc6faa398ff8c731fb18e63de31cc7fa6398fd4c731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fc6198f78c331fe986637e530c7fea418ff94831bf29063fd520c6faa418ff14831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ff98863df310c7fc6218fd8c431fe98863f5310c7ba6218ffd4031ff280637e500c7faa018df54031fe28063fe300c7bc6018ff4c031ffaa643fe54c877ca990df953219f2a643fd54c877aa990df553219eaa643fc54c86f8a990ffd4f21bfa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ffccb21ff19643fd32c87f86590ffd0721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fc6190ff4c321ffaa4437f54887fca910df95221feaa4437d54887f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887dc8510ff50a21f6a1443fc42887fe6510fbcca21ff19443fd32887f86510fb0ca21bf28c43ff41887fc8310ffcc621ff18c43fd31887f86310ffc8621fb90c43ef21887fea110ff94221bf28443fd50886faa110ff14221ff18443fd30887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43ff31487fc6290ff4c521fe18a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ff8c121fe98243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21ef298437e53086bca610ff54c21eea98437d53086baa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821f721043fd42087da8410ff10821ff99043ef32087fc6410ff4c821fe19043e
  | 3 => 0x3c0704f01202c0103400217c0100100004800023000000120240020249a805044242c4248c484246242008324624200822463109e21014848c40339c008c40239c008c6212162121084210118908020c918908020891894a5314050842109c8720421084a50146508425280a2284212108620084084210848421024084210908020c81090802088108423190601800009421084210842118c0310c21084a521405000010842108c2108425280a22842118c6600c6000c7108cb108c7104404210848c4831c62318c0310e3138006000f1080b109cb10440339007010e08c48020c038c40320ce0000478c46018c6319a2118e2119620880e4390f18906318e3118c6318c4318c1189084310042442421411204242441100c8421004202312100300c038c4031908320c84010448c422110401000008421108021882108400000210842108421000010842000000094a4280a00002508421094a50146509421084250000008441084212800500005000a00000108442308021442211411104221441101084200848c48210043100000023101084208511444238006000f1080b109cb10440238087200f1890e000067000000462021c072008200a208800220842000421084230222084428844228220880e401c043c62410860108420000000011880873904210a228884210844210860108001091090b109091044022008421091890840106400000046202100421002008028822000844208828844228222084421084410042000008c4038c40300c02144511004010842884658846318c6418063000008c4021c62318c63180028822000802008628882110a21108a0108001084210880000008c4038c46318c6288a221084210842144202c4202800020000200000462010e3100c00180031022088000008020084318862beaa485ff5390afea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fd4390afca5217fd0a42dfa1485fe3290bfa65217fd4642ff28c857e5190bfaa3215f54642fe28c85fe3190bfa63217fd4242ff284857e5090bfaa1215f54242fe28485fe3090bfa61217fd4d42bfa9a85fe5350bfaa6a15f54d42fe29a857c5350bfc84a16f90942ff19285fd3250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ff18a85fd3150bfea0a15fd4142ff28285fd5050bf8a0a15f14142ff18285fd3050bfea6215fd4c42ff298857e5310bfaa6215f54c42fe298857e5210bfc84217b90842fea1085bd4210b5a84217f8c842fe99085ff5110bfca2215f94442fea88857d5110bf8a2217f8c442fe98885ff5010bfca0215f94042fea80857d5010bf8a0217f8c042fe98085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332bf29e65ff43ccbfc87997f50f32bea9665ff42ccbfc85997f50b32fe21665fe32c
  | 4 => 0xc2bc15ef2c410c5beb4d3aaf48958eefc6f1aa7f8175fc4313f290f55d4982b2c59e8d96cb2ee3c4985d55d7ae9d88ea79fd8cfab337dc5e05955a2f2ed7bc62ac1a1fc392748135f1b0ee9aa19e2b7ce1f69de0f6a8a60fadc823534adbd9bff3a2b6c68d79a6becd93d7e1fd250f0b2138e10a6a0db0db3bcb7a050ab42a1ffc164eb1b11b66677f0e0d67bf810abf0057b804e429087072bffe1faa20729c39c1fe57e836c2c8290881edc418832d4efb83bf3d0d1d33272b403dfc6aa4b21832251f1ae16989164e5a491a5030d6ef1612689c9f2e1ecfdb51389db3f907d4f583917874af1dcb826e474fe1b707813e435fc0fadefca511e1304d4fc73e750433888cdf878839c86c9a2d0cf4703dcfe9f2102d55d936d3477050affe0177f86cefe14f3f85e2fe1fc185953b7c7b94627c950d1af2ce6ddd4024ada7fe1fc15146443987c920e069fab4f6a2e12c832a6a0dc2888222c4352620bcd1d50f38ca41f98ec98e3c52bd61d0b5354020d15dc3a5b9ad4b644e24a93772881533ab7ac3543115642b65f2eae30ca50f2bcb22a2f2025e5144da69d1394a2ae29726645bda3d4bb80058e081c7c2506d8a7bdddad25bc8f4e00db5c33b7f1924cbf1a801c03cd004b012050033350700a0515450040040cb4323e0b0190001a600001049004028ab0800901b8020051122c82281d0182c4070ea0aa008001dba0e5c02d007da2b2c3180d0180001580111407041bad0c644c0a84031c010238e3000020009f302c0001607400017cce9ec50833c1110200488c090700f288ced0173ce0002f17301a01c0280005230c018022b40380007300c1e8040540740788200473465c1200200e0000000801e1c4020201680d80d97f0720040a02b4aa08001a3607a0341e20d0a03f40001f1ac0080c98206a0dc1a0c50e43bc098631060980d847000000198000040300a80100a098088001b200078814014054078510a6050188000021c4000010360202d8300500d81e000076498078490060b10d01202201011802008c202a8070280e9af80f0900240001c01c01c2682604a03c0309b0000044f9240000bc138b500000c0904206e19c1a8340000004a22502801c0580300c010150042440241282e01818c3d01e19c1001e80710803c4100215c0000000500401402000000008000031780380903205a004b583a00c368020000545d4168e9002094068070420002b82617017c0c8040060e80405f030028018000000000384e072010190370be0d4000390261cc318b101e01c0083b00030c0382803e00c0383616c0080e0070020c00709e0041243701803e0000904c01e2d02280302e010000010000b00083c00a000068000001280000a03e000008000001080282002c5e87b01600200c060020400801983e012114008ce0040180001400
  | 5 => 0x44045b7a6f6136ea1632c6a7d0a88ebe7f0fe03083b4236df1a9a732cbb0e8fd931efcd58ee3917c0bfc3620776bb48bae7c8fe0a157e510aa280fe8050f47109ba6cb2903e42dcbfe28198b215ee17fc09de84b939e0f425a626dfc869205e8ba666ad3db7cea9222cfe0eaf88b34c84800f8acbf3ab49ee5064a6153f84d9fe1f5417c4ce7d16d657f0a5d979abcaab79e192bf5004d7c3f83804f3d7b406b5d45cdcaca38a62f4925ed2c06fc947333bb7b8dac0389a532a5a43848102bf85813bb892fa57e23b107f87820574ad97d64d221aa6db67553f055325917d6337cd3d44ff1cb9cbcfc301571d6c98c37ceccbd46a8e64ca428dcd47f83414c16eecfff02ae69151fac6c3045261a9ab807b130ba24475df260dbf8108f8546525317f874c7a87b3146bf1376da532e2141618ed6e23d3b601d48451b94eab5ddd7cb350fbb38b988ae78119d9655524d82f8827d2125bea70bf5a7a13fd517d3974cb092428a1d65ed6e3343fe036136cfc6183df97c80373b1f5e7f09e1d6389dfb3f78d8d53c0649424e3219b05383cf4948e71f7465cee5a001361afd4a8bfbc6dddbf25d720bfd7a8b4aa71c116a0ad35cd742c54b77c658e611635b7734b3a91a4172a958f21dc8181fa17afe7cbba8e8b6653bf0f302dbb0e2f5430bb5ca51088620f771119e9969d15e7902edb68d4c93e6cf4c640189bea70581e52ac5cf0a31d76a2d43f66eaa7b38e9cefa4d217ad084156c893d56ec57e704a3ba19a4562dab4491b87b3ebad1a48c451131d36fd48518cc37984f7eed34362e045741cd11b900628f9e7c854b9784e74aaa3b92f7cbadf16923156b45a42eca9d4b758641acf10ba05923927d86d3f255f14ec2ec3697a2c872cc586d5afccb1cd28ac05bf13c5ee8c31ce3a4b038146f67650ce4187157ca4f281e3752dc12f7972845b86c5f09051d334bac5740261217f97da94fcf05d5877d515e9034a83ed4af7a54d83f6c0e91d3feca035cc4e5b9c6acea38446c0659477f39b3fb9dab59239c40fabb6a4301082f5ddf3940f21f6ab81aaab6b1f7295568cd848061b6bf71f498463a6b1db562ee3604d79b541452701fe0e5bdc5847f1020976d5d43bd34e84f15580616571278ff8140606142430cab9b3b0e9e5c1d765bd6128550f966cf3519e8c0a9d71abdd2890871706d067587b06015575334b2a3d766022846faa78e6b8d23d19b273845ccb639b22255195993288760730ad58dbadada81e1864b45d8285cd2c81dc77f06dc071990357cf9c3f8486d1ac1e40ab3c2d23e86199c7d4faa4276a72b72a94718627e1aacd4025f6243daaa776b919155040e3d3a64add8a65ad89a868e25acee6bcc78e41373df1efe3b8c0a1b6cdbb6985611d935f92cdcf36e108ae0953be667ea3fc5b972b7e61d9757fd64a8a25579c5
  | 6 => 0x193e341d6460bfc54872abc6b6c492633fa821b3621ea6b392ba24539f5bdbcec611d4b899eb515140b48eda7a1da86024dde877ead42d0bd6ed1192d272070c7e8b4ee8bef35f1c5eb433204fa106f68b85e3f378f39392023d277bc488f188639e4e16e1249041d5940c45c4eadf2cdbf7a62d3bb66898a641b9da664ef9325db0d4a88ef13de0cae4ae2a055466de5b8fc4ee95e719bd2feb53405e56d91325ab2c70e32684a106cd664635c454958342d4a2a8272d6d12ba14d967577d3b2481910a3a4eb6d65891ba028439a1c93c0a7193db242539f0f450ba3721a9347fe0010d2fd2b333e5e10fbbb8cf1fa432c9296ef26bb6c090e097a8370db10232a6347dabefaaf6d01cb34e1fc6cb8516f24aae93bb298d27b23f838896e8f02b9a32ed78c8d2640c497d747f008dfc2fbc8c11c232604a91b40cfb6733cb87cf354fda058a823e997177a54de9cc0c373f0553def81016d8f5f72b9d2b63d85ab1fd302d3eaef4850bfa85c9f0d973456bfdd4b6162704013a03a4828f3a175fa632496f370f6827fb3edce061e4fc0fb4f3cc1294f6ed6b4bc4842cc49981fc431fc2c2c5e7724c384e82a61d827b23bab1fc2452a5223fc18f891c7929e6ff2a62f5094864841617b5be43857079c1cba22c3e1312504dec0f68fa2ace61b99703d73fc2b04fb2d9954401bcb99fc2d1f6846da3c7958eb168fb4529f1249c9615ff6d62135505320d748c90fcfa3e81b8b23fe1b04227020b512bf83482c444902c60e245e7f62d79e5aebef1b247a59e9b472bfc14684132b35d9a873949aa5ddbd31b81cb0ef88b3bf2022888fa956eb16aa4fc11c924c006bdc56056269bfa1edae4a437e6628b3e8599d8704af63f3a0e778ec4bb08a04d98e89fc03d7e7fe1fc05bab5fe0ce7f85ab23ef233f8ffa397a9aa2f9cd177b91d04a5b95e68ff0656dc9d4d414b1c55be2011d0ce05a9bae50e3308ff0da1874f287d2a4a1ff8694d3505adee7c7328dff851be2e99df0300abe6ee855b0b7516663ee5e18944675c0094d2abc1de4053068954c78e2a2621fa535282967e4632531f34a1bcf704f5a83d99fc267cb041ded31772281f322d64b880d38e150e2fe1c35823b508bd0abfc3c29d62b235d4dd1fc27593f9f1f264e95c028f619d73c3ff7cff6de0d4798bd72be49185dc2a9543bf13ca56f0686b9602804f07fba00a783e7aa518cc27438d84291e7bf09bb89d4a45fc160c891097131bee11a9a2b839dfe0f5bf80b9730653b9309b97db61876eb4b1f2237ce541e00f090045152b2d2d11bc102b3150aab8014b3185bd93198b645b5483938e5fbf686abf393a0b5aa181018ce40d3fd79c91629bff0602ca1df5fafe069aa87f0fe11581223437bd3bf8672b6318865478e153eaeaefb723fc177af3ae7fc23fe47a51ec34f3
  | _ => 0

def s0K7 : Nat → Nat
  | 0 => 0x7a16898f5cc59bc474329d48c74574e7404273bd75d4dd1b1f5d75d75713d71b65d24f97674b41d74d75d75d75d19d75805d5fd69d75d75d55402000038100100010c1981400fe42fd42fc42ff32fe32fd32fc32ff31fe31fd31fc31ff21fe21fd21fc21ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0

def s0K8 : Nat → Nat
  | 0 => 0x21f
  | _ => 0

def s0N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 60
  | 4 => 676
  | 5 => 2921
  | 6 => 1016
  | 7 => 29
  | 8 => 1
  | _ => 0

def s0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (i*71) 71
  | 3 => packedAt s0K3 (i*60) 60
  | 4 => packedAt s0K4 (i*49) 49
  | 5 => packedAt s0K5 (i*38) 38
  | 6 => packedAt s0K6 (i*27) 27
  | 7 => packedAt s0K7 (i*16) 16
  | 8 => packedAt s0K8 (i*5) 5
  | _ => 0

def s0H (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (213+i*9) 9
  | 3 => packedAt s0K3 (3600+i*8) 8
  | 4 => packedAt s0K4 (33124+i*7) 7
  | 5 => packedAt s0K5 (110998+i*6) 6
  | 6 => packedAt s0K6 (27432+i*5) 5
  | 7 => packedAt s0K7 (464+i*1) 1
  | _ => 0

def s0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (244+((h/1+packedAt s0K2 (240+(h % 1)*4) 4) % 11)*3) 3
  | 3 => packedAt s0K3 (4227+((h/21+packedAt s0K3 (4080+(h % 21)*7) 7) % 104)*7) 7
  | 4 => packedAt s0K4 (41046+((h/290+packedAt s0K4 (37856+(h % 290)*11) 11) % 1185)*11) 11
  | 5 => packedAt s0K5 (145749+((h/1325+packedAt s0K5 (128524+(h % 1325)*13) 13) % 5352)*13) 13
  | 6 => packedAt s0K6 (37319+((h/437+packedAt s0K6 (32512+(h % 437)*11) 11) % 1818)*11) 11
  | 7 => packedAt s0K7 (563+((h/10+packedAt s0K7 (493+(h % 10)*7) 7) % 77)*6) 6
  | 8 => packedAt s0K8 (6+((h/1+packedAt s0K8 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s0Pos : Nat → Bits
  | 0 => 0xfffddbdff2f3b5fecbcfdf9fffbb7bfe
  | 1 => 0xb4af7ffebd9ecb63feba77f695efffd7
  | 2 => 0xdad7fd6a5f3c6e0b7c7cbcfb5affad4b
  | 3 => 0xeff8818d67e177bc215fc95dff1031ac
  | 5 => 0x3062e318ffffbdfbff1226060c5c631
  | _ => 0

def s0Neg : Nat → Bits
  | 0 => 0x3e0cfc1f031800fc181cf807c19f83e
  | 1 => 0xf4070ffe018603e00e1a33fe80e1ffc0
  | 2 => 0xf807f00006387c0ff01c3c7f00fe0000
  | 3 => 0xfff8000007c07ff0001fc07fff000000
  | 5 => 0x7ffffffffe0000000000000
  | _ => 0

def s0Atlas : Atlas := ⟨8, rawDecor 47 s0Pos s0Neg, 0xeac8eac8a880a880, s0N, s0R, s0H, s0I, [((inputs.getD 3 zero), 6), ((inputs.getD 0 zero), 5), ((inputs.getD 1 zero), 5), (neg (inputs.getD 2 zero), 5), (neg (inputs.getD 3 zero), 5), (neg (inputs.getD 5 zero), 5), ((inputs.getD 2 zero), 4), ((inputs.getD 5 zero), 4)], [swapRows 82]⟩

def s2a0K2 : Nat → Nat
  | 0 => 0x43021094414ca6101329a408c6590630
  | _ => 0

def s2a0K3 : Nat → Nat
  | 0 => 0x6266663605466616602f995d32bc6370c6f185c30
  | _ => 0

def s2a0K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s2a0N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 6
  | 4 => 1
  | _ => 0

def s2a0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a0K2 (i*26) 26
  | 3 => packedAt s2a0K3 (i*15) 15
  | 4 => packedAt s2a0K4 (i*4) 4
  | _ => 0

def s2a0H (_k _i : Nat) : Nat := 0

def s2a0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a0K2 (107+((h/1+packedAt s2a0K2 (104+(h % 1)*3) 3) % 5)*4) 4
  | 3 => packedAt s2a0K3 (95+((h/1+packedAt s2a0K3 (90+(h % 1)*5) 5) % 17)*4) 4
  | 4 => packedAt s2a0K4 (5+((h/1+packedAt s2a0K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s2a0Pos : Nat → Bits
  | 1 => 0x5f5f35f355f55f5f35f355f55f5f35f3
  | 2 => 0xf5afcafcaf5af5afcafcaf5af5afcafc
  | 3 => 0xaaf5ff5ffaafaaf5ff5ffaafaaf5ff5f
  | 5 => 0xff0a00a0ffffff0a00a0ffffff0a00a0
  | _ => 0

def s2a0Neg : Nat → Bits
  | 1 => 0xf0f30f300f00f0f30f300f00f0f30f3
  | 2 => 0xf00fc0fc0f00f00fc0fc0f00f00fc0fc
  | 3 => 0xf00f00f00f00f00f00f00f00f00f00
  | 5 => 0xff000000ffffff000000ffffff000000
  | _ => 0

def s2a0Atlas : Atlas := ⟨4, rawDecor 46 s2a0Pos s2a0Neg, 0xfcc0fcc0fc00fc00, s2a0N, s2a0R, s2a0H, s2a0I, [], []⟩

def s2a1K2 : Nat → Nat
  | 0 => 0x132314c921c932483848520
  | _ => 0

def s2a1K3 : Nat → Nat
  | 0 => 0x30b1b332a102f995d32ec43d487d107920
  | _ => 0

def s2a1K4 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def s2a1N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | _ => 0

def s2a1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a1K2 (i*26) 26
  | 3 => packedAt s2a1K3 (i*15) 15
  | 4 => packedAt s2a1K4 (i*4) 4
  | _ => 0

def s2a1H (_k _i : Nat) : Nat := 0

def s2a1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a1K2 (80+((h/1+packedAt s2a1K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | 3 => packedAt s2a1K3 (94+((h/1+packedAt s2a1K3 (90+(h % 1)*4) 4) % 11)*4) 4
  | 4 => packedAt s2a1K4 (5+((h/1+packedAt s2a1K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s2a1Pos : Nat → Bits
  | 0 => 0xee24927b89ee24927b89ee24927b89ee
  | 2 => 0x22492fc8bf22492fc8bf22492fc8bf22
  | 3 => 0x55924495525592449552559244955255
  | 5 => 0x88fff9222488fff9222488fff9222488
  | _ => 0

def s2a1Neg : Nat → Bits
  | 0 => 0xee00003b80ee00003b80ee00003b80ee
  | 2 => 0xfc03f00000fc03f00000fc03f00
  | 3 => 0x0
  | 5 => 0xfff0000000fff0000000fff0000000
  | _ => 0

def s2a1Atlas : Atlas := ⟨4, rawDecor 45 s2a1Pos s2a1Neg, 0xfffafffaffa0ffa0, s2a1N, s2a1R, s2a1H, s2a1I, [], []⟩

def s2a2K2 : Nat → Nat
  | 0 => 0x43120a642cc6590f219443442910910
  | _ => 0

def s2a2K3 : Nat → Nat
  | 0 => 0x2b0a3313303333183b98f431ee43d087b887510
  | _ => 0

def s2a2K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s2a2N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 6
  | 4 => 1
  | _ => 0

def s2a2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a2K2 (i*26) 26
  | 3 => packedAt s2a2K3 (i*15) 15
  | 4 => packedAt s2a2K4 (i*4) 4
  | _ => 0

def s2a2H (_k _i : Nat) : Nat := 0

def s2a2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a2K2 (107+((h/1+packedAt s2a2K2 (104+(h % 1)*3) 3) % 5)*4) 4
  | 3 => packedAt s2a2K3 (94+((h/1+packedAt s2a2K3 (90+(h % 1)*4) 4) % 15)*4) 4
  | 4 => packedAt s2a2K4 (5+((h/1+packedAt s2a2K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s2a2Pos : Nat → Bits
  | 0 => 0xb7efdfbf5ad6b7efdfbf5ad6b7efdfbf
  | 1 => 0x6d9b366cb5ad6d9b366cb5ad6d9b366c
  | 2 => 0xcebd7af5e739cebd7af5e739cebd7af5
  | 5 => 0xf952a54afffff952a54afffff952a54a
  | _ => 0

def s2a2Neg : Nat → Bits
  | 0 => 0x1e3c78f000001e3c78f000001e3c78f
  | 1 => 0x6d9b366c318c6d9b366c318c6d9b366c
  | 2 => 0x8e1c3870c6318e1c3870c6318e1c3870
  | 5 => 0xf0000000fffff0000000fffff0000000
  | _ => 0

def s2a2Atlas : Atlas := ⟨4, rawDecor 39 s2a2Pos s2a2Neg, 0xeaeaeaeaa0a0a0a0, s2a2N, s2a2R, s2a2H, s2a2I, [], []⟩

def s2a3K2 : Nat → Nat
  | 0 => 0x102324c120d130443848110
  | _ => 0

def s2a3K3 : Nat → Nat
  | 0 => 0x28b1b312002f985d30de41b483b887510
  | _ => 0

def s2a3K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s2a3N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | _ => 0

def s2a3R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a3K2 (i*26) 26
  | 3 => packedAt s2a3K3 (i*15) 15
  | 4 => packedAt s2a3K4 (i*4) 4
  | _ => 0

def s2a3H (_k _i : Nat) : Nat := 0

def s2a3I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2a3K2 (80+((h/1+packedAt s2a3K2 (78+(h % 1)*2) 2) % 3)*3) 3
  | 3 => packedAt s2a3K3 (94+((h/1+packedAt s2a3K3 (90+(h % 1)*4) 4) % 9)*4) 4
  | 4 => packedAt s2a3K4 (5+((h/1+packedAt s2a3K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s2a3Pos : Nat → Bits
  | 0 => 0x9324c9324c9324c9324c9324c9324c93
  | 1 => 0x2e4b92e4b92e4b92e4b92e4b92e4b92e
  | 2 => 0x749d2749d2749d2749d2749d2749d274
  | 3 => 0xc8f23c8f23c8f23c8f23c8f23c8f23c8
  | _ => 0

def s2a3Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0xe0380e0380e0380e0380e0380e0380e
  | 2 => 0x701c0701c0701c0701c0701c0701c070
  | 3 => 0x80e0380e0380e0380e0380e0380e0380
  | _ => 0

def s2a3Atlas : Atlas := ⟨4, rawDecor 15 s2a3Pos s2a3Neg, 0xfeeafeeafeeafeea, s2a3N, s2a3R, s2a3H, s2a3I, [], []⟩

def s2a4K3 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def s2a4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def s2a4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2a4K3 (i*4) 4
  | _ => 0

def s2a4H (_k _i : Nat) : Nat := 0

def s2a4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2a4K3 (5+((h/1+packedAt s2a4K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s2a4Pos : Nat → Bits
  | 0 => 0x7d97f65f55d57d97f65f55d57d97f65f
  | 2 => 0xc6fd5bf5af2bc6fd5bf5af2bc6fd5bf5
  | 3 => 0x8fe83fa0fa3e8fe83fa0fa3e8fe83fa0
  | 5 => 0xf902a40afffff902a40afffff902a40a
  | _ => 0

def s2a4Neg : Nat → Bits
  | 0 => 0xd83f60f00000d83f60f00000d83f60f
  | 2 => 0xc03c00f00f03c03c00f00f03c03c00f0
  | 3 => 0xfc03f00f03c0fc03f00f03c0fc03f00
  | 5 => 0xf0000000fffff0000000fffff0000000
  | _ => 0

def s2a4Atlas : Atlas := ⟨3, rawDecor 45 s2a4Pos s2a4Neg, 0xfaaafaaaf0a0f0a0, s2a4N, s2a4R, s2a4H, s2a4I, [], []⟩

def s2a5K3 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s2a5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def s2a5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2a5K3 (i*4) 4
  | _ => 0

def s2a5H (_k _i : Nat) : Nat := 0

def s2a5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2a5K3 (5+((h/1+packedAt s2a5K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s2a5Pos : Nat → Bits
  | 0 => 0x5dc5dc5dc5dc5dc5dc5dc5dc5dc5dc5d
  | 1 => 0xce5ce5ce5ce5ce5ce5ce5ce5ce5ce5ce
  | 2 => 0xf5af5af5af5af5af5af5af5af5af5af5
  | 3 => 0xaafaafaafaafaafaafaafaafaafaafaa
  | _ => 0

def s2a5Neg : Nat → Bits
  | 0 => 0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0d
  | 1 => 0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce
  | 2 => 0xf00f00f00f00f00f00f00f00f00f00f0
  | 3 => 0xf00f00f00f00f00f00f00f00f00f00
  | _ => 0

def s2a5Atlas : Atlas := ⟨3, rawDecor 15 s2a5Pos s2a5Neg, 0xfca0fca0fca0fca0, s2a5N, s2a5R, s2a5H, s2a5I, [], []⟩

def s2K4 : Nat → Nat
  | 0 => 0x220820e4282820022504e824012827410823c1a666a827c0634266082488238446856824a0a543e822a2e3682245e7e1e3a80826e14465c6c82181664627a70725278321c284c085a300c048282762c5882823020207300c10a003d3020c144800c50910851060928c08e34d30844511840c28841931060850450861050810010c2144506114861844182143001001184063e6494b439d98652d0e756194b438f19150d0e776154c429d1855310a3f64542328f191508ca766514532d9988514cb656214532d58c8514cb543214532d5cc0514ca746154c41d50c5531063e64948419d986521063c6454041ce101501063e6494a318f592528c6766194a3197596328c7c5218ca318fd91508c63c64542319d185530863f64540218f19150086776154f409d18553d023e6494b409d98652d02756194b408f990524c23d64149309d984524c275611493097195324c2d4614c93097996314c27a65d01309dd8553c82746154f209e59740c83a942d03208f997544823e6515120cb988544832d6215120ce8c0544833820151208fd91534823c6454d209dd8553482746154d209e1953048338544c1209e997204833854c81209d18553c423e6494b108f59252c42766194b10
  | _ => 0

def s2K5 : Nat → Nat
  | 0 => 0x8a0184011842108644310c018061a50451040108420210c40180018061a504228420004212188528c03280050d0429944108441bf2a6877d53d0fbc87a1ef90f43eea1e87bc43d0efca5a1df54b43dea16877f51d0efca3a1df54743dfa0e87bd41d0efca1a1df54343be28687be40d0f7881a1df95342bf29e857d53d0af8a7a16fd0f42dea1e857d52d0bdc85a16f90b42f6a16857f51d0afca3a15f54742df20e857e50d0afaa1a15f14342dea06857e5410afca6215f54c42be298857e5210b7e84217b90842f6a1085bd4210afea2215f94442bea88857e5010afaa0215f14042df20085bc4010afea9195f95232beaa4657c548cafaa7195f94a32f799465df328cbd865195fd4632bf28c657d518cbb863197bc8632f690c657e508cafaa1195f14232bfaa2657e544cafaa8995f15132bfa9a657f524cbde6499778c932f619265dc324cbeea2995fd4532bba8a657d514cbe8a2995f14532ba28a65ef214cbda42995fd4132bf282657c504cbbe60995f95041bf298837d53106f8a620df94841bea9083bf421077a8420df94441dfa0883f641107ea8220ef50441fb98883f431107ea4220df94041bea80837c501077c8020ef10041bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7ee6318f7cc631ee98c63f4318c7ea4318df94231bea84637c508c7be6118dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21bf28c43f741887e88310fd8c621fa98c43f721887de4310fb48621bf284437d50886f8a110fd44221bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ee6210fd0c421f790843f621087ea4210fb48421bf280437d50086f8a010df95340bf29e817d53d02f8a7a05f94b40bea9681bf42d037a85a05fd4740bf28e817d51d02faa1a07e90340df20681f940d037881a07e8c340fc106817f544c2fca8985f55130be2a2617f534c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617d514c2f8a298778c530ee18a617f504c3f680987e10130fd98261de304c3f06098770c130fd10261fa104c3f220985fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7905f94b20f721641ed42c82fea3905f94720bea8e417d50c83f681907e10320fd10641ee20c83d841906fd5120bfaa2413f54482fca8905f55120de2a2417c5448278a8905fd4d20bf29a417d53482f8a6905fd4920f721241ed42482fea2905f54520be28a417f50483f460907e4c120fd90241ee20483f040907b08120bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10bf28e21f641c43ea83887dcc710fa18e21f621c43ea43885f54310fd08621f610c43f221887d04310
  | 1 => 0xa690238641c4220ac271fc0f8300b13a5f0561194a0ea308088a091dc3e1e42e1c8888e06c1746f95426078708082a8fa1794c181d86117a7496c160920f206289ae678cc9002890068030ca901065023c258e22d126901f46f18a668f68ea28582002c8205ca12431c0579ec659da6e0629019263a18750bc5c2360a9567784c900106e8700d1e875a404392c728768f84e03a40212404ca402b9f6902409020a3b20e6d186788022911a9014e7f8d2098902781c04852900445707a5224001a16201e0689ac7c9c6079940ba2c881f0900e81f1cc5188c2e84810a2e33912128505da041711c0610a3d110281827ba40891085496a251a45f8d08223432128191ce67144029d02d840268c6300b0360ea630a8681223c240069141516e408863c918898e4059641d20c3092a47a1e851fa541f89006a90166568da311046a8de6c8663f9e686a404d01423968209306d9005e0d44e1880124049072561a84b86c3f07e870be37210699164f136359ea4f9800c8ee58a408a9428c8381b8001699808920398361709ccca80380cb0001b814121b23889707c0012c1c5e000ec1a000000400350a0212e00078788033028006a02050a80c000f09450067d86c300a040882c06020140a2a00014040c0204c5c0f00134040b18c6320c00208a2948200c6241806621084208a22040121060190c421045104018c4862186318c6228872904012188618c6018c021080504a400846218060018821104214c410063121885100001884210c4100464310a518062108a510842080222188528c0310853114420802118060018822882109021090c430474000601
  | _ => 0

def s2K6 : Nat → Nat
  | 0 => 0x44130e5060ba83e28b19068442824a05a748706012a154220ea001b3a1941328a0d0d3c3d02812452a308580acc0468c40100e3120603510413410061641041051ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0

def s2K7 : Nat → Nat
  | 0 => 0x21f
  | _ => 0

def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 65
  | 5 => 288
  | 6 => 40
  | 7 => 1
  | _ => 0

def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*38) 38
  | 5 => packedAt s2K5 (i*27) 27
  | 6 => packedAt s2K6 (i*16) 16
  | 7 => packedAt s2K7 (i*5) 5
  | _ => 0

def s2H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (2470+i*6) 6
  | 5 => packedAt s2K5 (7776+i*5) 5
  | 6 => packedAt s2K6 (640+i*3) 3
  | _ => 0

def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (2972+((h/16+packedAt s2K4 (2860+(h % 16)*7) 7) % 83)*8) 8
  | 5 => packedAt s2K5 (9864+((h/72+packedAt s2K5 (9216+(h % 72)*9) 9) % 313)*10) 10
  | 6 => packedAt s2K6 (820+((h/10+packedAt s2K6 (760+(h % 10)*6) 6) % 49)*7) 7
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s2Pos : Nat → Bits
  | 0 => 0x2f85ef4067d8f49331cbe17bd019f63d
  | 1 => 0xf0bcf06ed577292e423c2f3c1bb55dca
  | 2 => 0x595f25b77e1e36748f5657c96ddf878d
  | 3 => 0x83ea53fb98638bc8ec20fa94fee618e2
  | 5 => 0xfe108a042184c3fff7bf842281086130
  | _ => 0

def s2Neg : Nat → Bits
  | 0 => 0x380efc001f8f0000000e03bf0007e3c
  | 1 => 0xe01cf007c1ff000e0038073c01f07fc0
  | 2 => 0x1f0007fe00007007c007c001ff8000
  | 3 => 0x3e003f800000380f800f800fe000000
  | 5 => 0xfc000000000003ffffff000000000000
  | _ => 0

def s2Atlas : Atlas := ⟨7, rawDecor 47 s2Pos s2Neg, 0xfeeafeeafca0fca0, s2N, s2R, s2H, s2I, [(neg (inputs.getD 0 zero), 5), ((inputs.getD 1 zero), 5), (neg (inputs.getD 3 zero), 5), ((inputs.getD 5 zero), 5), (neg (inputs.getD 1 zero), 4), (neg (inputs.getD 5 zero), 4)], []⟩

def s4a0K3 : Nat → Nat
  | 0 => 0x240d1a71a1cf0a0288a1a309d38c3a18b1f2098ca72a1502738913a74a3c1174e9d39b4e110a74e393a726445881234005100400206d90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0

def s4a0K4 : Nat → Nat
  | 0 => 0x14a2c8b04b0c1ac30030c24bb0730c30c30c20a842963864309b0c0cc02c18c1e2300090811c7fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0

def s4a0K5 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s4a0N (k : Nat) : Nat :=
  match k with
  | 3 => 39
  | 4 => 24
  | 5 => 1
  | _ => 0

def s4a0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4a0K3 (i*26) 26
  | 4 => packedAt s4a0K4 (i*15) 15
  | 5 => packedAt s4a0K5 (i*4) 4
  | _ => 0

def s4a0H (_k _i : Nat) : Nat := 0

def s4a0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4a0K3 (1068+((h/9+packedAt s4a0K3 (1014+(h % 9)*6) 6) % 54)*7) 7
  | 4 => packedAt s4a0K4 (396+((h/6+packedAt s4a0K4 (360+(h % 6)*6) 6) % 45)*6) 6
  | 5 => packedAt s4a0K5 (5+((h/1+packedAt s4a0K5 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s4a0Pos : Nat → Bits
  | 0 => 0xfffd5b6ffd5bb7fffeadb7feaddbffff
  | 1 => 0x9aa6b6da66b76d4d535b6d335bb6a6a9
  | 3 => 0x24cbe4fc8be47e9265f27e45f23f4932
  | 4 => 0x4713ff9113fec82389ffc889ff6411c4
  | _ => 0

def s4a0Neg : Nat → Bits
  | 0 => 0x77e00001dc00003bf00000ee00001df8
  | 1 => 0x880036da20376f44001b6d101bb7a200
  | 3 => 0x3c0fc03c07f8001e07e01e03fc000
  | 4 => 0x3ff0003ff800001ff8001ffc00000
  | _ => 0

def s4a0Atlas : Atlas := ⟨5, rawDecor 27 s4a0Pos s4a0Neg, 0xeeaaaa88eeaaaa88, s4a0N, s4a0R, s4a0H, s4a0I, [], []⟩

def s4K6 : Nat → Nat
  | 0 => 0x43f
  | _ => 0

def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | _ => 0

def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | _ => 0

def s4H (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (5+i*1) 1
  | _ => 0

def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (7+((h/1+packedAt s4K6 (6+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s4Pos : Nat → Bits
  | 0 => 0xf6dd77f56dbffdb75dfd5b6fff6dd77f
  | 1 => 0x5beeddfadb6996fbb77eb6da65beeddf
  | 3 => 0xbf66ff5f93f22fd9bfd7e4fc8bf66ff5
  | 4 => 0x3fff880ffe444fffe203ff9113fff880
  | 5 => 0xe49922affffff92648abfffffe49922a
  | _ => 0

def s4Neg : Nat → Bits
  | 0 => 0xf6dd33f000077db74cfc0001df6dd33f
  | 1 => 0xeeccf0db68803bb33c36da200eeccf
  | 3 => 0x3f00ff0f03f00fc03fc3c0fc03f00ff0
  | 4 => 0x3fff000ffc000fffc003ff0003fff000
  | 5 => 0xc000000ffffff0000003fffffc000000
  | _ => 0

def s4Atlas : Atlas := ⟨6, rawDecor 59 s4Pos s4Neg, 0xeeaaaa88cc008800, s4N, s4R, s4H, s4I, [((inputs.getD 5 zero), 6)], []⟩

def s6a0K2 : Nat → Nat
  | 0 => 0x982c310c421d031043808410
  | _ => 0

def s6a0K3 : Nat → Nat
  | 0 => 0x3133323300a9b02f18dc31dc43b087d887810
  | _ => 0

def s6a0K4 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def s6a0N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | _ => 0

def s6a0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s6a0K2 (i*26) 26
  | 3 => packedAt s6a0K3 (i*15) 15
  | 4 => packedAt s6a0K4 (i*4) 4
  | _ => 0

def s6a0H (_k _i : Nat) : Nat := 0

def s6a0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s6a0K2 (81+((h/1+packedAt s6a0K2 (78+(h % 1)*3) 3) % 5)*3) 3
  | 3 => packedAt s6a0K3 (94+((h/1+packedAt s6a0K3 (90+(h % 1)*4) 4) % 13)*4) 4
  | 4 => packedAt s6a0K4 (5+((h/1+packedAt s6a0K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s6a0Pos : Nat → Bits
  | 0 => 0x7fa5d7fa5d7fa5d7fa5d7fa5d7fa5d7f
  | 2 => 0xffffffffffffffffffffffffffffffff
  | 3 => 0xf5fa3f5fa3f5fa3f5fa3f5fa3f5fa3f5
  | 4 => 0x8affe8affe8affe8affe8affe8affe8a
  | _ => 0

def s6a0Neg : Nat → Bits
  | 0 => 0x3fa0c3fa0c3fa0c3fa0c3fa0c3fa0c3f
  | 2 => 0xcf0f3cf0f3cf0f3cf0f3cf0f3cf0f3cf
  | 3 => 0xf0f03f0f03f0f03f0f03f0f03f0f03f0
  | 4 => 0xffc00ffc00ffc00ffc00ffc00ffc00
  | _ => 0

def s6a0Atlas : Atlas := ⟨4, rawDecor 29 s6a0Pos s6a0Neg, 0xf0a0a000f0a0a000, s6a0N, s6a0R, s6a0H, s6a0I, [], []⟩

def s6a1K2 : Nat → Nat
  | 0 => 0x204310a642cc6590f219443442910910
  | _ => 0

def s6a1K3 : Nat → Nat
  | 0 => 0x6462566366066666103b98f431ee43d087b887510
  | _ => 0

def s6a1K4 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def s6a1N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 6
  | 4 => 1
  | _ => 0

def s6a1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s6a1K2 (i*26) 26
  | 3 => packedAt s6a1K3 (i*15) 15
  | 4 => packedAt s6a1K4 (i*4) 4
  | _ => 0

def s6a1H (_k _i : Nat) : Nat := 0

def s6a1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s6a1K2 (107+((h/1+packedAt s6a1K2 (104+(h % 1)*3) 3) % 5)*4) 4
  | 3 => packedAt s6a1K3 (95+((h/1+packedAt s6a1K3 (90+(h % 1)*5) 5) % 17)*4) 4
  | 4 => packedAt s6a1K4 (5+((h/1+packedAt s6a1K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s6a1Pos : Nat → Bits
  | 0 => 0xff55d7ff55d7ff55d7ff55d7ff55d7ff
  | 2 => 0xf0af3cf0af3cf0af3cf0af3cf0af3cf0
  | 3 => 0x55fa3f55fa3f55fa3f55fa3f55fa3f55
  | 4 => 0xaaffe8aaffe8aaffe8aaffe8aaffe8aa
  | _ => 0

def s6a1Neg : Nat → Bits
  | 0 => 0xff0000ff0000ff0000ff0000ff0000ff
  | 2 => 0xf00f3cf00f3cf00f3cf00f3cf00f3cf0
  | 3 => 0xf03f00f03f00f03f00f03f00f03f00
  | 4 => 0xffc000ffc000ffc000ffc000ffc000
  | _ => 0

def s6a1Atlas : Atlas := ⟨4, rawDecor 29 s6a1Pos s6a1Neg, 0xfaaaaa00faaaaa00, s6a1N, s6a1R, s6a1H, s6a1I, [], []⟩

def s6a2K3 : Nat → Nat
  | 0 => 0x27
  | _ => 0

def s6a2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def s6a2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s6a2K3 (i*3) 3
  | _ => 0

def s6a2H (_k _i : Nat) : Nat := 0

def s6a2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s6a2K3 (4+((h/1+packedAt s6a2K3 (3+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s6a2Pos : Nat → Bits
  | 0 => 0xff5555ff5555ff5555ff5555ff5555ff
  | 3 => 0x55aaff55aaff55aaff55aaff55aaff55
  | 4 => 0xaaffaaaaffaaaaffaaaaffaaaaffaaaa
  | _ => 0

def s6a2Neg : Nat → Bits
  | 0 => 0xff0000ff0000ff0000ff0000ff0000ff
  | 3 => 0xff0000ff0000ff0000ff0000ff00
  | 4 => 0xff0000ff0000ff0000ff0000ff0000
  | _ => 0

def s6a2Atlas : Atlas := ⟨3, rawDecor 25 s6a2Pos s6a2Neg, 0xffaaaa00ffaaaa00, s6a2N, s6a2R, s6a2H, s6a2I, [], []⟩

def s6a3K3 : Nat → Nat
  | 0 => 0x10f
  | _ => 0

def s6a3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def s6a3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s6a3K3 (i*4) 4
  | _ => 0

def s6a3H (_k _i : Nat) : Nat := 0

def s6a3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s6a3K3 (5+((h/1+packedAt s6a3K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s6a3Pos : Nat → Bits
  | 0 => 0x7db65f5f555d7db65f5f555d7db65f5f
  | 2 => 0xc6dbf5f5aaf3c6dbf5f5aaf3c6dbf5f5
  | 4 => 0x8fffa0a0ffa28fffa0a0ffa28fffa0a0
  | 5 => 0xf9240a0afffff9240a0afffff9240a0a
  | _ => 0

def s6a3Neg : Nat → Bits
  | 0 => 0xdb60f0f00000db60f0f00000db60f0f
  | 2 => 0xc000f0f000f3c000f0f000f3c000f0f0
  | 4 => 0xfff0000ff000fff0000ff000fff0000
  | 5 => 0xf0000000fffff0000000fffff0000000
  | _ => 0

def s6a3Atlas : Atlas := ⟨3, rawDecor 53 s6a3Pos s6a3Neg, 0xfafaaaaaf0f0a0a0, s6a3N, s6a3R, s6a3H, s6a3I, [], []⟩

def s6K4 : Nat → Nat
  | 0 => 0xd3872900c159659258259658b3c4180216313154251540719512045208a4110081100a114a211479a64194f950319eaa063b5410c67ca810cf55021daa08433e54cc27aa9985b94830b6a90613e54c827aa9905794c20aea98413e54c427aa9886d50710dc206213e540427aa8086e10010
  | _ => 0

def s6K5 : Nat → Nat
  | 0 => 0x192c1c825007530c58856110c49622587cda414b068e588c585580562b58a102c2a51603124c2273c6161a383d529045c40f01114314000305824924996024945d61c6094491681200d8ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0

def s6K6 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def s6N (k : Nat) : Nat :=
  match k with
  | 4 => 22
  | 5 => 44
  | 6 => 1
  | _ => 0

def s6R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s6K4 (i*27) 27
  | 5 => packedAt s6K5 (i*16) 16
  | 6 => packedAt s6K6 (i*5) 5
  | _ => 0

def s6H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s6K4 (594+i*5) 5
  | 5 => packedAt s6K5 (704+i*3) 3
  | _ => 0

def s6I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s6K4 (729+((h/5+packedAt s6K4 (704+(h % 5)*5) 5) % 30)*6) 6
  | 5 => packedAt s6K5 (902+((h/11+packedAt s6K5 (836+(h % 11)*6) 6) % 56)*7) 7
  | 6 => packedAt s6K6 (6+((h/1+packedAt s6K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s6Pos : Nat → Bits
  | 0 => 0xfff5d75fff6cbebffd75d7ffdb2fafff
  | 2 => 0xaffa3cf3c1bfebebfe8f3cf06ffafaff
  | 3 => 0xfd5f68fd57f741ff57da3f55fdd07fd5
  | 4 => 0x2afbfa2abfbff40abefe8aafeffd02a
  | 5 => 0x500ffffffe40141403ffffff90050500
  | _ => 0

def s6Neg : Nat → Bits
  | 0 => 0x7bc00003ff7c1e1ef00000ffdf0787bc
  | 2 => 0x83f03cf3c001e1e0fc0f3cf00078783f
  | 3 => 0xfc0fc0fc03fe01ff03f03f00ff807fc0
  | 4 => 0xfff0003fffe0003ffc000ffff8000
  | 5 => 0xffffffc00000003ffffff00000000
  | _ => 0

def s6Atlas : Atlas := ⟨6, rawDecor 61 s6Pos s6Neg, 0xfaaaaa00f0a0a000, s6N, s6R, s6H, s6I, [(neg (inputs.getD 5 zero), 5), ((inputs.getD 5 zero), 5), ((inputs.getD 2 zero), 4), ((inputs.getD 3 zero), 4), ((inputs.getD 4 zero), 4)], []⟩

def s8a0K2 : Nat → Nat
  | 0 => 0x24314400a5428c6550e219543042950810
  | _ => 0

def s8a0K3 : Nat → Nat
  | 0 => 0x1301ab0b2303b18f531ec43d487b087410
  | _ => 0

def s8a0K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s8a0N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 6
  | 4 => 1
  | _ => 0

def s8a0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s8a0K2 (i*26) 26
  | 3 => packedAt s8a0K3 (i*15) 15
  | 4 => packedAt s8a0K4 (i*4) 4
  | _ => 0

def s8a0H (_k _i : Nat) : Nat := 0

def s8a0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s8a0K2 (107+((h/1+packedAt s8a0K2 (104+(h % 1)*3) 3) % 7)*4) 4
  | 3 => packedAt s8a0K3 (94+((h/1+packedAt s8a0K3 (90+(h % 1)*4) 4) % 10)*4) 4
  | 4 => packedAt s8a0K4 (5+((h/1+packedAt s8a0K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s8a0Pos : Nat → Bits
  | 0 => 0xff5555ff5555ff5555ff5555ff5555ff
  | 1 => 0x99cccc99cccc99cccc99cccc99cccc99
  | 3 => 0x22aaff22aaff22aaff22aaff22aaff22
  | 4 => 0x44ffaa44ffaa44ffaa44ffaa44ffaa44
  | _ => 0

def s8a0Neg : Nat → Bits
  | 0 => 0x77000077000077000077000077000077
  | 1 => 0x88cccc88cccc88cccc88cccc88cccc88
  | 3 => 0xff0000ff0000ff0000ff0000ff00
  | 4 => 0xff0000ff0000ff0000ff0000ff0000
  | _ => 0

def s8a0Atlas : Atlas := ⟨4, rawDecor 27 s8a0Pos s8a0Neg, 0xffaaaa88ffaaaa88, s8a0N, s8a0R, s8a0H, s8a0I, [], []⟩

def s8a1K2 : Nat → Nat
  | 0 => 0x5360314c521d131443848510
  | _ => 0

def s8a1K3 : Nat → Nat
  | 0 => 0x3130b0321a82f98dd31de43b487d087910
  | _ => 0

def s8a1K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s8a1N (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 6
  | 4 => 1
  | _ => 0

def s8a1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s8a1K2 (i*26) 26
  | 3 => packedAt s8a1K3 (i*15) 15
  | 4 => packedAt s8a1K4 (i*4) 4
  | _ => 0

def s8a1H (_k _i : Nat) : Nat := 0

def s8a1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s8a1K2 (81+((h/1+packedAt s8a1K2 (78+(h % 1)*3) 3) % 5)*3) 3
  | 3 => packedAt s8a1K3 (94+((h/1+packedAt s8a1K3 (90+(h % 1)*4) 4) % 10)*4) 4
  | 4 => packedAt s8a1K4 (5+((h/1+packedAt s8a1K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s8a1Pos : Nat → Bits
  | 0 => 0xee249ee249ee249ee249ee249ee249ee
  | 1 => 0x33492334923349233492334923349233
  | 3 => 0x4493f4493f4493f4493f4493f4493f44
  | 4 => 0x88fe488fe488fe488fe488fe488fe488
  | _ => 0

def s8a1Neg : Nat → Bits
  | 0 => 0xee000ee000ee000ee000ee000ee000ee
  | 1 => 0x0
  | 3 => 0x3f0003f0003f0003f0003f0003f00
  | 4 => 0xfc000fc000fc000fc000fc000fc000
  | _ => 0

def s8a1Atlas : Atlas := ⟨4, rawDecor 27 s8a1Pos s8a1Neg, 0xffeeeeccffeeeecc, s8a1N, s8a1R, s8a1H, s8a1I, [], []⟩

def s8a3K3 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s8a3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0

def s8a3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s8a3K3 (i*4) 4
  | _ => 0

def s8a3H (_k _i : Nat) : Nat := 0

def s8a3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s8a3K3 (5+((h/1+packedAt s8a3K3 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s8a3Pos : Nat → Bits
  | 0 => 0x66db777755db66db777755db66db7777
  | 1 => 0xbdb6ddddaa6dbdb6ddddaa6dbdb6dddd
  | 4 => 0x4fff2222ff924fff2222ff924fff2222
  | 5 => 0xf9248888fffff9248888fffff9248888
  | _ => 0

def s8a3Neg : Nat → Bits
  | 0 => 0x6000333300db6000333300db60003333
  | 1 => 0xdb6cccc00000db6cccc00000db6cccc
  | 4 => 0xfff0000ff000fff0000ff000fff0000
  | 5 => 0xf0000000fffff0000000fffff0000000
  | _ => 0

def s8a3Atlas : Atlas := ⟨3, rawDecor 51 s8a3Pos s8a3Neg, 0xeeeeccccaaaa8888, s8a3N, s8a3R, s8a3H, s8a3I, [], []⟩

def s8K4 : Nat → Nat
  | 0 => 0x22cb2c82cb0671461602c40a112b2a8a4a2c31eb2cb026acb0eb26b04080140208311062110081100a1146420cb9864994fd51319e2a263b4414c67ea890cf15121da20a433e548c27aa9185bd4930b6292613e548827aa91057d4d20ae29a413e548427aa9086d10610dca04213f5444278a8886e50110
  | _ => 0

def s8K5 : Nat → Nat
  | 0 => 0x160106596281e14f1930b162c4a2930d588030c22b11ac5849608586d62c580162458b162c58b09a744b0e97583822c52b109f58ace1012b010b5451615341c0010132004030e00104249249b0425126b0e30c9251a05804603ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0

def s8K6 : Nat → Nat
  | 0 => 0x21f
  | _ => 0

def s8N (k : Nat) : Nat :=
  match k with
  | 4 => 22
  | 5 => 44
  | 6 => 1
  | _ => 0

def s8R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s8K4 (i*27) 27
  | 5 => packedAt s8K5 (i*16) 16
  | 6 => packedAt s8K6 (i*5) 5
  | _ => 0

def s8H (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s8K4 (594+i*5) 5
  | 5 => packedAt s8K5 (704+i*3) 3
  | _ => 0

def s8I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s8K4 (734+((h/5+packedAt s8K4 (704+(h % 5)*6) 6) % 37)*6) 6
  | 5 => packedAt s8K5 (913+((h/11+packedAt s8K5 (836+(h % 11)*7) 7) % 72)*7) 7
  | 6 => packedAt s8K6 (6+((h/1+packedAt s8K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s8Pos : Nat → Bits
  | 0 => 0xf7f249ee28d28ebdfc927b8a34a3af7f
  | 1 => 0x9c949233e6ce6a6725248cf9b39a99c9
  | 3 => 0x21293f44532ffd884a4fd114cbff6212
  | 4 => 0x424fe488ffb5311093f9223fed4c4424
  | 5 => 0x80fffff8408404203ffffe102101080
  | _ => 0

def s8Neg : Nat → Bits
  | 0 => 0x738000ee0000001ce0003b8000000738
  | 1 => 0x8c000000e7ce7e6300000039f39f98c0
  | 3 => 0x3f00000fff80000fc00003ffe000
  | 4 => 0xfc000fff0000003f0003ffc000000
  | 5 => 0xfffff0000000003ffffc000000000
  | _ => 0

def s8Atlas : Atlas := ⟨6, rawDecor 59 s8Pos s8Neg, 0xffeeeeccffaaaa88, s8N, s8R, s8H, s8I, [(neg (inputs.getD 5 zero), 5), ((inputs.getD 5 zero), 5), (neg (inputs.getD 1 zero), 4), (neg (inputs.getD 3 zero), 4), (neg (inputs.getD 4 zero), 4)], []⟩

def s10a0K2 : Nat → Nat
  | 0 => 0x21340094414ca6101329a408c6590630
  | _ => 0

def s10a0K3 : Nat → Nat
  | 0 => 0x130ab33031b32302f995d32bc6370c6f185c30
  | _ => 0

def s10a0K4 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def s10a0N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 6
  | 4 => 1
  | _ => 0

def s10a0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s10a0K2 (i*26) 26
  | 3 => packedAt s10a0K3 (i*15) 15
  | 4 => packedAt s10a0K4 (i*4) 4
  | _ => 0

def s10a0H (_k _i : Nat) : Nat := 0

def s10a0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s10a0K2 (107+((h/1+packedAt s10a0K2 (104+(h % 1)*3) 3) % 5)*4) 4
  | 3 => packedAt s10a0K3 (94+((h/1+packedAt s10a0K3 (90+(h % 1)*4) 4) % 14)*4) 4
  | 4 => packedAt s10a0K4 (5+((h/1+packedAt s10a0K4 (4+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s10a0Pos : Nat → Bits
  | 1 => 0x5f55f3f3555f5f55f3f3555f5f55f3f3
  | 2 => 0xf5aafcfcaaf5f5aafcfcaaf5f5aafcfc
  | 4 => 0xaaff5f5fffaaaaff5f5fffaaaaff5f5f
  | 5 => 0xff00a0a0ffffff00a0a0ffffff00a0a0
  | _ => 0

def s10a0Neg : Nat → Bits
  | 1 => 0xf00f3f3000f0f00f3f3000f0f00f3f3
  | 2 => 0xf000fcfc00f0f000fcfc00f0f000fcfc
  | 4 => 0xff0000ff0000ff0000ff0000ff0000
  | 5 => 0xff000000ffffff000000ffffff000000
  | _ => 0

def s10a0Atlas : Atlas := ⟨4, rawDecor 54 s10a0Pos s10a0Neg, 0xfcfcc0c0fcfc0000, s10a0N, s10a0R, s10a0H, s10a0I, [], []⟩

def s10K5 : Nat → Nat
  | 0 => 0x43f
  | _ => 0

def s10N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0

def s10R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s10K5 (i*5) 5
  | _ => 0

def s10H (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s10K5 (5+i*1) 1
  | _ => 0

def s10I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s10K5 (7+((h/1+packedAt s10K5 (6+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def s10Pos : Nat → Bits
  | 1 => 0xd7fd7cfcf55f5ff5f3f3d57d7fd7cfcf
  | 2 => 0x7d7ebf3f3af5f5fafcfcebd7d7ebf3f3
  | 3 => 0xbfc3d7ffcfaaff0f5fff3eabfc3d7ffc
  | 4 => 0xea83ffd7cfffaa0fff5f3ffea83ffd7c
  | 5 => 0xfffc28283ffffff0a0a0ffffffc28283
  | _ => 0

def s10Neg : Nat → Bits
  | 1 => 0xc3cc3cfcf00f0f30f3f3c03c3cc3cfcf
  | 2 => 0x3c303f3f30f0f0c0fcfcc3c3c303f3f3
  | 3 => 0x3fc3c03fcf00ff0f00ff3c03fc3c03fc
  | 4 => 0xc003ffc00fff000fff003ffc003ffc00
  | 5 => 0xfffc00000ffffff000003fffffc00000
  | _ => 0

def s10Atlas : Atlas := ⟨5, rawDecor 62 s10Pos s10Neg, 0xfcc0c0c0fc000000, s10N, s10R, s10H, s10I, [((inputs.getD 3 zero), 5)], []⟩

def mainK5 : Nat → Nat
  | 0 => 0x88c1f2a4411a2c28399489099c200d22148344a00c20a1e3a912240048b8b481520c469071b023c22534408234014071717173737171737371b4b2d172727472727474727274b1b3e202017472737174727371c4f4c709bb26018527a6384dd9300c293d29416ec9806149d94a0b764c030a4fca305bb2601852725182dd9300c293d2940eec9806149d94a07764c030a4fca303bb2601852725181dd9300c30bd0bbb6429806185d85ddb214c030c4e3a30c10a601861ba6085dd9200828dd3042eec9004146e95a0f7648020a36cad07bb2401051be5583dd9200828d92ac1eec9004146e95a077648020a36cad03bb2401051be5581dd9200828d92ac0eec900418ae84dda3148020c56c26ed18a401061b594874c5200820fd3042cec102210be98e13764c010a3b4ad07bb2200851d65683dd91004296f28c1eec880214b49460f7644010a3b4ad05bb2200851d65682dd91004296f28c16ec880214b49460b7644010
  | _ => 0

def mainK6 : Nat → Nat
  | 0 => 0xd835db300423f20d76cc0108ff825db300423fa0976cc0108fd825db300423f20976cc0108ff815db300423fa0576cc0108fd815db300423f20576cc010cde305db30043370c176cc010cf7105db300433d44176cc0108ff85dd9300423fa17764c0108fd85dd9300423f217764c010cbf84dd9300423fe13764c0108bf84dd9300423fa13764c0108fd84dd9300432f213764c0108fc84dd9300422f213764c0108ff83dd9300423fa0f764c0108fd83dd9300423f20f764c0108ff82dd9300423fa0b764c0108fd82dd9300423f20b764c0108ff81dd9300423fa07764c0108fd81dd9300423f207764c0108ff80dd9300423f603764c010cde30dd930043370c3764c010cf710dd9300433d443764c0108ff855db200423fa1576c80108fd855db200423f21576c80108ff845db200423fa1176c80108fd845db200423f21176c80108ff835db200423fa0d76c80108fd835db200423f20d76c80108ff825db200423fa0976c80108fd825db200423f20976c8010cee525db200433b54976c80108ff815db200423fa0576c80108fd815db200423f20576c8010cee205db200433b08176c8010cf7105db200433d44176c80108ff85dd9200423fa1776480108fd85dd9200423f21776480108ff84dd9200423fa1376480108fd84dd9200423f21376480108ff83dd9200423fa0f76480108fd83dd9200423f20f76480108ff82dd9200423fa0b76480108fd82dd9200423f20b7648010cee52dd9200433b54b76480108ff81dd9200423fa0776480108fd81dd9200423f20776480108ff80dd9200423fa0376480108fd80dd9200423f2037648010cee20dd9200433b0837648010cf710dd9200433d4437648010cf785dd9100433da177644010cf585dd9100433d2177644010cf784dd9100433da137644010cf584dd9100433d2137644010cf754dd9100433d9537644010cf554dd9100433d1537644010cf783dd9100433da0f7644010cf583dd9100433d20f7644010cf753dd9100433d94f7644010cf553dd9100433d14f7644010cf743dd9100433d90f7644010cf543dd9100433d10f7644010cf782dd9100433da0b7644010cf582dd9100433d20b7644010cf752dd9100433d94b7644010cf552dd9100433d14b7644010cf742dd9100433d90b7644010cf542dd9100433d10b7644010cf780dd9100433da037644010cf580dd9100433d2037644010cf750dd9100433d9437644010cf550dd9100433d1437644010cf740dd9100433d9037644010cf540dd9100433d1037644010cf730dd9100433d8c37644010cf530dd9100433d0c37644010cf720dd9100433d8837644010cf520dd9100433d0837644010cf776cc9100433ddda32440109f7874c9100427d21d3244010cf7764c910042bda183244010af5860c9100433ddd83244010
  | 1 => 0x59d8304423fe12760c1108fe849d8304423f612760c1108fc849d8304423fe0e760c1108fe839d83044337d0e760c110cdc439d8304423fe0a760c1108fe829d8304423f60a760c1108fc829d8304423f606760c1108fc819d8304423fa02760c1108fc809d83044337cc2760c110cdd309d8304433d842760c110cf4109d8304423fe1676881108fe859da204423f61676881108fc859da204423fe1276881108fe849da204423f61276881108fc849da204423fe0e76881108fe839da204423f60e76881108fc839da204423f60a76881108fc829da204423f60676881108fc819da204433bc827688110ced209da204433d8427688110cf4109da204431fe1676081108ff859d8204421fe1676081108fe859d8204423f6167608110c7c859d8204423f216760811087c859d8204423fe1276081108fe849d8204423f61276081108fc849d8204423fe0e76081108fe839d8204423f60e76081108fc839d8204423fe0a76081108fe829d8204423f60676081108fc819d8204423fe0276081108fe809d8204423f60276081108fc809d8204433bc827608110ced209d8204433d8427608110cf4109d8204423fe1576cc8108fe855db320423f61576cc8108fc855db320423fe1176cc8108fe845db320423f61176cc8108fc845db320423f20d76cc8108ff825db320433b8c976cc810ced325db320423fe0576cc8108fe815db320423f60576cc8108fc815db320423fe0176cc8108fe805db320423f60176cc8108fc805db320423fe15768c8108fe855da320423f615768c8108fc855da320423fe11768c8108fe845da320423f611768c8108fc845da320423fe0d768c8108fd835da320423fa09768c8108fc825da3204337cc9768c810cdd325da320423fe05768c8108fe815da320423f605768c8108fc815da320423fe01768c8108fe805da320423f601768c8108fc805da320423fe17764c8108fe85dd9320423f617764c8108fc85dd9320423fe13764c8108fe84dd9320423f613764c8108fc84dd9320423f60f764c8108fd82dd9320423fe07764c8108fe81dd9320423f607764c8108fc81dd9320423fe03764c8108fe80dd9320423f603764c8108fc80dd9320423fe15760c8108fe855d8320423f615760c8108fc855d8320423fe11760c8108fe845d8320423f611760c8108fc845d8320423fa0d760c8108fc835d8320423fa09760c8108fc825d83204337cc9760c810cee325d8320433b4c9760c810cdd325d8320423fe05760c8108fe815d8320423f605760c8108fc815d8320423fe01760c8108fe805d8320423f601760c8108fc805d8320433dc41760c8108ff855db300423fa1576cc0108fd855db300423f21576cc0108ff845db300423fa1176cc0108fd845db300423f21176cc0108ff835db300423fa0d76cc0108f
  | 2 => 0xdb328423fe1176cca108fe845db328423f61176cca108fc845db328423f20d76cca108ff825db328423fe0576cca108fd815db328423fa0176cca108fc805db328423fe15768ca108fe855da328423f615768ca108fc855da328423fe11768ca108fe845da328423f611768ca108fc845da328423fe0d768ca108fd835da328423fa09768ca108fc825da328423fe05768ca108fd815da328423fa01768ca108fc805da328423fe17764ca108fe85dd9328423f617764ca108fc85dd9328423fe13764ca108fe84dd9328423f613764ca108fc84dd9328423f60f764ca108fd82dd9328423fe07764ca108fd81dd9328423fa03764ca108fc80dd9328423fe15760ca108fe855d8328423f615760ca108fc855d8328423fe11760ca108fe845d8328423f611760ca108fc845d8328423fa0d760ca108fc835d8328423fa09760ca108fc825d8328423fe05760ca108fd815d8328423fa01760ca108fc805d8328433d441760ca109f7874cb108427d21d32c4210af6860cb10842bd61832c42108ff859db324423fa1676cc9108fd859db324423f21676cc9108ff849db324423fa1276cc9108fd849db324423f21276cc9108fe839db324423f60a76cc910cde329db32443370ca76cc9108fe819db324423f60676cc9108fc819db324423fa0276cc9108fd809db324423f20276cc9108ff859da324423fa16768c9108fd859da324423f216768c9108ff849da324423fa12768c9108fd849da324423f212768c9108ff839da324423f60e768c9108fe829da324423f20a768c910cef329da324433b0ca768c9108fe819da324423f606768c9108fc819da324423fa02768c9108fd809da324423f202768c9108ff851d9324423fa14764c9108fd851d9324423f214764c9108ff841d9324423fa10764c9108fd841d9324423f210764c9108fd831d9324423f608764c910cef321d932443378c8764c910cec321d932443370c8764c9108fe811d9324423f604764c9108fc811d9324423fa00764c9108fd801d9324423f200764c910cf6101d9324423fe16760c9108fe859d8324423f616760c9108fc859d8324423fe12760c9108fe849d8324423f612760c9108fc849d8324423fa0e760c9108fc839d8324423fa0a760c9108fc829d8324423fa06760c9108fd819d8324423f206760c9108fe809d8324423f602760c9108fc809d8324423fe16768c1108fe859da304423f616768c1108fc859da304423fe12768c1108fe849da304423f612768c1108fc849da304423f60e768c1108fc839da3044337d0e768c110cdc439da304423fe0a768c1108fe829da304423f60a768c1108fc829da304423f606768c1108fc819da3044337cc2768c110cdd309da304433d842768c110cf4109da304423fe16760c1108fe859d8304423f616760c1108fc8
  | 3 => 0x300823f21176cc0208fd835db300823f20d76cc0208fd825db300823f20976cc0208ff815db300823fa0576cc0208fd815db300823f20576cc020cde305db30083370c176cc020cef205db300833b48176cc0208ff85dd9300823fa17764c0208fd85dd9300823f217764c0208ff84dd9300823fa13764c0208fd84dd9300823f213764c0208fd83dd9300823f20f764c0208ff82dd9300823fa0b764c0208ff81dd9300823fa07764c0208fd81dd9300823f207764c020cde30dd930083370c3764c020cef20dd9300833b483764c020cef85dd9200831be177648020cee85dd9200833b6177648020cec85dd9200831b2177648020cef84dd9200833ba137648020ced84dd9200833b2137648020cef54dd9200833b9537648020ced54dd9200833b1537648020cef83dd9200833ba0f7648020ced83dd9200833b20f7648020cef53dd9200833b94f7648020ced53dd9200833b14f7648020cef43dd9200833b90f7648020ced43dd9200833b10f7648020cef81dd9200833ba077648020ced81dd9200833b2077648020cef51dd9200833b9477648020ced51dd9200833b1477648020cef41dd9200833b9077648020ced41dd9200833b1077648020cef80dd9200833ba037648020ced80dd9200833b2037648020cef50dd9200833b9437648020ced50dd9200833b1437648020cef40dd9200833b9037648020ced40dd9200833b1037648020cef30dd9200833b8c37648020ced30dd9200833b0c37648020cef10dd9200833b8437648020ced10dd9200833b0437648020cef76cc5200839b5973148020cef768c5200839b5963148020bae848c520082eb6123148020bea808c520082fa60231480209ef874c5200827b21d3148020cef764c5200839b5953148020aee860c520082bb6183148020cef760c5200839b59431480208ff855db32c423fa1576ccb108fd855db32c423f21576ccb108ff845db32c423fa1176ccb108fd845db32c423f21176ccb108fc835db32c423fe0976ccb108fc815db32c423fe0176ccb108ff855da32c423fa15768cb108fd855da32c423f215768cb108ff845da32c423fa11768cb108fd845da32c423f211768cb108ff835da32c423f60d768cb108fe825da32c423f209768cb108fc815da32c423fe01768cb108ff85dd932c423fa17764cb108fd85dd932c423f217764cb108ff84dd932c423fa13764cb108fd84dd932c423f213764cb108fd83dd932c423f60b764cb108fe81dd932c423f603764cb10cf410dd932c423fe15760cb108fe855d832c423f615760cb108fc855d832c423fe11760cb108fe845d832c423f611760cb108fc845d832c423fa0d760cb108fc835d832c423fa09760cb108fc825d832c423f205760cb108ff805d832c423fe1576cca108fe855db328423f61576cca108fc855
  | 4 => 0x4823fa10764c5208fd841d9314823f210764c5208fd831d9314823f608764c5208fc821d9314833b948764c520ced521d9314823f604764c520cf7311d931483378c4764c520cf4311d931483370c4764c5208fd801d9314823f200764c520cee201d9314823fe16760c5208fe859d8314823f616760c5208fc859d8314823fe12760c5208fe849d8314823f612760c5208fc849d8314823fa0e760c5208fc839d8314823f60a760c5208fc829d8314823fa06760c5208fc819d8314823f602760c5208fc809d8314823fe16768c1208fe859da304823f616768c1208fc859da304823fe12768c1208fe849da304823f612768c1208fc849da304823f60e768c1208fc839da3048337d0e768c120cdc439da304823f60a768c1208fc829da304833b94a768c120ced529da304823fe06768c1208fe819da304823f606768c1208fc819da3048337cc2768c120cdd309da304833b882768c120cec209da304823fe16760c1208fe859d8304823f616760c1208fc859d8304823fe12760c1208fe849d8304823f612760c1208fc849d8304823fe0e760c1208fe839d83048337d0e760c120cdc439d8304823f60a760c1208fc829d8304833b94a760c120ced529d8304823fe06760c1208fe819d8304823f606760c1208fc819d83048337cc2760c120cdd309d8304833b882760c120cec209d8304823fe1576cc4208fe855db310823f61576cc4208fc855db310823fe1176cc4208fe845db310823f61176cc4208fc845db310823f20d76cc4208fe825db310823f60976cc4208fc825db310823fe0576cc420cf6315db310833d4c576cc4208fe805db310823f60176cc4208fc805db310823fe15768c4208fe855da310823f615768c4208fc855da310823fe11768c4208fe845da310823f611768c4208fc845da310823fe0d768c4208fd835da310823fa09768c4208fd825da310823f209768c4208fe815da310823f205768c420cdf315da31083374c5768c4208fe805da310823f601768c4208fc805da310823fe17764c4208fe85dd9310823f617764c4208fc85dd9310823fe13764c4208fe84dd9310823f613764c4208fc84dd9310823f60f764c4208ff82dd9310823fa0b764c4208fc82dd9310823f607764c4208ff80dd9310823fa03764c4208fc80dd9310823fe15760c4208fe855d8310823f615760c4208fc855d8310823fe11760c4208fe845d8310823f611760c4208fc845d8310823fa0d760c4208fc835d8310823fa09760c4208fd825d8310823f209760c4208fe815d8310823f205760c420cdf315d8310833d8c5760c420cf5315d831083374c5760c4208fe805d8310823f601760c4208fc805d8310833bc81760c4208ff855db300823fa1576cc0208fd855db300823f21576cc0208ff845db300823fa1176cc0208fd845db
  | 5 => 0x2b7618214c030cdf76085300c3671d0214c0308ff855db31c823fa1576cc7208fd855db31c823f21576cc7208ff845db31c823fa1176cc7208fd845db31c823f21176cc7208fc835db31c823f20976cc7208ff815db31c823fe0176cc7208ff855da31c823fa15768c7208fd855da31c823f215768c7208ff845da31c823fa11768c7208fd845da31c823f211768c7208ff835da31c823f60d768c7208fc825da31c823fa05768c7208fc815da31c823fe01768c7208ff85dd931c823fa17764c7208fd85dd931c823f217764c7208ff84dd931c823fa13764c7208fd84dd931c823f213764c7208fd83dd931c823fa0b764c720cee52dd931c833b54b764c7208fd81dd931c823f603764c720cec20dd931c823fe15760c7208fe855d831c823f615760c7208fc855d831c823fe11760c7208fe845d831c823f611760c7208fc845d831c823fa0d760c7208fc835d831c823f209760c7208fe815d831c823f205760c7208ff805d831c823fe1576cc6208fe855db318823f61576cc6208fc855db318823fe1176cc6208fe845db318823f61176cc6208fc845db318823f20d76cc6208ff825db318823f60976cc6208ff815db318823fa0176cc6208fc805db318823fe15768c6208fe855da318823f615768c6208fc855da318823fe11768c6208fe845da318823f611768c6208fc845da318823fe0d768c6208fd835da318823fe09768c6208fd825da318823fa05768c6208fc815da318823fa01768c6208fc805da318823fe17764c6208fe85dd9318823f617764c6208fc85dd9318823fe13764c6208fe84dd9318823f613764c6208fc84dd9318823f60f764c6208ff82dd9318823f60b764c6208fd81dd9318823fa03764c6208fc80dd9318823fe15760c6208fe855d8318823f615760c6208fc855d8318823fe11760c6208fe845d8318823f611760c6208fc845d8318823fa0d760c6208fc835d8318823fe09760c6208fd825d8318823fa05760c6208fc815d8318823fa01760c6208fc805d8318833b481760c620bae848c720882eb61231c82209ef874c7208827b21d31c8220aee860c720882bb61831c82208ff859db314823fa1676cc5208fd859db314823f21676cc5208ff849db314823fa1276cc5208fd849db314823f21276cc5208fe839db314823f60a76cc5208fc829db314823f60676cc520cde319db31483370c676cc5208fd809db314823f20276cc5208ff859da314823fa16768c5208fd859da314823f216768c5208ff849da314823fa12768c5208fd849da314823f212768c5208ff839da314823f60e768c5208fd829da314823f20a768c5208fe819da314823f206768c520cf7319da314833d0c6768c5208fd809da314823f202768c5208ff851d9314823fa14764c5208fd851d9314823f214764c5208ff841d931
  | 6 => 0xf61676085308fc859d8214c23fe1276085308fe849d8214c23f61276085308fc849d8214c23f60e76085308fc839d8214c23fa0a76085308fc829d8214c23fa0676085308fc819d8214c23f60276085308fc809d8214c23fe1576c84308fe855db210c23f61576c84308fc855db210c23fe1176c84308fe845db210c23f61176c84308fc845db210c23fa0d76c84308fd835db210c23f20d76c84308fc825db210c23fe0576c8430cf6215db210c33d48576c84308fe805db210c23f60176c84308fc805db210c23fe1576884308fe855da210c23f61576884308fc855da210c23fe1176884308fe845da210c23f61176884308fc845da210c23fa0d76884308fd835da210c23f20d76884308ff825da210c23f60976884308fe815da210c23f2057688430cef215da210c33b48576884308fe805da210c23f60176884308fc805da210c23fe1776484308fe85dd9210c23f61776484308fc85dd9210c23fe1376484308fe84dd9210c23f61376484308fc84dd9210c23fe0f76484308fe83dd9210c23f20f76484308fd82dd9210c23f60776484308ff80dd9210c23fa0376484308fc80dd9210c23fe1576084308fe855d8210c23f61576084308fc855d8210c23fe1176084308fe845d8210c23f61176084308fc845d8210c23fa0d76084308fd835d8210c23f20d7608430cdf435d8210c33710d76084308fe825d8210c23f20976084308fe815d8210c23f2057608430cef215d8210c33d8857608430cf5215d8210c33b48576084308fe805d8210c23f60176084308fc805d8210c337cc17608430cdf85dd9300c337a17764c030cdd85dd9300c337217764c030cdf84dd9300c327e13764c030cde84dd9300c337613764c030cdc84dd9300c327213764c030cdf54dd9300c337953764c030cdd54dd9300c337153764c030cdf82dd9300c337a0b764c030cdd82dd9300c33720b764c030cdf52dd9300c33794b764c030cdd52dd9300c33714b764c030cdf42dd9300c33790b764c030cdd42dd9300c33710b764c030cdf81dd9300c337a07764c030cdd81dd9300c337207764c030cdf51dd9300c337947764c030cdd51dd9300c337147764c030cdf41dd9300c337907764c030cdd41dd9300c337107764c030cdf80dd9300c337a03764c030cdd80dd9300c337203764c030cdf50dd9300c337943764c030cdd50dd9300c337143764c030cdf40dd9300c337903764c030cdd40dd9300c337103764c030cdf20dd9300c337883764c030cdd20dd9300c337083764c030cdf10dd9300c337843764c030cdd10dd9300c337043764c030cdf76c85300c2d7a17214c030b5d85c85300c3671d3214c030bda80c85300c2f6603214c030cdf76885300c3671d2214c0309df87485300c27721d214c030cdf76485300c3671d1214c030ade86085300c
  | 7 => 0x1576887308fd855da21cc23f21576887308ff845da21cc23fa1176887308fd845da21cc23f21176887308fc835da21cc23fe0976887308fd825da21cc23fa0576887308fc815da21cc23fe0176887308ff85dd921cc23fa1776487308fd85dd921cc23f21776487308ff84dd921cc23fa1376487308fd84dd921cc23f21376487308fe83dd921cc23f60b76487308fd81dd921cc23f6037648730cdc30dd921cc23fe1576087308fe855d821cc23f61576087308fc855d821cc23fe1176087308fe845d821cc23f61176087308fc845d821cc23f20d76087308fe825d821cc23f20976087308fe815d821cc23f20576087308ff805d821cc23fe1576c86308fe855db218c23f61576c86308fc855db218c23fe1176c86308fe845db218c23f61176c86308fc845db218c23fe0d76c86308fd835db218c23f20976c86308ff815db218c23fa0176c86308fc805db218c23fe1576886308fe855da218c23f61576886308fc855da218c23fe1176886308fe845da218c23f61176886308fc845da218c23fe0d76886308fd835da218c23fe0976886308fd825da218c23fa0576886308fc815da218c23fa0176886308fc805da218c23fe1776486308fe85dd9218c23f61776486308fc85dd9218c23fe1376486308fe84dd9218c23f61376486308fc84dd9218c23fe0f76486308fd83dd9218c23f60b76486308fd81dd9218c23fa0376486308fc80dd9218c23fe1576086308fe855d8218c23f61576086308fc855d8218c23fe1176086308fe845d8218c23f61176086308fc845d8218c23fe0d76086308fd835d8218c337d0d7608630cdc435d8218c23fa0976086308fc825d8218c23fa0576086308fc815d8218c23fa0176086308fc805d8218c3374c17608630b5e85c87308c2d761721cc2309df87487308c27721d21cc230ade86087308c2b761821cc2308ff859db214c23fa1676c85308fd859db214c23f21676c85308ff849db214c23fa1276c85308fd849db214c23f21276c85308fd839db214c23f20e76c85308fe829db214c23f60676c8530cee219db214c33b08676c85308fd809db214c23f20276c85308ff859da214c23fa1676885308fd859da214c23f21676885308ff849da214c23fa1276885308fd849da214c23f21276885308fd839da214c23f20e76885308ff829da214c23f60a76885308fe819da214c23f2067688530cf7219da214c33d08676885308fd809da214c23f20276885308ff851d9214c23fa1476485308fd851d9214c23f21476485308ff841d9214c23fa1076485308fd841d9214c23f21076485308fd831d9214c23f20c76485308fd821d9214c23f6047648530cf7211d9214c33b8847648530cf4211d9214c33b08476485308fd801d9214c23f2007648530cde301d9214c23fe1676085308fe859d8214c23
  | 8 => 0x5c40f10228295e3c42850e1ca952a5c3052aab972e5cb880e3c78f1e3c78f10000000e5cb972e3c78f10000000e5cb972e3c78f10dc7886e5cb972e3c78f1162c58b162c58b00d195116300510c00051140005105c8172e2078814a1529805c8172e2078814a182874a5817205cb881e205285e5c92964a0b902e5c40f102212850c94b82e40b97103c408730243050a0b902e5c40f10218316121c3850a0b902e5c40f102184961014282e40b97103c4088105c4860c142a962cc005120017205cb881e2043980a1abd70a2017205cb881e2043062c143872c5828605c8172e2078810c582f2e420b162d5c286520b902e5c40f102204170a183050e0b902e5c40f10214b71e2582f2e4203880e2cb29160b902e5c40f102182f1e2182f2e4203880e685a9160b902e5c40f102942a50a96b561220c02e40b97103c40a50c152850e94b961218b02e40b97103c40a54a142a50c58482e40b97103c40884a152850c94bd6ac5c4872e9417205cb881e2042a54a14407101c59a4a2c17205cb881e2052854a14407101cb0b4a2f972e5cb900e3c78f1e3c78f10000000e5cb972e3c78f10000000e5cb972e3c78f10bc7885e5cb972e3c78f1162c58b162c58b018806262cc58c12000620a0006205c8172e2078810a1838805c8172e2078810c182852a5417205cb881e2042a72c59382e40b97103c40894e142952a0b902e5c40f10214308101c382e40b97103c40860c14295101ca82e40b97103c40855020b160e0b902e5c40f102254050a544072aa0007100017205cb881e204286ab543880e2438905c8172e2078810c182852c542950a14a8505c8172e2078810aa0b552d543160c18b06500b902e5c40f102a04850a14a850a54282e40b97103c40862dc78890a242960c2cb28160b902e5c40f102183f1e2242890a183a10c685a8160b902e5c40f10218506141c2850e2cca817c8102e40807209c40f1021850614542950a1d0910a545a8160b902e5c40f10214356ac9c3a70e24409100b902e5c40f102183050a54a850e14a851014a82e40b97103c40854e18b060e18b06100b902e5c40f102253850a54ad62a143852a144052a9c17205cb881e2043080c9c48512153864e1859a4e2c17205c807106078f102043160c5848512143160c1c3212c2d38b05c8172e2078810c2830a2a14a85e5c82870a545954e2c17205cb881e20430a0c284054e179724e153850a45087322d38be5cb972e3c78f1e3c78f10000000e5cb972e3c78f10000000e5cb972e3c78f10fc7887e5cb972e3c78f1162c58b162c58b0000400001c0008ff855db21cc23fa1576c87308fd855db21cc23f21576c87308ff845db21cc23fa1176c87308fd845db21cc23f21176c87308fc835db21cc23f20976c87308ff815db21cc23fe0176c87308ff855da21cc23fa
  | 9 => 0x3594b07454547c53dc5a03ac220f54ccc3144d14b0a84d952482bc2952b49b0a0930d4b009852c6bd4b142d3412a87f90154b14b1418f203b0f3810437ca5475005872c8942ecbf8a804a13bce14c114b00ed4b10bcc1845c7090d13f8514171028dbc10059c8d91f839c0ccfb54b08a4578e90ec0968a1cda4408f6cd584d8eb43a865c61477505061cdec9a0d98664a58308948a187212282e8de41bcabd0e80954b01913b14b14b093c5a876807cc94eb13800480f4bfcd5d0f8654f7926c0a52b87e47285bc988390b4919c04058d1b00bcd007e8e60b442644840d0d885c4110e043f4afc9701243c921c72403c3cca8cd4931c2680e0be458030ca68854900c0c60c7b8ec853025c22d4b08c83e5354538c489d14b09fcce0e543294b04e885c46c4e401cdd9394a0415d024e1828c0fd1b8b593e8d845d9010e69328ee51453e4360b7c9514b07852bd45c4707dca0d0584c0c806dd310a4490cd5411c049781c6adc180482080280d8008b26c80000f3d834c0297410a034290c52aa37d738ed00000800062004130e602a3720a40495d0041059784000a0003880d14616c4d8fe00234c5d0782ac3dc0000201609c0000902e1dc2680907e1601b03b0000081c81347e1603f8ed0560008185600a004399a202609c228670324dca00fd0081a812812080030068920ac0a404a180006042500003c0e4860020101a87f2250000283003f0ee50c018e41fc0080701900410c2304e002490bf1fa0102000584f018088e100003c2a80d8280120001081108c0e80a8421880e40780600203c0b07202603c000a0000094430080ee5a40280502a04c2200320005c000240001bc2a02e0987a01a803000008000060082ec220020fe070048050040187483720011c2f00f00400c4580600a0400e01300e1202b82c10e03c390530040800c8d906a0c8390000620a0008f900005c160021522c8070040120b4070130260100900a0560dc5f8000180202a80200c124b68040020000f01e29e07c1280400004c0480d0001cc0a011000000000090044000100002a0040f80400801c028010081640080000c0200389a0040ec0180603e0183a81b0000040008900a02c0100000a05c0800705c8172e2078812a1441505c8172e2078812e204050a1817205cb881e204c070a19502e40b97103c40950a143872a0b902e5c40f102543054c28a82e40b97103c40860c984050a28b82e40b97103c40860c98298140b902e5c40f10254371e2142874c28aa668c800a0c0017205cb881e204a850a9ab952a1417205cb881e2043261098285ab54b8705c8172e2078810c99305ab5ead73021302e40b97103c40950a142a60e54282e40b97103c408a0a542882a543052a0b902e5c40f1022831710202852e5c3070c0b902e5c40f10218c0a0e144060c0b902e
  | 10 => 0x4305b044904cfa47a8c55304214f60ea4cc8e484a4c6ce202f93081e857c83c97c0b46f44f52c053c8bcdd0211204520e78b7898cab86e94780b8cf47f0e0d488ee03a09a82c4284d3064cba8b18b892dcc9c4ecdcd3d4af4c74e24c08f91070338681408fd006132d060ed10c03b514881064123948c9242803a4d6d388d8d3ec1341c8690e74930138dc12951c0ac0aeca502002910006203510c933c9aca6c5b8b34e8c224a341f48f01951f08e0dd4600d10b2000cfbc050d1c2f1278a4cb8d1a52884e0ec54009049c8fd50ccbe877cebcfecea0890af11f4d7c2753a85ac44c17c2343d82b5098d04f48f0d0302dd1307e01dc27d0903781a81ec05ca60cd91d889d1152cc29cda0980144bc4444e3c6d9004b14610b25224a90f3c0f91ed018bc8908685038548e9c1e41790c40a0b548348512a4458c5076cc853252589b549525487113c0c421d38cb5c9e0c245c91601644fd074c3076505cdfcb691a8cc4ef52b070cce93f0b90d0d4414acff850c8413c88b500cc7c78c9340e84907c12848e46e09dd1241c49f4874584acce50b2cc294989782d48ac914f4c3710dcfacaa86d06704f08781e06c8888cd107c56d41ca5d3b420c99d4442e146418ce6ce38bd887cb981fd298bd49a4e94df0f1cca0cf0eb8074688044ef911cb741c04406b94146cc108c98bdcc643f8ae54b14b13303182f4c00f5cae90654b05f91383f04f827047c348d9c7106a0bccee8588b50b9c34c08075c5c00e51e4b6c45148410cc586b50f4e981142410d88050340890893fd34c7c8954e590b50788e8eace281b11bc8307bd17d3d89f8ddc9c11506592804c4a9848c3dd3486309742307408fc8451885404ad350510dac63cd50779320d75410f990b0374de05e8414ac8754168204e0884c140c1d3588b0460944d4078884888c69c2a40b0f2c1cc0acab4f701b45194b01f0d25104524a64734c385008244dcf75194b10f8c7d40101a0cd52d510c808c412900007fc9e4ffcb1cc052e0a9ccb48cd374828e00fc1468c6949c9bc82d2f851d39c79d361314480a104cccfd4b006cbb8e64dc4794a294b0c445291089394b0f441540853980710f13654590d42514b14b0b613d0380de81749c430489824c91c41909d02067d4b06484044948807d81a477137c12014ca78238228f58bd066112d1c83305ecba4f1467892cb80a008c47aca20eed4b07b46b06a80645582c81f838d1b49b92e4b952ac6a51103008d026c958a746f947118d0e0468c209954b1338188344d080204a94b086c0c86985cc118ce54b04994b12d936d47d4b14b14b14b11688194b05fc3c504832c11cd3903c80d068c4c02856055d2c54b0e3473d2084c8b312754494381d02ac6fcb3ca14465268694fcd4a09653ac0d54b05e4cb8e7c1601b940cac54b026108c3954a54b
  | 11 => 0x598f80c791202fcdb0f9c0313c516cd14b091c4b052fcad471cab02b82d1200278fe8fe10849e81ac6f0259185264d207d060523028805419d2206c05710403400250ecf345b5100ca43ed42433cd18990f94d44bec66911943d3e09992a05083891752e82a88005d4e300dd00922d4b009040d4b0f007cd1e0bf0a30a48a2d4b1140ae14b14214b0aa0fa074d4b0c147392705e14b07808b82542a128cd3c7f54b1251044f05344fdc478cecad85900042e53ccbe066cfa88f53a442c59468ced54b0bbc2994049d8d35460a7d01c364d60f084b4cb14b067460835d490d701d90b8bb462c5f11791e8208b70df8f28310d4c0390545a4e81234940730d80fe4c8c12c2c0aa4180c2cc894b0324625214438b38ca804c198f85475240aac5d121800935d094035244e5c4883fc158ecd1710a86443e8fb0a887484d495c0187b10e49613913f4884cbcc71429370d288c0e1c71525c629134f640f0b402d87ed29d451481300db4f50ff4bc03993781d51fc3bcf112d120cefcedc0c00790a514c6386c4b64700860568014bac2cc8205043b919927c130cf86d4e105f4c5c634838334f7caf88dc4010a0f8849d3c11d51a03d506ca3cfb8d792c8caca403e043cff0474815430c343693189205544bcdf43d1190db8e4013c1844b0718da8b0126081cf253851587a50fc0d86192f136896cd2c54c1284b91ad46cb2944d12802d1d08d408d164354f30149080ad0e84cc0b0c918d642187a00a8a24f188ec94d4b0e8816c428bb0cdd23cdc89291549f009d3a05448688a8068add4b053431ca714a845436c864f40b4c384650e2c248a94ba04353b8150e706ec9ec704fd85508a1434ed8c3d1cc9107592ed24c6aca389847992f4320e4c244bf4fc4420e4518041c858ea8fc85651dc2b03c115cc906e4b84ef057423c8f8d90410d692107904253349cd02c7605dd0acf689d4c614b0
  | _ => 0

def mainK7 : Nat → Nat
  | 0 => 0x37e31260085ff714c010bfce2980217f5c530042fe38a60086fe614c010bfee098021bf98130043fd98260087de304c010ff06098021f70c130043fb88260087fa104c010ff22098021bf5db20042febb640084fd76c8010bfeeb900217f9d720042febae40085fc75c8010dfecb90021bf997200437eb2e40086fc65c8010bfee9900217f9d320042feba640085fc74c8010dfec990021ef993200437f32640086be64c8010f7ac990021bf593200435eb2640086fc64c8010bfee7900217f9cf20042feb9e40085fc73c8010dfec790021bf98f200437eb1e40086fc63c8010bfce590021bfd8b200437f31640086fd62c8010df8c590021fb94b20043f6a9640085ff71c8010bfce3900217f5c720042fe38e40086fe61c8010bfae190021bf98320043fda8640087f850c8010ff44190021fb88320043f610640087f710c8010ff42190021fe443200437fbb240085ff76480109feec90021dfdd520042ffbaa400857f7548010bfcea900217f5d520043be3aa40085fc7548010af8ea90021bfd95200437f32a40086fd6548010df8ca900217fdd120042ff3a240085fd7448010bf8e890021bfd9120043df32240086fe6448010d7cc890021ef591200437eb2240086bd6448010df8c8900217fdcd20042ff39a40085fd7348010bf8e690021bfd8d200437f31a40086fd6348010df8c6900217fdc9200437fb1240086fe6248010dfac490021bf18920043f729240087ed5248010bfee2900217f9c520042feb8a40085fc7148010dfcc2900217fdc1200437f30240087fb2048010fdc4090021fe08120043f610240087f71048010ff42090021fe44120043fbbb220086f77644010beeec880213ddd910043fbbaa20087777544010fecea88021fd5d510043fa3aa20087747544010feeca88021fd99510043fab2a20087f46544010feee888021fd9d110043faba220087f47444010feec888021fd99110043db32220087f56444010f6ac888021fd19110043fbaa220087f65444010feaa888021fd15110043fbb9a20087f67344010feae688021fd1cd10043fbb1a20087f66344010feac688021fd18d10043fba9a20087f65344010feaa688021fd14d10043fba1a20087f64344010fea8688021fd10d10043fbb9220087f67244010feae488021fd1c910043fbb1220087f66244010feac488021fd18910043fba9220087f65244010feaa488021fd14910043fba1220087f64244010fea8488021fd10910043fb99220087f63244010fea6488021fd0c910043fbb8220087f37044010beee088021fd98110043f930220086f66044010feea088021fd94110043faa8220087f45044010fee8088021fd90110043faa0220087f44044010fee6088021fd8c110043fa98220087f43044010fee4088021fd88110043fa90220087f42044010
  | 1 => 0xdfeec990217fdd9320427fbb264086fe764c810bfcec990213f9d9320437ebb264085fd764c8109faec99021bf1d932042fe3b264084fc764c810bfeea990217f9d532042febaa64085fc754c810dfeca99021bf995320437eb2a64086fc654c810bfee8990217f9d132042feba264085fc744c810dfec899021ef991320437f32264086be644c810f7ac899021bf591320435eb2264086fc644c810dfec699021f798d320437f31a64086de634c810fbac699021bf58d320436eb1a64086fc634c810dfec499021fb989320437f31264086ee624c810fdac499021bf5893204376b1264086fc624c810fde6499021f78c932043fbb8a64085ff714c810beee2990217f9c532042feb8a64087f4714c810bf8e2990217d1c5320437f30a64085ff704c810bfce0990217f1c1320437f30264087f7104c810ff42099021fe441320437fbb064085ff760c8109feec19021bf9d832042ff3b064084fe760c810dfaec190217f5d8320427ebb064086fc760c810bf8ec190213f1d832042ffba864085fe750c810bfaea190217f1d4320437fb2864086fe650c810dfaca19021bf19432042ffba064085fe740c810bfae8190217f1d0320437fb2064087be640c810dfcc819021af99032043deb2064086fd640c810d7ac819021bf19032042ff39864086ff630c810dfcc619021bf58c320437e31864085fe720c810dfec419021bf988320437eb1064086fc620c810fbe6419021fb8c832043f699064087dd320c810bfee2190217f9c432042feb8864085fc710c810dfcc2190217f9c032042feb8064085fc700c810dfcc019021fdc4032043fd08064087f9100c810dfaed980217f5db300427ebb660085ff75cc010bfceb980217f5d730042fe3ae60086ff65cc010dfccb98021bf597300437e32e60085ff74cc010bfce9980217f5d330042fe3a660086ff64cc010f7cc998021bf993300435f32660087bd64cc010dfac998021af593300437e32660085fe73cc010dfec798021bf98f300437eb1e60086fc63cc010bfce5980217f5cb300437fb1660086fe62cc010dfac598021bf18b30042ffb8e60085fe71cc010bfae3980217f1c7300437f30e60085fd70cc010dfcc198021fed0330043fc20660087fa30cc010fbc6198021f70c330043fb88660087fa10cc010ff22198021bfdd930042ffbb260084ff764c010bfeea980217f9d530042febaa60085fc754c010dfeca98021bf995300437eb2a60086fc654c010f7ee8980217fdd130042dfba260085fe744c010bfae898021ef1d130042fe3a260085bc744c010dfec898021ef991300437f32260086be644c010f7ac898021bf591300435eb2260086fc644c010bfee698021bfd8d300437f31a60086fd634c010df8c6980217fdc930042fe39260086ff624c010dfcc498021bf5893004
  | 2 => 0x437eb2c408877c6588110df8cb102219f19620442ffba440885fe7488110bfae9102217f1d2204437fb2440886fe6488110dfac910221bf19220442ffb9c40885fe7388110bfae7102217f1ce204437fb1c40886fe6388110dfac710221bf18e20442feb9440886ff6288110dfcc510221bf58a204437e31440885ff7188110bfce3102217f5c620442fe38c40886ff6188110bfce110221bfd8220443fd28440887f95088110ff64110221fbc8220443f690440887fb1088110fec2110221fe042204437f3b040885fe76081109fcec102217fdd420443bf3a840885fe7508110afcea10221df5d420442feba8408857d7508110bf8ea10221dfd94204437fb28408867f6508110dfcca10221bf59420443be32840886fc6508110cf8ca102217fdd020442ff3a040885fd7408110bf8e810221bfd90204437f32040886fd6408110df8c8102217fdcc20442ff39840885fd7308110bf8e610221bfd8c204437f31840886fd6308110df8c6102217f9c8204437fb1040886fe6208110dfac410221bf18820442ffb8840885fe7108110bfae2102217f1c4204437fb0840885fe7008110dfec010221fbc8020443fd10040887f92008110fda4010221fec4020443fb08040887f81008110dfeed990217fddb320427fbb664086fe76cc810bfced990213f9db320437ebb664085fd76cc8109faed99021bf1db32042fe3b664084fc76cc810bfeeb990217f9d732042febae64085fc75cc810dfecb99021bf997320437eb2e64086fc65cc810bfee9990217f9d332042feba664085fc74cc810dfec999021ef993320437f32664086be64cc810f7ac999021bf593320435eb2664086fc64cc810dfec799021f798f320437f31e64086de63cc810fbac799021bf58f320436eb1e64086fc63cc810dfec599021bf98b320437eb1664086fc62cc810bfee3990217f9c732042feb8e64085fc71cc810dfcc3990217f9c332042feb8664085fc70cc810dfcc199021fdc4332043fd08664087f910cc810dfeed190217fdda320427fbb464086fe768c810bfced190213f9da320437ebb464085fd768c8109faed19021bf1da32042fe3b464084fc768c810bfeeb190217f9d632042febac64085fc758c810dfecb19021bf996320437eb2c64086fc658c810bfee9190217f9d232042feba464085fc748c810dfec919021ef992320437f32464086be648c810f7ac919021bf592320435eb2464086fc648c810bfae719021bfd8e320437f31c64086fd638c810df8c7190217f9ca320437fb1464087ee628c810dfcc519021bb98a32043f6b1464086fd628c810ddac519021bf18a32043f799464087df328c810bfee3190217f9c632042feb8c64085fc718c810dfcc3190217f9c232042feb8464085fc708c810dfcc119021fdc4232043fd08464087f9108c81
  | 3 => 0x10bfee8992217f9d132442feba264885fc744c910dfec899221bf991324437eb2264886fc644c910dfec699221bf98d324437eb1a64886fc634c910dfec499221bf989324437eb1264886fc624c910fde6499221f78c932442ffb8a64885fe714c910bfae2992217f1c532442ffb8264885fd704c910bf8e099221fec4132443fb08264886ff760c910bfeec192213fdd8324437f3b064885fe760c9109fcec19221bf5d832442febb064884fd760c910df8ec192217f1d8324427e3b064885ff750c910bfcea192217f5d432442fe3a8648877f650c910dfeca192219fd94324437f32864886fd650c910ef8ca19221bf194324433e32864885ff740c910bfce8192217f5d032442fe3a064886ff640c910dfcc819221bf590324437e32064885fe730c910fbec619221bfd8c324436fb1864886fe630c910dfac619221f718c324437e31864886dc630c910bfce419221fbd88324437fb1064886ef620c910dfcc419221bf58832443f631064886fc620c910dd8c419221f7cc832443f719064887ed320c910fba64192217fdc432443fb38864885fe710c910bece219221fd5c432442feb8864885f5710c910bf8e2192217fdc032442ff38064885fd700c910ff62019221fd840324437f3b460885fe768c1109fced182217fdd630442ff3ac60885fd758c110bf8eb18221dfd96304437fb2c608867f658c110dfccb18221bf59630443be32c60886fc658c110cf8cb182217fdd230442ff3a460885fd748c110bf8e918221bfd92304437f32460886fd648c110df8c9182217f5ce304437fb1c60886fe638c110dfac718221bf18e30443efa1c60887dc438c110bfce5182217f5ca304437fb1460886fe628c110dfac518221bf18a30442ffb8c60885fe718c110bfae3182217f1c6304437fb0c60885fe708c110dfec118221fe90230443fca0460887fb308c110fbe6118221f74c230443fd88460887f6108c110ff02118221bf9d830442ff3b060884fe760c110bfeea182217f9d430442feba860885fc750c110efeca18221bfd94304433fb2860886fe650c110dfaca18221df194304437e328608867c650c110bfee818221ef9d030442ff3a060885be740c110f7ae8182217f5d030442deba060885fc740c110dfec818221bf990304437eb2060886fc640c110bfce618221bfd8c304437f31860886fd630c110df8c618221f7d0c30443ee21860885fe720c110bfae418221bfd88304437f31060886fd620c110df8c4182217fdc430442ff38860885fd710c110bf8e218221bfd8430442ff38060886ff600c110fbe6018221fe8c030443fc98060887dd300c110ff62018221fd84030443fc08060886fe7688110bfced102213f9da20442ffbac40885fe7588110bfaeb102217f1d620443bfb2c40886ff6588110cfecb10221bf996204
  | 4 => 0x843fbbae21087f675c4210feaeb88421fd1d710843fbb2e21087f665c4210feacb88421fd19710843fbba621087f674c4210feae988421fd1d310843fbb2621087f664c4210feac988421fd19310843fbaa621087f654c4210feaa988421fd15310843fbb9e21087f673c4210feae788421fd1cf10843fbb1e21087f663c4210feac788421fd18f10843fba9e21087f653c4210feaa788421fd14f10843fba1e21087f643c4210fea8788421fd10f10843fbb9621087f672c4210feae588421fd1cb10843fbb1621087f662c4210feac588421fd18b10843fba9621087f652c4210feaa588421fd14b10843fba1621087f642c4210fea8588421fd10b10843fb99621087f632c4210fea6588421fd0cb10843fab8621087f170c4210fecc188421fc98310843fba8621087f650c4210feaa188421fd14310843fba0621087f640c4210fea8188421fd10310843fb98621087f630c4210fea6188421fd0c310843fb90621087f620c4210fea4188421fd083108437fbb664885ff76cc9109feed99221bf9db32442ff3b664884fe76cc910dfaed992217f5db324427ebb664886fc76cc910bf8ed992213f1db32442ffbae64885fe75cc910bfaeb992217f1d732443bfb2e64886ff65cc910cfecb99221bf997324437eb2e648877c65cc910df8cb992219f19732442ffba664885fe74cc910bfae9992217f1d3324437fb2664886fe64cc910dfac999221bf193324437fb1e64886fe63cc910dfac799221bf18f32443f7b1664886ff62cc910ddec599221bf98b324437eb1664887ec62cc910df8c599221bb18b32442ffb8e64885fe71cc910bfae3992217f1c732442ffb8664885fe70cc910bfae199221fec4332443fb08664886ff768c910bfeed192213fdda324437f3b464885fe768c9109fced19221bf5da32442febb464884fd768c910df8ed192217f1da324427e3b464885ff758c910bfceb192217f5d632442fe3ac648877f658c910dfecb192219fd96324437f32c64886fd658c910ef8cb19221bf196324433e32c64885ff748c910bfce9192217f5d232442fe3a464886ff648c910dfcc919221bf592324437e32464885fd738c910fbec719221bfd8e324436fb1c64886fe638c910dfac719221f718e324437e31c64886dc638c910bfce519221bfd8a324437f31464886fd628c910df8c519221fbcca32443ef99464885ff718c910bfce3192217f5c632442fe38c64885ff708c910bfce1192217f5c232443fd88464887f6108c910dfeec992217fdd9324427fbb264886fe764c910bfcec992213f9d9324437ebb264885fd764c9109faec99221bf1d932442fe3b264884fc764c910bfeea992217f9d532442febaa64885fc754c910efeca99221bfd95324433fb2a64886fe654c910dfaca99221df195324437e32a648867c654c9
  | 5 => 0xa109f8ec194217fdd432842ff3a865085fd750ca10bf8ea19421bfd94328437f32865086fd650ca10df8ca194217fdd032842ff3a065085fd740ca10bf8e819421bfd90328437f32065086fd640ca10df8c819421bfd8c328437f31865086fd630ca10df8c619421bfd88328437f31065086fd620ca10df8c419421f7cc832843f719065087ed320ca10fba64194217fdc432842ff38865085fd710ca10bf8e2194217f9c032842feb8065085fc700ca10ff62019421bf5db30842febb661085ff75cc210bfceb984217f5d730842fe3ae61086ff65cc210dfccb98421bf597308437e32e61085ff74cc210bfce9984217f5d330842fe3a661086ff64cc210dfcc998421bf593308437e32661086ff63cc210dfcc798421bf58f308437e31e61085fe72cc210bfae598421bfd8b308437f31661086fd62cc210df8c5984217fdc730842ff38e61085fd71cc210bf8e398421fe8c330843ef18661087dc30cc210ff62198421fd443308437fbb261085ff764c210bfeea984217f9d530842febaa61085fc754c210dfeca98421bf995308437eb2a61086fc654c210f7ee8984217fdd130842dfba261085fe744c210bfae898421ef1d130842fe3a261085bc744c210dfec898421bf991308437eb2261086fc644c210dfec698421bf98d308437eb1a61086fc634c210bfee4984217f1c9308437fb1261086fe624c210dfac498421bf18930842ffb8a61085fe714c210bfae2984217f1c530843fd20261087f9404c210ff66098421f78c130843fc18261087dc304c210ff62098421fd441308437ebb641085fd76c8210bfeeb904217f9d720842febae41085fc75c8210dfecb90421bf997208437eb2e41086fc65c8210bfee9904217f9d320842feba641085fc74c8210dfec990421bf993208437eb2641086fc64c8210bfee7904217f9cf20842feb9e41085fc73c8210dfec790421bf98f208437eb1e41086fc63c8210dfec590421bf98b208437eb1641086fc62c8210fdca590421fb54b20842ffb8e41085fe71c8210bfae3904217f1c720843fd10641087ee20c8210fd84190421fec4320843fa88641086ff7648210bfeec90421dfdd520842ffbaa410857f7548210bfcea904217f5d520843be3aa41085fc7548210af8ea90421bfd95208437f32a41086fd6548210df8ca904217fdd120842ff3a241085fd7448210bf8e890421bfd91208437f32241086fd6448210df8c8904217fdcd20842ff39a41085fd7348210bf8e690421bfd8d208437f31a41086fd6348210df8c690421bfd89208437f31241086fd6248210df8c490421fb94920843f6a9241085ff7148210bfce2904217f5c520842fe38a41087fa5048210ff2a090421fec8120843f710241087f82048210fd84090421fec4120843fa88241087f576c4210deaed884217d5db10
  | 6 => 0xc437fb1441886fe6288310dfac510621bf18a20c42ffb8c41885fe7188310bfae3106217f1c620c43fd90441887ef2088310fda4110621fe84220c43fa08441886fd7608310bfaec106217fdd420c43bf3a841885fe7508310afcea10621df5d420c42feba8418857d7508310bf8ea10621bfd9420c437f32841886fd6508310df8ca106217fdd020c42ff3a041885fd7408310bf8e810621bfd9020c437f32041886fd6408310df8c8106217fdcc20c42ff39841885fd7308310bf8e610621bfd8c20c437f31841886fd6308310df8c610621bfd8820c437f31041886fd6208310df8c4106217fdc420c42ff38841885fd7108310bf8e210621fed4020c43fc28041887ef2008310ff44010621fe48020c43f690041887fa1008310fe82010621bfddb32842ffbb665084ff76cca10dfced994217f9db328427f3b665086fd76cca10bfaed994213f5db328437e3b665085fc76cca109f8ed994217fdd732842ff3ae65085fd75cca10bf8eb99421bfd97328437f32e65086fd65cca10df8cb994217fdd332842ff3a665085fd74cca10bf8e999421bfd93328437f32665086fd64cca10df8c999421bfd8f328437f31e65086fd63cca10df8c799421bfd8b328437f31665086fd62cca10df8c5994217fdc732842ff38e65085fd71cca10bf8e3994217f9c332842feb8665085fc70cca10ff62199421bfdda32842ffbb465084ff768ca10dfced194217f9da328427f3b465086fd768ca10bfaed194213f5da328437e3b465085fc768ca109f8ed194217fdd632842ff3ac65085fd758ca10bf8eb19421bfd96328437f32c65086fd658ca10df8cb194217fdd232842ff3a465085fd748ca10bf8e919421bfd92328437f32465086fd648ca10df8c919421bfd8e328437f31c65086fd638ca10df8c719421bfd8a328437f31465086fd628ca10df8c519421fbcca32843ef99465085ff718ca10bfce3194217f5c632842fe38c65085fe708ca10bfae1194217f1c232843fd88465086ff764ca10bfeec994213fdd9328437f3b265085fe764ca109fcec99421bf5d932842febb265084fd764ca10df8ec994217f1d9328427e3b265085ff754ca10bfcea994217f5d532842fe3aa65086ff654ca10dfcca99421bf595328437e32a65085ff744ca10bfce8994217f5d132842fe3a265086ff644ca10dfcc899421bf591328437e32265086ff634ca10dfcc699421bf58d328437e31a65086ff624ca10dfcc499421bf589328437e31265087ef324ca10fbc6499421fddc532842ffb8a65085f7714ca10bfce2994217f5c532843fa38a65085fc714ca10be8e2994217fdc132842ff38265085fc704ca10ff62099421bfdd832842ffbb065084ff760ca10dfcec194217f9d8328427f3b065086fd760ca10bfaec194213f5d8328437e3b065085fc760c
  | 7 => 0xcb10bfee1196217f9c232c42feb8465886ff764cb10bfeec996213fdd932c437f3b265885fe764cb109fcec99621bf5d932c42febb265884fd764cb10df8ec996217f1d932c427e3b265885ff754cb10bfcea996217f5d532c42fe3aa65886ff654cb10dfcca99621bf59532c437e32a65885ff744cb10bfce8996217f5d132c42fe3a265886ff644cb10dfcc899621bf59132c437e32265886ff634cb10dfcc699621bf58d32c437e31a65886ff624cb10dfcc499621bf58932c437e31265887ef324cb10fbc64996217fdc532c42ff38a65885fd714cb10bf8e2996217fdc132c42feb8265885fc704cb10dfeec196217fdd832c427fbb065886fe760cb10bfcec196213f9d832c437ebb065885fd760cb109faec19621bf1d832c42fe3b065884fc760cb10bfeea196217f9d432c42feba865885fc750cb10dfeca19621bf99432c437eb2865886fc650cb10bfee8196217f9d032c42feba065885fc740cb10dfec819621bf99032c437eb2065886fc640cb10dfec619621bf98c32c437eb1865886fc630cb10dfec419621bf98832c437eb1065886fc620cb10fbe6419621fb8c832c43f699065887dd320cb10bfee219621fd9c432c42ff38865885f6710cb10feae2196217f5c432c42fab8865885fc710cb10bfee0196217f9c032c42feb8065886fd768c310bfaed186217fdd630c42ff3ac61885fd758c310bf8eb18621bfd9630c437f32c61886fd658c310df8cb186217fdd230c42ff3a461885fd748c310bf8e918621bfd9230c437f32461886fd648c310df8c918621bfd8e30c437f31c61886fd638c310df8c718621f7d0e30c43ee21c61885fe728c310bfae518621bfd8a30c437f31461886fd628c310df8c5186217fdc630c42ff38c61885fd718c310bf8e318621fecc230c43ef98461887dd308c310ff42118621fd04230c437ebb061885fd760c310bfeea186217f9d430c42feba861885fc750c310dfeca18621bf99430c437eb2861886fc650c310bfee818621ef9d030c42ff3a061885be740c310f7ae8186217f5d030c42deba061885fc740c310dfec818621bf99030c437eb2061886fc640c310dfec618621bf98c30c437eb1861886fc630c310fbe8618621f710c30c42ff39061885fd720c310dfec418621bf98830c437eb1061886fc620c310bfee2186217f9c430c42feb8861885fc710c310ff68018621fe10030c43ef98061887fa300c310ff26018621f74c030c43fd08061887f4100c310dfaed106217f5da20c42ffbac41885fe7588310bfaeb106217f1d620c437fb2c41886fe6588310dfacb10621bf19620c42ffba441885fe7488310bfae9106217f1d220c437fb2441886fe6488310dfac910621bf19220c42ffb9c41885fe7388310bfae7106217f1ce20c437fb1c41886fe6388310dfac710621bf18e2
  | 8 => 0x300833f32a601077d654c020dfaca980419f595300837e32a60107bf744c020bfee8980416fdd130082ff3a260105fd744c020f78e8980417f1d130082de3a260106ff644c020dfcc898041bf591300837e32260105ff734c020dfec698041bf98d300837eb1a60106fc634c020bfee4980417f9c930082feb9260105fc724c020dfcc4980417fdc530082fe38a60106fe614c020dfac2980417fdc1300837f30260107fb304c020fbc6098041fe0c130083ee18260107ef204c020ff44098041fe48130083f7bb240106ef7648020bdeec900413bdd920083f7baa401076f7548020fdcea90041fb5d520083f63aa401076c7548020fdeca90041bbd9520083f732a401076e6548020fdaca90041db5952008376b2a401066d6548020fd8ca90041fbdd120083f73a240107ed7448020fd8e890041fbd9120083f732240107ed6448020fd8c890041fbd5120083f72a240107ed5448020fd8a890041fbdcd20083f739a40107ed7348020fd8e690041fbd8d20083f731a40107ed6348020fd8c690041fbd4d20083f729a40107ed5348020fd8a690041fbd0d20083f721a40107ed4348020fd88690041fbdc520083f738a40107ed7148020fd8e290041fbd8520083f730a40107ed6148020fd8c290041fbd4520083f728a40107ed5148020fd8a290041fbd0520083f720a40107ed4148020fd88290041fbcc520083f718a40107ed3148020fd86290041fbdc120083f5b8240105ef7048020fdcc090041fa981200837730240107ef5048020fdca090041fb54120083f628240107ef4048020fdc8090041fb50120083f620240107ef3048020fdc6090041fb4c120083f618240106ff76ccb10bfeed996213fddb32c437f3b665885fe76ccb109fced99621bf5db32c42febb665884fd76ccb10df8ed996217f1db32c427e3b665885ff75ccb10bfceb996217f5d732c42fe3ae65886ff65ccb10dfccb99621bf59732c437e32e65885ff74ccb10bfce9996217f5d332c42fe3a665886ff64ccb10dfcc999621bf59332c437e32665886ff63ccb10dfcc799621bf58f32c437e31e65886ff62ccb10dfcc599621bf58b32c437e31665885ff71ccb10bfce3996217f5c732c42fe38e65885ff70ccb10bfce1996217f5c332c437fbb465885ff768cb109feed19621bf9da32c42ff3b465884fe768cb10dfaed196217f5da32c427ebb465886fc768cb10bf8ed196213f1da32c42ffbac65885fe758cb10bfaeb196217f1d632c437fb2c65886fe658cb10dfacb19621bf19632c42ffba465885fe748cb10bfae9196217f1d232c437fb2465886fe648cb10dfac919621bf19232c437fb1c65886fe638cb10dfac719621bf18e32c437fb1465886fe628cb10dfac519621bf18a32c43f799465887df328cb10bfee3196217f9c632c42feb8c65885fc718
  | 9 => 0x8c420dfcc918841bf592310837e32462105fd738c420dfec718841bf98e310837eb1c62106fc638c420bfee5188417f9ca31082feb9462105fc728c420dfcc5188417f9c6310837fb0c62107f6618c420dfcc318841bd98631083fab0c62106fd618c420deac318841bf18631083fb98c62107df318c420bfce1188417f5c231082fe38462106fe608c420fde4118841fe88231083fc90462106ff764c420bfeec988413fdd9310837f3b262105fe764c420dfaec988417f5d9310827ebb262106fc764c420bf8ec988413f1d931082ffbaa62105fe754c420bfaea988417f1d5310837fb2a621077e654c420dfcca988419f99531083beb2a62106fd654c420cfaca98841bf19531082ffba262105fe744c420bfae8988417f1d1310837fb2262106fe644c420dfac898841bf191310837fb1a62107de634c420dfcc698841b798d31083eeb1a62106fd634c420dbac698841bf18d31083f7b9262105ff724c420bdee4988417f9c931082feb9262107ec724c420bf8e4988417b1c9310837f31262106ff614c420fecc298841bf985310837b30a62107f5614c420dfac298841bd585310837e30a62107f7314c420fbc62988417fdc131082ff38262105fc704c420dfcc098841fbc8131083fd10262107f9204c420dfeec188417fdd8310827fbb062106fe760c420bfcec188413f9d8310837ebb062105fd760c4209faec18841bf1d831082fe3b062105ff750c420bfcea188417f5d431082fe3a862106ff650c420efcca18841bf994310833f328621077d650c420dfaca188419f594310837e32862105ff740c420bfce8188417f5d031082fe3a062106ff640c420dfcc818841bf590310837e32062105fe730c420dfec618841bf98c310837eb1862106fc630c420bfee4188417f9c831082feb9062105fc720c420dfcc4188417f9c4310837fb0862106fe610c420dfac218841bf18431083ef98862107f6310c420fea6218841f74c431082ff38062105fd700c420bf8e018841bf98031083f790062107fa200c420ff24018841bf5db30082febb660104fd76cc020bfeeb980417f9d730082febae60105fc75cc020dfecb98041df997300837f32e601067e65cc020efacb98041bf597300833eb2e60106fc65cc020bfee9980417f9d330082feba660105fc74cc020dfec998041bf993300837eb2660106fc64cc020bfce798041bfd8f300837f31e60106fd63cc020df8c7980417fdcb30082ff39660105fd72cc020bf8e598041bf98b30082ff38e60105fd71cc020dfcc398041bf58730082feb8660106fe60cc020ff6a198041fe14330083fd18660107de30cc020fb86198041fbc8330083fd10660107f920cc020dfeec980417fdd9300827fbb260105ff754c020bfcea980417f5d530082fe3aa60106ff654c020efcca98041bf995
  | 10 => 0x831482ff38862907f7610c520dfec218a41bdd84314837f30862906fd610c520fe8c218a41bf184314837a30862907df310c520fec6218a41fd4c431483ee98862905ff700c520bfce018a417f5c031483fd90062907ee200c520dfced182417f9da304827f3b460905ff758c120bfceb182417f5d630482fe3ac609077f658c120dfecb182419fd96304837f32c60906fd658c120ef8cb18241bf196304833e32c60905ff748c120bfce9182417f5d230482fe3a460906ff648c120dfcc918241bf592304837e32460905fd738c120dfec718241bf98e304837eb1c60906fc638c120fbe8718241f710e30482ffb9460905fe728c120bfae5182417f1ca304837fb1460907ee528c120fdaa5182417f9c630482feb8c60906ff618c120df8c3182417f9c2304837fb0460907fa408c120ff28118241fecc230483ef98460907dd308c120ff64118241fb88230483fc10460906fe760c120bfcec182413f9d830482ffba860905fe750c120bfaea182417f1d430483bfb2860906ff650c120cfeca18241bf994304837eb28609077c650c120df8ca182419f19430482ffba060907be740c120bfce8182416f9d030483deba060905fd740c120b7ae8182417f1d0304837fb2060906fe640c120dfac818241bf19030482ff39860906ff630c120dfcc618241bf58c304837e31860907df430c120fb886182417fdc830482ff39060905fd720c120bf8e418241bfd8830483f729060907ed520c120bfce2182417f5c4304837fb0860906fc610c120bfce018241bfd8030483ef98060907fa300c120ff26018241f74c030483fd90060907ee200c120ff04018241bfddb31082ffbb662104ff76cc420dfced988417f9db310827f3b662106fd76cc420bfaed988413f5db310837e3b662105fc76cc420bfeeb988417f9d731082febae62105fc75cc420dfecb98841df997310837f32e621067e65cc420efacb98841bf597310833eb2e62106fc65cc420bfee9988417f9d331082feba662105fc74cc420dfec998841bf993310837eb2662106fc64cc420dfec798841f798f310837f31e62106de63cc420fbac798841bf58f310836eb1e62106fc63cc420bfee5988417f9cb31082feb9662105fc72cc420dfcc598841bfd87310837f30e62106fd61cc420df8c3988417f9c331082feb8662105fc70cc420dfcc198841fbc8331083fd10662107f920cc420dfeed188417fdda310827fbb462106fe768c420bfced188413f9da310837ebb462105fd768c4209faed18841bf1da31082fe3b462105ff758c420bfceb188417f5d631082fe3ac62106ff658c420efccb18841bf996310833f32c621077d658c420dfacb188419f596310837e32c62105ff748c420f7ce9188417f9d231082df3a462107bd748c420bfae9188416f5d231082fe3a462106ff64
  | 11 => 0x6cc520df8ed98a417f1db314827e3b662905ff75cc520bfceb98a417f5d731482fe3ae629077f65cc520dfecb98a419fd97314837f32e62906fd65cc520ef8cb98a41bf197314833e32e62905ff74cc520bfce998a417f5d331482fe3a662906ff64cc520dfcc998a41bf593314837e32662906ff63cc520dfcc798a41bf58f314837e31e62905ff72cc520bfce598a417f5cb31482fe39662907ee52cc520fdaa598a41fdd87314837fb0e62906f761cc520dfcc398a41bf58731483fa30e62906fc61cc520de8c398a417fdc331482ff38662905fd70cc520ff64198a41fb883314837fbb462905ff768c520dfced18a417f9da314827f3b462906fd768c520bfaed18a413f5da314837e3b462905fc768c5209f8ed18a417fdd631482ff3ac62905fd758c520bf8eb18a41dfd96314837fb2c629067f658c520dfccb18a41bf59631483be32c62906fc658c520cf8cb18a417fdd231483df3a462905fe748c520b7ce918a41ef5d231482feba462905bd748c520bf8e918a41bfd92314837f32462906fd648c520df8c918a417f5ce31483efb1c62906ff638c520dbec718a41bf98e314837eb1c62907dc638c520df8c718a41b718e31482ffb9462905fe728c520bfae518a417f1ca31483f729462907ed528c520bfce318a41bfd86314837f30c62906fd618c520df8c318a41fdcc631483ef98c62905ff708c520bfce118a417f5c231483fd90462907ee208c520dfeec98a417fdd9314827fbb262906fe764c520bfcec98a413f9d9314837ebb262905fd764c520df8ec98a417f1d9314827e3b262905ff754c520bfcea98a417f5d531482fe3aa629077f654c520dfeca98a419fd95314837f32a62906fd654c520ef8ca98a41bf195314833e32a62905ff744c520bfce898a417f5d131482fe3a262906ff644c520dfcc898a41bf591314837e32262906ff634c520dfcc698a41bf58d314837e31a62905ff724c520bfce498a417f5c931482fe39262907ee524c520fdaa498a41bfd85314837f30a62906fd614c520df8c298a41fdcc531483ef18a62905ff704c520bfae098a417f1c131483fd90262907ee204c520dfeec18a417fdd8314837f3b062905fe760c5209fcec18a41bf5d831482febb062904fd760c520df8ec18a417f1d8314827e3b062905ff750c520bfcea18a417f5d431482fe3a8629077f650c520dfeca18a419fd94314837f32862906fd650c520ef8ca18a41bf194314833e32862905ff740c520bfce818a417f5d031482fe3a062906ff640c520dfcc818a41bf590314837e32062905fe730c520fbec618a41bfd8c314836fb1862906fe630c520dfac618a41f718c314837e31862906dc630c520bfee418a41fb9c831482ff39062905ee720c520fdae418a417f5c831482f6b9062905fc720c520fdca418a41fb54
  | 12 => 0xc131883fd90263106ff760c620bfeec18c413fdd8318837f3b063105fe760c6209fcec18c41bf5d831882febb063104fd760c620df8ec18c417f1d831882ffba863105fe750c620bfaea18c417f1d4318837fb2863106fe650c620dfaca18c41bf19431882ffba063105fe740c620bfae818c417f1d0318837fb2063106fe640c620dfac818c41bf190318837fb1863106fe630c620dfac618c41bf18c31882ffb9063105fe720c620bfae418c417f1c8318837fb0863106fe610c620dfac218c41bf18431883ef98863107f6310c620fea6218c41f74c431882ff38063105fd700c620bf8e018c41fec80318837ebb661105fd76cc220bfeeb984417f9d730882febae61105fc75cc220dfecb98441bf997308837eb2e61106fc65cc220bfee9984417f9d330882feba661105fc74cc220dfec998441bf993308837eb2661106fc64cc220dfec798441bf98f308837eb1e61106fc63cc220bfee5984417f9cb30882feb9661105fc72cc220bfce3984417f5c7308837f30e61106fd61cc220ff46198441f78c330883ee18661107fb20cc220fda4198441bfdd930882ffbb261105ff754c220bfcea984417f5d530882fe3aa61106ff654c220dfcca98441bf595308837e32a61107bf744c220bfee8984416fdd130882ff3a261105fd744c220f78e8984417f1d130882de3a261106ff644c220dfcc898441bf591308837e32261106ff634c220dfcc698441bf58d308837e31a61105ff724c220bfce4984417f5c930882fe39261105ff714c220bf8e298441bf985308837eb0a61107fa404c220ff28098441fecc130883ef18261107f8304c220fb86098441fec8130883f690261107ed76c8220ddaed904417b5db20883f7bae41107ee75c8220fdaeb90441fb1d720883f7b2e41106ef65c8220fdccb90441fb5972088376b2e41107ec65c8220fdee990441fb9d320883f6ba641107ec74c8220fdec990441fb99320883f6b2641107ec64c8220fdea990441fb95320883f6aa641107ec54c8220fdee790441fb9cf20883f6b9e41107ec73c8220fdec790441fb98f20883f6b1e41107ec63c8220fdea790441fb94f20883f6a9e41107ec53c8220fde8790441fb90f20883f6a1e41107ec43c8220fdee390441fb9c720883f6b8e41107ec71c8220fdec390441fb98720883f6b0e41107ec61c8220fdea390441fb94720883f6a8e41107ec51c8220fde8390441fb90720883f6a0e41107ec41c8220fde6390441fb8c720883f698e41107ec31c8220fdae190441fa5c320883f730641107ea60c8220fdea190441fb94320883f6a8641107ec50c8220fde8190441fb90320883f6a0641107ec40c8220fde6190441fb8c320883f698641107ec30c8220dfeed98a417fddb314837f3b662905fe76cc5209fced98a41bf5db31482febb662904fd7
  | 13 => 0x648c320dfcc918641bf59230c837e32461906ff638c320dfcc718641bf58e30c837e31c61907df438c320fb887186417fdca30c82ff39461905fd728c320bf8e518641fb94a30c83f6a9461905fe718c320bfae318641bf98630c837eb0c61907fb308c320fbe6118641f74c230c83fd10461907ec208c320dfaec186417f5d830c82ffba861905fe750c320bfaea186417f1d430c837fb2861906fe650c320dfaca18641bf19430c82ffba061907be740c320bfce8186416f9d030c83deba061905fd740c320b7ae8186417f1d030c837fb2061906fe640c320dfac818641bf19030c837fb1861906fe630c320dfac618641bf18c30c83efa1861907dc430c320bfee4186417f9c830c82feb9061905fc720c320fdca418641fb54830c82ff38861905fd710c320dfcc218641bf58430c83fda8061907f8500c320fbe6018641fe8c030c83fc98061907dd300c320ff44018641fb08030c837fbb663105ff76cc6209feed98c41bf9db31882ff3b663104fe76cc620dfaed98c417f5db318827ebb663106fc76cc620bf8ed98c417fdd731882ff3ae63105fd75cc620bf8eb98c41bfd97318837f32e63106fd65cc620df8cb98c417fdd331882ff3a663105fd74cc620bf8e998c41bfd93318837f32663106fd64cc620df8c998c41bfd8f318837f31e63106fd63cc620df8c798c417fdcb31882ff39663105fd72cc620bf8e598c41bfd87318837f30e63106fd61cc620df8c398c417f9c331882feb8663105fc70cc620ff64198c41bfdda31882ffbb463104ff768c620dfced18c417f9da318827f3b463106fd768c620bfaed18c413f5da318837e3b463105fc768c620bfeeb18c417f9d631882febac63105fc758c620dfecb18c41bf996318837eb2c63106fc658c620bfee918c41ef9d231882ff3a463105be748c620f7ae918c417f5d231882deba463105fc748c620dfec918c41bf992318837eb2463106fc648c620dfec718c41bf98e318837eb1c63106fc638c620bfee518c417f9ca31882feb9463105fc728c620dfec318c41bf986318837eb0c63106fc618c620fee6318c41f7cc631882ff38463105fd708c620bf8e118c41fec82318837fbb263105ff764c6209feec98c41bf9d931882ff3b263106fd764c620bfaec98c413f5d9318837e3b263105fc764c6209f8ec98c417fdd531882ff3aa63105fd754c620bf8ea98c41bfd95318837f32a63106fd654c620df8ca98c417fdd131882ff3a263105fd744c620bf8e898c41bfd91318837f32263106fd644c620df8c898c41bfd8d318837f31a63106fd634c620df8c698c41fbdc931882ffb9263105ef724c620bfce498c417f5c931883f639263105fc724c620bd8e498c41bfd85318837f30a63106fd614c620df8c298c41fdcc531883ef18a63105ff704c620bfce098c417f1
  | 14 => 0xd01300c3ef20260187dd404c030fb88098061bfddb31c82ffbb663904ff76cc720dfced98e417f9db31c827f3b663906fd76cc720bfaed98e413f5db31c837e3b663905fc76cc720bfeeb98e417f9d731c82febae63905fc75cc720dfecb98e41bf99731c837eb2e63906fc65cc720bfee998e417f9d331c82feba663905fc74cc720dfec998e41bf99331c837eb2663906fc64cc720dfec798e41bf98f31c837eb1e63906fc63cc720bfee598e417f9cb31c82feb9663905fc72cc720fdca598e41fb54b31c837fb0e63906fe61cc720dfac398e41bf18731c82ffb8663905fe70cc720bfae198e41bfdda31c82ffbb463904ff768c720dfced18e417f9da31c827f3b463906fd768c720bfaed18e413f5da31c837e3b463905fc768c720bfeeb18e417f9d631c82febac63905fc758c720dfecb18e41bf99631c837eb2c63906fc658c720bfee918e41ef9d231c82ff3a463905be748c720f7ae918e417f5d231c82deba463905fc748c720dfec918e41bf99231c837eb2463906fc648c720dfec718e41bf98e31c837eb1c63906fc638c720bfee518e417f9ca31c82feb9463905fc728c720fdca518e41fb54a31c837fb0c63906fe618c720dfac318e41bf18631c83fb98c63907df318c720bfee118e417f9c231c82feb8463906ff764c720bfeec98e413fdd931c837f3b263905fe764c720dfaec98e417f5d931c827ebb263906fc764c720bf8ec98e413f1d931c82ffbaa63905fe754c720bfaea98e417f1d531c837fb2a63906fe654c720dfaca98e41bf19531c82ffba263905fe744c720bfae898e417f1d131c837fb2263906fe644c720dfac898e41bf19131c837fb1a63906fe634c720dfac698e41bf18d31c82ffb9263905fe724c720bfae498e417f1c931c83f729263907ed524c720dfec298e41bf98531c837eb0a63906fc614c720fee6298e41f78c531c82ffb8263905fd704c720bf8e098e41bfdd831c82ffbb063904ff760c720dfcec18e417f9d831c827f3b063906fd760c720bfaec18e413f5d831c837e3b063905fc760c720bfeea18e417f9d431c82feba863905fc750c720dfeca18e41bf99431c837eb2863906fc650c720bfee818e417f9d031c82feba063905fc740c720dfec818e41bf99031c837eb2063906fc640c720dfec618e41bf98c31c837eb1863906fc630c720bfee418e41fb9c831c82ff39063905ee720c720fdae418e417f5c831c82f6b9063905fc720c720fdca418e41fb54831c837fb0863906fe610c720dfac218e41bf18431c83ef98863907f6310c720fea6218e41f74c431c82ffb8063905fe700c720bfae018e41bf5da30c82febb461905ff758c320bfceb186417f5d630c82fe3ac61906ff658c320dfccb18641bf59630c837e32c61905ff748c320bfce9186417f5d230c82fe3a461906ff
  | 15 => 0xe7088430bfae1108617f1c2210c37f30442187df3088430ff46110861fe4c2210c37fbb242185ff76484309feec90861bf9d9210c2ff3b242186fd7648430bfaec908613f5d9210c37e3b242185fc76484309f8ec908617fdd5210c2ff3aa42185fd7548430bf8ea90861bfd95210c37f32a42186fd6548430df8ca908617fdd1210c2ff3a242185fd7448430bf8e890861bfd91210c3df32242186fe6448430d7cc890861ef591210c37eb2242186bd6448430df8c890861f7dcd210c2ffb9a42185df7348430bfce6908617f5cd210c3ee39a42185fc7348430bb8e690861bf98d210c3efa1a42187dc4348430dfec490861fb989210c37f31242186ee6248430fdac490861bf589210c376b1242186fc6248430dfec290861fd985210c37f30a42186f66148430feac290861bf585210c37ab0a42186fc6148430fee4290861fb885210c2ffb8242185fe7048430bf8e090861bf981210c3ef98242187fa3048430ff26090861bfdd8210c2ffbb042184ff7608430dfcec108617f9d8210c27f3b042186fd7608430bfaec108613f5d8210c37e3b042185fc7608430bfeea108617f9d4210c2feba842185fc7508430dfeca10861bf994210c37eb2842186fc6508430bfee8108617f9d0210c2feba042185fc7408430dfec810861ef990210c37f32042186be6408430f7ac810861bf590210c35eb2042186fc6408430bfee6108617f9cc210c2feb9842185fc7308430dfcc610861f7d0c210c3ee21842185fe7208430dfec410861bf988210c37eb1042186fc6208430bfce210861bfd84210c37f30842186fd6108430df8c210861fbc84210c3fb10842187f52108430fda42108617f9c0210c2feb8042185fc7008430dfcc010861f7cc0210c3fd18042187f93008430fbeec98061b7dd9300c2efbb260184df764c030fbeea98061f79d5300c3eebaa60187dc754c030fbeca98061f7995300c3eeb2a60187dc654c030fbee898061e7dd1300c3ef3a260185de744c030fbae898061f71d1300c3ce3a260185dc744c030b38e898061f7d91300c3ef322601879e644c030fbac898061e7591300c3ee32260187df544c030fbca898061f7551300c3ee2a260187df724c030fbce498061f75c9300c3ee39260187df624c030fbcc498061f7589300c3ee31260187df524c030fbca498061f7549300c3ee29260187df424c030fbc8498061f7509300c3ee21260187df714c030fbce298061f75c5300c3ee38a60187df614c030fbcc298061f7585300c3ee30a60187df514c030fbca298061f7545300c3ee28a60187df414c030fbc8298061f7505300c3ee20a60187df214c030fbc4298061f7485300c3ee10a60187df704c030fb6e09806177dc1300c3ef30260187da604c030dbcc098061f7d41300c3ef28260187dd504c030fb8a098061f7
  | 16 => 0xf5d1214c2fe3a242987bf6448530dfec890a61afd91214c37f32242986fd6448530f78c890a61bf191214c35e32242985ff7348530bfce690a617f5cd214c2fe39a42986ff6248530dfcc490a61bf589214c37e31242986ff6148530dfcc290a61bf585214c37e30a42987f72148530fdc4290a617fdc1214c2feb8242985fc7048530ff66090a61f78c1214c37fbb042985ff7608530dfcec10a617f9d8214c27f3b042986fd7608530bfaec10a613f5d8214c37e3b042985fc76085309f8ec10a617fdd4214c2ff3a842985fd7508530bf8ea10a61bfd94214c37f32842986fd6508530df8ca10a617fdd0214c2ff3a042985fd7408530bf8e810a61efd90214c37fb2042986bf6408530dfcc810a61bf590214c3de32042986fc6408530d78c810a617fdcc214c3ef39842985fe7308530bbce610a61f75cc214c2feb9842985dd7308530bf8e610a617f9c8214c3f7b1042986ff6208530ddec410a61bf988214c37eb1042987ec6208530df8c410a61bb188214c2ff38842987f76108530dfec210a61bdd84214c37f30842986fd6108530fe8c210a61bf184214c37a30842987ef2108530fec4210a61fd484214c3f690842985ff7008530bfce010a617f5c0214c3fd98042987de3008530dfeed908617fddb210c27fbb642186fe76c8430bfced908613f9db210c37ebb642185fd76c84309faed90861bf1db210c2fe3b642185ff75c8430efceb908617f9d7210c2bf3ae421877d75c8430bfaeb908615f5d7210c2fe3ae42186ff65c8430dfccb90861bf597210c37e32e42185ff74c8430bfce9908617f5d3210c2fe3a642186ff64c8430f7cc990861bf993210c35f32642187bd64c8430dfac990861af593210c37e32642185ff73c8430bfce7908617f5cf210c2fe39e42186fe63c8430fbe8790861f710f210c37fb1642187ee62c8430dfcc590861bb98b210c3f6b1642186fd62c8430ddac590861bf18b210c37fb0e42186fe61c8430dfac390861bf187210c2ff38642185fd70c8430bf8e190861bf983210c3ef98642187fa30c8430ff26190861bfdda210c2ffbb442184ff7688430dfced108617f9da210c27f3b442186fd7688430bfaed108613f5da210c37e3b442185fc7688430bfeeb108617f9d6210c2febac42185fc7588430dfecb10861bf996210c37eb2c42186fc6588430bfee9108617f9d2210c2feba442185fc7488430dfec910861ef992210c37f32442186be6488430f7ac910861bf592210c35eb2442186fc6488430bfee7108617f9ce210c2feb9c42185fc7388430dfcc710861f7d0e210c3ee21c42185fd7288430dfec510861bf98a210c37eb1442186fc6288430bfce310861bfd86210c3fb30c42186fe6188430decc310861fd586210c37eb0c42186f56188430df8c310861fdc86210c3f790c42185f
  | 17 => 0xfe7008630bfae010c617f1c0218c3fd98043187dd76cc230dbaed98461775db308c3efbae61187de75cc230fbaeb98461f71d7308c3efb2e61187de65cc230fbacb98461f7197308c3efba661187de74cc230bbce998461f75d3308c3ee3a661185dc74cc230fbec998461f7993308c3eeb2661187dc64cc230fbea998461f7953308c3eeaa661187dc54cc230fbee598461f79cb308c3eeb9661187dc72cc230fbec598461f798b308c3eeb1661187dc62cc230fbea598461f794b308c3eea9661187dc52cc230fbe8598461f790b308c3eea1661187dc42cc230fbee398461f79c7308c3eeb8e61187dc71cc230fbec398461f7987308c3eeb0e61187dc61cc230fbea398461f7947308c3eea8e61187dc51cc230fbe8398461f7907308c3eea0e61187dc41cc230fbe4398461f7887308c3ee90e61187dc21cc230fbae198461f65c3308c3ef30661187da60cc230fbea198461f7943308c3eea8661187dc50cc230fbe8198461f7903308c3eea0661187dc40cc230dfeed90a617fddb214c37f3b642985fe76c85309fced90a61bf5db214c2febb642984fd76c8530df8ed90a617f1db214c27e3b642985ff75c8530efceb90a617f9d7214c2bf3ae429877d75c8530bfaeb90a615f5d7214c2fe3ae42986ff65c8530dfccb90a61bf597214c37e32e42985ff74c8530bfce990a617f5d3214c2fe3a642987bf64c8530dfec990a61afd93214c37f32642986fd64c8530f78c990a61bf193214c35e32642985ff73c8530bfce790a617f5cf214c2fe39e42986ff62c8530dfcc590a61bf58b214c37e31642987f761c8530dfec390a61bdd87214c37f30e42986fd61c8530fe8c390a61bf187214c37a30e42985ff70c8530bfce190a617f5c3214c3fd98642987de30c8530dfeed10a617fdda214c37f3b442985fe76885309fced10a61bf5da214c2febb442984fd7688530df8ed10a617f1da214c27e3b442985ff7588530bfceb10a617f5d6214c2fe3ac42986ff6588530dfccb10a61bf596214c37e32c42985ff7488530bfce910a617f5d2214c2fe3a442987bf6488530dfec910a61afd92214c37f32442986fd6488530f78c910a61bf192214c35e32442985ff7388530bfce710a617f5ce214c2fe39c42985fd7288530fdec510a61bfd8a214c377b1442986fe6288530dfac510a61fb18a214c37e31442986ec6288530bfce310a61bfd86214c37f30c42986fd6188530df8c310a61fdc86214c3f790c42985ff7088530bfce110a617f5c2214c3fd98442987de3088530dfeec90a617fdd9214c27fbb242986fe7648530bfcec90a613f9d9214c37ebb242985fd7648530df8ec90a617f1d9214c27e3b242985ff7548530bfcea90a617f5d5214c2fe3aa42986ff6548530dfcca90a61bf595214c37e32a42985ff7448530bfce890a617
  | 18 => 0x7f5cc21cc2eeb9843985fc7308730dfec410e61bf98821cc37eb1043986fc6208730dfec210e61bf98421cc37eb0843986fc6108730fde4210e61fd88421cc3fa90843987ed2108730bfee010e617f9c021cc2feb8043986ff76c8630bfeed90c613fddb218c37f3b643185fe76c86309fced90c61bf5db218c2febb643184fd76c8630df8ed90c617f1db218c2ffbae431877e75c8630bfceb90c615f9d7218c3bebae43185fd75c8630afaeb90c617f1d7218c37fb2e43186fe65c8630dfacb90c61bf197218c2ffba643185fe74c8630bfae990c617f1d3218c37fb2643186fe64c8630dfac990c61bf193218c2ffb9e43185fe73c8630bfae790c617f1cf218c3efa1e43187dc43c8630dfec590c61bf98b218c37eb1643186fc62c8630dfec390c61bf987218c37eb0e43186fc61c8630bfce190c617f5c3218c2fe38643187fb30c8630dfeed10c617fdda218c27fbb443186fe7688630bfced10c613f9da218c37ebb443185fd76886309faed10c61bf1da218c2fe3b443185ff7588630bfceb10c617f5d6218c2fe3ac43186ff6588630dfccb10c61bf596218c37e32c43185ff7488630bfce910c617f5d2218c2fe3a443186ff6488630dfcc910c61bf592218c37e32443185ff7388630bfce710c617f5ce218c2fe39c43187df4388630fb88710c61bfd8a218c37f31443186fd6288630df8c510c61bfd86218c37f30c43186fd6188630df8c310c61fdc86218c3f790c43185fe7088630bfae110c617f1c2218c3fd98443186ff7648630bfeec90c613fdd9218c37f3b243185fe7648630dfaec90c617f5d9218c27ebb243186fc7648630bf8ec90c613f1d9218c2ffbaa43185fe7548630bfaea90c617f1d5218c37fb2a43186fe6548630dfaca90c61bf195218c2ffba243185fe7448630bfae890c617f1d1218c37fb2243186fe6448630dfac890c61bf191218c3efb9a43185ff7348630bbee690c617f9cd218c2feb9a43187dc7348630bf8e690c61771cd218c3efa1a43187dc4348630dfec490c61bf989218c37eb1243186fc6248630dfec290c61bf985218c37eb0a43186fc6148630fee4290c61fb885218c2ffb8243185fe7048630bf8e090c61fecc1218c37fbb043185ff76086309feec10c61bf9d8218c2ff3b043184fe7608630dfaec10c617f5d8218c27ebb043186fc7608630bf8ec10c617fdd4218c2ff3a843185fd7508630bf8ea10c61bfd94218c37f32843186fd6508630df8ca10c617fdd0218c2ff3a043185fd7408630bf8e810c61bfd90218c37f32043186fd6408630df8c810c617fdcc218c2ff39843185fd7308630bf8e610c61f7d0c218c3ee21843186ff6208630dfcc410c61bf588218c37e31043186ff6108630dfcc210c61bf584218c37e30843187ef2108630fec4210c61fd484218c3f690843185
  | 19 => 0xcfd7158021df8e2b00433f1c5600877fa8ac010efe5158021dfaa2b0043bf145600877fa0ac010efe4158021dfa82b0043bf105600877f98ac010efe3158021dfa62b0043bf0c5600877f90ac010efe2158021dfa42b0043bf085600877fb82c010efb70580219fee0b0043bfd41600877f282c010efa5058021dfaa0b0043be541600877e282c010eff4058021dfc80b0043bf501600877e202c010eff2058021df640b0043bf881600877e902c010efc2058021df040b0043bfc41600877d882c010efe1058021dfa20b0043bf041600877c082c010eff76c8730bfeed90e613fddb21cc37f3b643985fe76c87309fced90e61bf5db21cc2febb643984fd76c8730df8ed90e617f1db21cc2ffbae439877e75c8730bfceb90e615f9d721cc3bebae43985fd75c8730afaeb90e617f1d721cc37fb2e43986fe65c8730dfacb90e61bf19721cc2ffba643985fe74c8730bfae990e617f1d321cc37fb2643986fe64c8730dfac990e61bf19321cc2ffb9e43985fe73c8730bfae790e617f1cf21cc37fb1643986fe62c8730dfac590e61bf18b21cc37fb0e43986fe61c8730dfac390e61bf18721cc2ffb8643985fe70c8730bfae190e61bfdda21cc2ffbb443984ff7688730dfced10e617f9da21cc27f3b443986fd7688730bfaed10e613f5da21cc37e3b443985fc7688730bfeeb10e617f9d621cc2febac43985fc7588730dfecb10e61bf99621cc37eb2c43986fc6588730bfee910e617f9d221cc2feba443985fc7488730dfec910e61bf99221cc37eb2443986fc6488730bfee710e617f9ce21cc2feb9c43985fc7388730dfec510e61bf98a21cc37eb1443986fc6288730dfec310e61bf98621cc37eb0c43986fc6188730fee4310e61fbc8621cc2ffb8443985fe7088730bfae110e61bfdd921cc2ffbb243984ff7648730dfcec90e617f9d921cc37ebb243985fd76487309faec90e61bf1d921cc2fe3b243984fc7648730bfeea90e617f9d521cc2febaa43985fc7548730dfeca90e61bf99521cc37eb2a43986fc6548730bfee890e617f9d121cc2feba243985fc7448730dfec890e61bf99121cc37eb2243986fc6448730bfee690e617f9cd21cc2feb9a43985fc7348730dfec490e61bf98921cc37eb1243986fc6248730dfec290e61bf98521cc37eb0a43986fc6148730fee4290e61fb88521cc2ffb8243985fd7048730bf8e090e61bfdd821cc2ffbb043984ff7608730dfcec10e617f9d821cc27f3b043986fd7608730bfaec10e613f5d821cc37e3b043985fc7608730bfeea10e617f9d421cc2feba843985fc7508730dfeca10e61bf99421cc37eb2843986fc6508730bfee810e617f9d021cc2feba043985fc7408730dfec810e61bf99021cc37eb2043986fc6408730bfee610e61f79cc21cc2ff39843985de7308730fbae610e61
  | 20 => 0x3bf548604877e290c090eff4218121dfc8430243bf508604877e210c090eff3218121dfc6430243bf4c8604877e190c090eff71181219fce230243bf5c4604867eb88c090cfc7118121dfea230243bf944604877ea88c090efc5118121dfe8230243bf904604877ea08c090efc4118121dfe6230243bf8c4604877e988c090efc3118121dfe4230243bf884604877e908c090efc2118121dfce030243be9c0604867f380c090eff5018121df6a030243bf940604877ea80c090efc5018121df0a030243bfd00604877f200c090efd4018121df88030243bfc80604877f100c090efa2018121dfa4030243be480604877e100c090eff1018121dfc2030243be840604877e880c090ef91018121df82030243bfdd6600867fbacc010efe75980219fceb30043bf5d6600867ebacc010efc75980219f8eb30043bfdd2600867fba4c010efe74980219fce930043bf5d2600867eba4c010efc74980219f8e930043bfd52600877f2a4c010efd5498021df8a930043bfdce600877f39cc010cfe7398021dfae7300433f5ce600877e39cc010eff5398021dfca730043bf54e600877e29cc010eff4398021dfc8730043bf50e600877e21cc010efe72980219fce530043bf1ca600867e394c010eff5298021dfca530043bf54a600877e294c010eff4298021dfc8530043bf50a600877e214c010eff3298021dfc6530043bf4ca600877e194c010efe71980219fce330043bf1c6600867e38cc010eff5198021dfca330043bf546600877e28cc010eff4198021dfc8330043bf506600877e20cc010eff3198021dfc6330043bf4c6600877e18cc010eff2198021dfc4330043bf486600877e10cc010efe7098021df4e1300433f9c2600877fa84c010efe5098021df4a130043bf542600877ca84c010efc5098021dfe8130043bf902600877ea04c010efc4098021dfe4130043bec82600877f104c010efd2098021df84130043be082600877f884c010efb1098021dfc2130043bf442600877e084c010ef81098021dfeeab00439fdd5600867fbaac010c7f7558021dfceab00433f9d5600877ebaac010cfd7558021df8eab00439f1d5600867e3aac010c7c7558021dfee8b00433fdd1600877f3a2c010cfe7458021dfae8b00433f5d1600877e3a2c010cfc7458021dfea8b0043bf951600877eaa2c010efc5458021dfee6b00433fdcd600877f39ac010efd7358021df8e6b00433f1cd600877fa9ac010efe5358021dfaa6b0043bf14d600877fa1ac010efe4358021dfa86b0043bf10d600867fb92c010efe72580219fce4b00433f5c9600877e392c010cfc7258021dfea4b0043bf949600877ea92c010efc5258021dfe84b0043bf909600877ea12c010efc4258021dfe64b0043bf8c9600877e992c010efc32580219fee2b0043bf9c5600867f38ac010
  | 21 => 0xefc74582219f8e8b0443bfd51608877f2a2c110efd5458221df8a8b0443bfdcd608867fb9ac110efe7358221dfae6b0443bf1cd608867e39ac110eff5358221dfca6b0443bf54d608877e29ac110eff4358221dfc86b0443bf50d608877e21ac110eff72582219fee4b0443bf5c9608877fa92c110efe5258221dfaa4b0443bf149608877fa12c110efe4258221dfa84b0443bf109608877f992c110efe3258221dfa64b0443bf0c9608877f38ac110efc71582219f8e2b0443bfd45608877f28ac110efd5158221df8a2b0443bfd05608877f20ac110efd4158221df882b0443bfcc5608877f18ac110efd3158221df862b0443bfc85608877f10ac110efd2158221df842b0443bfdc1608877db82c110eff5058221dfca0b0443bf541608877e282c110eff4058221dfc80b0443bf501608877e202c110eff2058221dfc40b0443be881608877e902c110ef92058221df840b0443bfc41608877d882c110efe1058221dfa20b0443bf041608877c082c110eff75d81219feebb0243bf9d7604867f3aec090efd75d81219faebb0243bf1d7604867e3aec090eff74d81219fee9b0243bf9d3604867f3a6c090efd74d81219fae9b0243bf1d3604867e3a6c090eff54d8121dfca9b0243bf553604877e2a6c090eff73d8121dfce7b02433f9cf604877eb9ec090cfd73d8121df8e7b0243bfd4f604877f29ec090efd53d8121df8a7b0243bfd0f604877f21ec090efd43d8121df887b0243bfdcb604877eb96c090cfd72d8121dfea5b0243bf94b604877ea96c090efc52d8121dfe85b0243bf90b604877ea16c090efc42d8121dfe65b0243bf8cb604877e996c090efc32d8121dfee3b0243bf5c7604867eb8ec090eff51d8121dfca3b0243bf547604877e28ec090eff41d8121dfc83b0243bf507604877e20ec090eff31d8121dfc63b0243bf4c7604877e18ec090eff21d8121dfc43b0243bf487604877e10ec090efd70d8121df2e1b02433f5c3604877fa86c090efb50d8121dfca1b0243bf543604877e286c090ef850d8121dfe81b0243bf903604877ea06c090efc40d8121dfe41b0243bf883604877d106c090efd20d8121df241b0243bf083604877f886c090efe10d8121df421b0243bf443604877c886c090efc10d8121dfeea302433fdd4604877f3a8c090cfe7518121dfaea302433f5d4604877e3a8c090cfc7518121dfee8302433fdd0604877f3a0c090cfe7418121dfae8302433f5d0604877e3a0c090cfc7418121dfea830243bf950604877eaa0c090efc5418121dfee630243bf9cc604867f398c090efd73181219fae630243bf1cc604877fa98c090efe5318121dfaa630243bf14c604877fa18c090efe4318121dfa8630243bf10c604877fb90c090cfe7218121dfae4302433f5c8604867e390c090eff5218121dfca43024
  | 22 => 0x43bfd0260c877f204c190efd4098321df88130643bfc8260c877d904c190efe2098321dfa4130643bf08260c877c104c190eff1098321dfc2130643be84260c877e884c190ef91098321df82130643bfdd560c867fbaac190efe75583219fceab0643bf5d560c867ebaac190efc75583219f8eab0643bfdd160c867fba2c190efe74583219fce8b0643bf5d160c867eba2c190efc74583219f8e8b0643bfd5160c877f2a2c190efd5458321df8a8b0643bfdcd60c867fb9ac190efe7358321dfae6b0643bf1cd60c867e39ac190eff5358321dfca6b0643bf54d60c877e29ac190eff4358321dfc86b0643bf50d60c877e21ac190efe7258321df8e4b06433f1c960c877fa92c190efe5258321dfaa4b0643bf14960c877fa12c190efe4258321dfa84b0643bf10960c877f992c190efe3258321dfa64b0643bf0c960c877fb8ac190cff7158321dfae2b0643bfd4560c877f28ac190efd5158321df8a2b0643bfd0560c877f20ac190efd4158321df882b0643bfcc560c877f18ac190efd3158321df862b0643bfc8560c877f10ac190efd2158321df842b0643bfdc160c877db82c190eff5058321dfca0b0643bf54160c877e282c190eff4058321dfc80b0643bf50160c877e202c190eff2058321df640b0643bf88160c877e902c190efc2058321df040b0643bfc4160c877f082c190efa1058321dfa20b0643be44160c877e082c190eff75982219feeb30443bf9d6608867f3acc110efd75982219faeb30443bf1d6608867e3acc110eff74982219fee930443bf9d2608867f3a4c110efd74982219fae930443bf1d2608867e3a4c110eff5498221dfca930443bf552608877e2a4c110eff7398221dfce7304433f9ce608877eb9cc110cfd7398221df8e730443bfd4e608877f29cc110efd5398221df8a730443bfd0e608877f21cc110efd4398221df88730443bfdca608877eb94c110cfd7298221dfea530443bf94a608877ea94c110efc5298221dfe8530443bf90a608877ea14c110efc4298221dfe6530443bf8ca608877e994c110efc3298221dfce3304433f9c6608877e38cc110eff5198221dfca330443bf546608877e28cc110eff4198221dfc8330443bf506608877e20cc110eff3198221dfc6330443bf4c6608877e18cc110eff2198221dfc4330443bf486608877e10cc110efe7098221df4e130443bfd42608877f284c110efd5098221df8a130443bfd02608877f204c110efd4098221df88130443bfc82608877f104c110efa2098221dfa4130443be482608877e104c110eff1098221df62130443bf842608877e884c110efc1098221df02130443bfdd5608867fbaac110efe75582219fceab0443bf5d5608867ebaac110efc75582219f8eab0443bfdd1608867fba2c110efe74582219fce8b0443bf5d1608867eba2c11
  | 23 => 0x18efd5198031df8a330063bfd06600c77f20cc018efd4198031df88330063bfcc6600c77f18cc018efd3198031df86330063bfc86600c77f10cc018efd2198031df84330063bf9c2600c77d384c018cfe7098031dfea130063bf942600c77ea84c018efc5098031dfe8130063bf902600c77d204c018efd4098031df28130063bf102600c77f984c018efb3098031dfc6130063bf4c2600c77e184c018ef83098031dfe2130063bec42600c77f084c018efd1098031df82130063be042600c77fbaac018cff7558031dfceab00633f9d5600c77ebaac018cfd7558031df8eab00633f1d5600c77fba2c018cff7458031dfce8b00633f9d1600c77eba2c018cfd7458031df8e8b00633f1d1600c77faa2c018efe5458031dfaa8b0063bf151600c67fb9ac018efe73580319fce6b00633f5cd600c77e39ac018cfc7358031dfea6b0063bf94d600c77ea9ac018efc5358031dfe86b0063bf90d600c77ea1ac018efc4358031dfee4b00633fdc9600c77f392c018efd7258031df8e4b00633f1c9600c77fa92c018efe5258031dfaa4b0063bf149600c77fa12c018efe4258031dfa84b0063bf109600c77f992c018efe3258031dfa64b0063bf0c9600c77f38ac018cfe7158031df8e2b00633f1c5600c77fa8ac018efe5158031dfaa2b0063bf145600c77fa0ac018efe4158031dfa82b0063bf105600c77f98ac018efe3158031dfa62b0063bf0c5600c77f90ac018efe2158031dfa42b0063bf085600c77fb82c018efb70580319fee0b0063bfd41600c77f282c018efd5058031df8a0b0063bfd01600c77f202c018efa4058031dfa80b0063be501600c77e202c018eff3058031df660b0063bf8c1600c77e982c018efc3058031df060b0063bfc41600c77d882c018efe1058031dfa20b0063bf041600c77c082c018eff75983219feeb30643bf9d660c867f3acc190efd75983219faeb30643bf1d660c867e3acc190eff74983219fee930643bf9d260c867f3a4c190efd74983219fae930643bf1d260c867e3a4c190eff5498321dfca930643bf55260c877e2a4c190eff7398321dfce7306433f9ce60c877eb9cc190cfd7398321df8e730643bfd4e60c877f29cc190efd5398321df8a730643bfd0e60c877f21cc190efd4398321df88730643bf9ca60c867f394c190efc7298321dfea530643bf94a60c877ea94c190efc5298321dfe8530643bf90a60c877ea14c190efc4298321dfe6530643bf8ca60c877e994c190efc3298321dfee330643bf5c660c867eb8cc190eff5198321dfca330643bf54660c877e28cc190eff4198321dfc8330643bf50660c877e20cc190eff3198321dfc6330643bf4c660c877e18cc190eff2198321dfc4330643bf48660c877e10cc190efe7098321df4e130643bfd4260c877f284c190efd5098321df8a1306
  | 24 => 0x263bf94b604c77ea96c098efc52d8131dfe85b0263bf90b604c77ea16c098efc42d8131dfe65b0263bf8cb604c77e996c098efc32d8131dfee3b0263bf5c7604c67eb8ec098eff51d8131dfca3b0263bf547604c77e28ec098eff41d8131dfc83b0263bf507604c77e20ec098eff31d8131dfc63b0263bf4c7604c77e18ec098eff21d8131dfc43b0263bf487604c77e10ec098efd70d8131df2e1b02633f5c3604c77fa86c098efe50d8131dfaa1b0263bf143604c77fa06c098efb40d8131dfc81b0263bf503604c77e206c098ef840d8131dfe61b0263bf8c3604c77d186c098efd30d8131df261b0263bf0c3604c77f886c098efe10d8131df421b0263bf443604c77c886c098efc10d8131dfeea302633fdd4604c77f3a8c098cfe7518131dfaea302633f5d4604c77e3a8c098cfc7518131dfee8302633fdd0604c77f3a0c098ebe74181319fce8302632f9d0604c77eba0c098ebd74181319fae8302632f5d0604c77e3a0c098cfc7418131dfea830263bf950604c77eaa0c098efc5418131dfee6302633f9cc604c77eb98c098cfd73181319f8e630263bfd4c604c77f298c098efd5318131df8a630263bfd0c604c77f218c098efd4318131df88630263bfdc8604c77f390c098cfe7218131dfae4302633f5c8604c77e390c098eff5218131dfca430263bf548604c77e290c098eff4218131dfc8430263bf508604c77e210c098eff3218131dfc6430263bf4c8604c77e190c098eff7118131dfae2302633f5c4604c77fa88c098efe5118131dfaa230263bf144604c77fa08c098efe4118131dfa8230263bf104604c77f988c098efe3118131dfa6230263bf0c4604c77f908c098efe2118131dfa4230263bf084604c77f380c098efa70181319fce030263bfd40604c77f280c098efd5018131df8a030263bfd00604c77da00c098efe4018131dfa8030263bf100604c77c200c098eff3018131dfc6030263be8c0604c77e980c098ef93018131df86030263bfc40604c77f080c098efa1018131dfa2030263be440604c77e080c098eff75980319feeb30063bf9d6600c67f3acc018efd75980319faeb30063bf1d6600c67e3acc018eff74980319fee930063bf9d2600c67f3a4c018efd74980319fae930063bf1d2600c67e3a4c018eff5498031dfca930063bf552600c77e2a4c018efe73980319fce730063bf1ce600c67e39cc018eff5398031dfca730063bf54e600c77e29cc018eff4398031dfc8730063bf50e600c77e21cc018eff7298031dfce5300633f9ca600c77eb94c018cfd7298031df8e530063bfd4a600c77f294c018efd5298031df8a530063bfd0a600c77f214c018efd4298031df88530063bfcca600c77f194c018efd3298031df86530063bf9c6600c67f38cc018efc71980319f8e330063bfd46600c77f28cc0
  | 25 => 0x118eff74982319fee930463bf9d2608c67f3a4c118efd74982319fae930463bf1d2608c67e3a4c118eff5498231dfca930463bf552608c77e2a4c118eff7398231dfae7304633f5ce608c77fa9cc118efe5398231dfaa730463bf14e608c77fa1cc118efe4398231dfa8730463bf10e608c77fb94c118efe72982319fce530463bf5ca608c67eb94c118efc7298231dfea530463bf94a608c77ea94c118efc5298231dfe8530463bf90a608c77ea14c118efc4298231dfe6530463bf8ca608c77e994c118efc3298231dfce3304633f9c6608c77e38cc118eff5198231dfca330463bf546608c77e28cc118eff4198231dfc8330463bf506608c77e20cc118eff3198231dfc6330463bf4c6608c77e18cc118eff2198231dfc4330463bf486608c77e10cc118efe7098231df4e130463bfd42608c77f284c118efd5098231df8a130463bfd02608c77f204c118efd4098231df88130463bfcc2608c77f184c118efa3098231dfa6130463be4c2608c77e184c118eff1098231df62130463bf842608c77e884c118efc1098231df02130463bfdd5608c67fbaac118efe75582319fceab0463bf5d5608c67ebaac118efc75582319f8eab0463bfdd1608c67fba2c118efe74582319fce8b0463bf5d1608c67eba2c118efc74582319f8e8b0463bfd51608c77f2a2c118efd5458231df8a8b0463bfdcd608c67fb9ac118efd7358231dfea6b0463bf94d608c77ea9ac118efc5358231dfe86b0463bf90d608c77ea1ac118efc4358231dfee4b04633fdc9608c77f392c118efd7258231df8e4b04633f1c9608c77fa92c118efe5258231dfaa4b0463bf149608c77fa12c118efe4258231dfa84b0463bf109608c77f992c118efe3258231dfa64b0463bf0c9608c77f38ac118efc71582319f8e2b0463bfd45608c77f28ac118efd5158231df8a2b0463bfd05608c77f20ac118efd4158231df882b0463bfcc5608c77f18ac118efd3158231df862b0463bfc85608c77f10ac118efd2158231df842b0463bfdc1608c77db82c118eff5058231dfca0b0463bf541608c77e282c118eff4058231dfc80b0463bf501608c77e202c118eff3058231dfc60b0463be8c1608c77e982c118ef93058231df860b0463bfc41608c77d882c118efe1058231dfa20b0463bf041608c77c082c118eff75d81319feebb0263bf9d7604c67f3aec098efd75d81319faebb0263bf1d7604c67e3aec098eff74d81319fee9b0263bf9d3604c67f3a6c098efd74d81319fae9b0263bf1d3604c67e3a6c098eff54d8131dfca9b0263bf553604c77e2a6c098eff73d8131dfae7b02633f5cf604c77fa9ec098efe53d8131dfaa7b0263bf14f604c77fa1ec098efe43d8131dfa87b0263bf10f604c77fb96c098efe72d81319fce5b0263bf5cb604c67eb96c098efc72d8131dfea5b0
  | 26 => 0x65bfd41600cb7f282c0196fd5058032df8a0b0065bfd01600cb7f202c0196fa4058032dfa80b0065be501600cb7e202c0196ff3058032df660b0065bf8c1600cb7e982c0196fc3058032df060b0065bfc81600cb7d902c0196fe2058032dfa40b0065bf081600cb7c102c0196ff75983319feeb30663bf9d660cc67f3acc198efd75983319faeb30663bf1d660cc67e3acc198eff74983319fee930663bf9d260cc67f3a4c198efd74983319fae930663bf1d260cc67e3a4c198eff5498331dfca930663bf55260cc77e2a4c198efe73983319fce730663bf1ce60cc77fa9cc198efe5398331dfaa730663bf14e60cc77fa1cc198efe4398331dfa8730663bf10e60cc77fb94c198efe72983319fce530663bf5ca60cc67eb94c198efc7298331dfea530663bf94a60cc77ea94c198efc5298331dfe8530663bf90a60cc77ea14c198efc4298331dfe6530663bf8ca60cc77e994c198efc3298331dfee330663bf5c660cc67eb8cc198eff5198331dfca330663bf54660cc77e28cc198eff4198331dfc8330663bf50660cc77e20cc198eff3198331dfc6330663bf4c660cc77e18cc198eff2198331dfc4330663bf48660cc77e10cc198efe7098331df4e130663bfd4260cc77f284c198efd5098331df8a130663bfd0260cc77f204c198efd4098331df88130663bfcc260cc77d984c198efe3098331dfa6130663bf0c260cc77c184c198eff1098331dfc2130663be84260cc77e884c198ef91098331df82130663bfdd560cc67fbaac198efe75583319fceab0663bf5d560cc67ebaac198efc75583319f8eab0663bfdd160cc67fba2c198efe74583319fce8b0663bf5d160cc67eba2c198efc74583319f8e8b0663bfd5160cc77f2a2c198efd5458331df8a8b0663bf9cd60cc77e39ac198cfc7358331dfea6b0663bf94d60cc77ea9ac198efc5358331dfe86b0663bf90d60cc77ea1ac198efc4358331dfee4b06633fdc960cc77f392c198efd7258331df8e4b06633f1c960cc77fa92c198efe5258331dfaa4b0663bf14960cc77fa12c198efe4258331dfa84b0663bf10960cc77f992c198efe3258331dfa64b0663bf0c960cc77fb8ac198cff7158331dfae2b0663bfd4560cc77f28ac198efd5158331df8a2b0663bfd0560cc77f20ac198efd4158331df882b0663bfcc560cc77f18ac198efd3158331df862b0663bfc8560cc77f10ac198efd2158331df842b0663bfdc160cc77db82c198eff5058331dfca0b0663bf54160cc77e282c198eff4058331dfc80b0663bf50160cc77e202c198eff3058331df660b0663bf8c160cc77e982c198efc3058331df060b0663bfc4160cc77f082c198efa1058331dfa20b0663be44160cc77e082c198eff75982319feeb30463bf9d6608c67f3acc118efd75982319faeb30463bf1d6608c67e3acc
  | 27 => 0xc0996fc7118132dfea230265bf944604cb7ea88c0996fc5118132dfe8230265bf904604cb7ea08c0996fc4118132dfe6230265bf8c4604cb7e988c0996fc3118132dfe4230265bf884604cb7e908c0996fc2118132dfce030265be9c0604ca7f380c0996ff5018132df6a030265bf940604cb7ea80c0996fc5018132df0a030265bfd00604cb7f200c0996fd4018132df88030265bfcc0604cb7f180c0996fa3018132dfa6030265be4c0604cb7e180c0996ff2018132dfc4030265be880604cb7e900c0996f92018132df84030265bfdd6600ca7fbacc0196fe75980329fceb30065bf5d6600ca7ebacc0196fc75980329f8eb30065bfdd2600ca7fba4c0196fe74980329fce930065bf5d2600ca7eba4c0196fc74980329f8e930065bfd52600cb7f2a4c0196fd5498032df8a930065bf9ce600ca7f39cc0196fc73980329f8e730065bfd4e600cb7f29cc0196fd5398032df8a730065bfd0e600cb7f21cc0196fd4398032df88730065bf9ca600ca7f394c0196fc72980329f8e530065bfd4a600cb7f294c0196fd5298032df8a530065bfd0a600cb7f214c0196fd4298032df88530065bfcca600cb7f194c0196fd3298032df86530065bfdc6600cb7f38cc0194fe7198032dfae3300653f5c6600cb7e38cc0196ff5198032dfca330065bf546600cb7e28cc0196ff4198032dfc8330065bf506600cb7e20cc0196ff3198032dfc6330065bf4c6600cb7e18cc0196ff2198032dfc4330065bf486600cb7e10cc0196fe7098032df4e1300653f9c2600cb7fa84c0196fe5098032dfaa130065bf142600cb7fa04c0196fe4098032df48130065bf502600cb7ca04c0196fc4098032dfe6130065becc2600cb7f184c0196fd3098032df86130065be0c2600cb7f904c0196fb2098032dfc4130065bf482600cb7e104c0196f82098032dfeeab00653fdd5600cb7f3aac0194fe7558032dfaeab00653f5d5600cb7e3aac0194fc7558032dfee8b00653fdd1600cb7f3a2c0194fe7458032dfae8b00653f5d1600cb7e3a2c0194fc7458032dfea8b0065bf951600cb7eaa2c0196fc5458032dfce6b00653f9cd600cb7e39ac0194fc7358032dfea6b0065bf94d600cb7ea9ac0196fc5358032dfe86b0065bf90d600cb7ea1ac0196fc4358032dfce4b00653f9c9600cb7e392c0194fc7258032dfea4b0065bf949600cb7ea92c0196fc5258032dfe84b0065bf909600cb7ea12c0196fc4258032dfe64b0065bf8c9600cb7e992c0196fc3258032dfee2b00653fdc5600cb7f38ac0196fd7158032df8e2b00653f1c5600cb7fa8ac0196fe5158032dfaa2b0065bf145600cb7fa0ac0196fe4158032dfa82b0065bf105600cb7f98ac0196fe3158032dfa62b0065bf0c5600cb7f90ac0196fe2158032dfa42b0065bf085600cb7fb82c0196fb70580329fee0b
  | 28 => 0xb0465bf94d608cb7ea9ac1196fc5358232dfe86b0465bf90d608cb7ea1ac1196fc4358232dfce4b0465bf1c9608ca7e392c1196ff5258232dfca4b0465bf549608cb7e292c1196ff4258232dfc84b0465bf509608cb7e212c1196ff3258232dfc64b0465bf4c9608cb7e192c1196ff71582329fee2b0465bf9c5608cb7eb8ac1196fc71582329f8e2b0465bfd45608cb7f28ac1196fd5158232df8a2b0465bfd05608cb7f20ac1196fd4158232df882b0465bfcc5608cb7f18ac1196fd3158232df862b0465bfc85608cb7f10ac1196fd2158232df842b0465bfdc1608cb7db82c1196ff5058232dfca0b0465bf541608cb7e282c1196ff4058232dfc80b0465bf501608cb7e202c1196ff3058232dfc60b0465be8c1608cb7e982c1196f93058232df860b0465bfc81608cb7d902c1196fe2058232dfa40b0465bf081608cb7c102c1196ff75d81329feebb0265bf9d7604ca7f3aec0996fd75d81329faebb0265bf1d7604ca7e3aec0996ff74d81329fee9b0265bf9d3604ca7f3a6c0996fd74d81329fae9b0265bf1d3604ca7e3a6c0996ff54d8132dfca9b0265bf553604cb7e2a6c0996ff73d8132dfae7b02653f5cf604cb7fa9ec0996fe53d8132dfaa7b0265bf14f604cb7fa1ec0996fe43d8132dfa87b0265bf10f604cb7fb96c0996fd72d81329fae5b0265bfd4b604cb7f296c0996fd52d8132df8a5b0265bfd0b604cb7f216c0996fd42d8132df885b0265bfccb604cb7f196c0996fd32d8132df865b0265bfdc7604cb7f38ec0994fe71d8132dfae3b02653f5c7604cb7e38ec0996ff51d8132dfca3b0265bf547604cb7e28ec0996ff41d8132dfc83b0265bf507604cb7e20ec0996ff31d8132dfc63b0265bf4c7604cb7e18ec0996ff21d8132dfc43b0265bf487604cb7e10ec0996fd70d8132df2e1b02653f5c3604cb7fa86c0996fb50d8132dfca1b0265bf543604cb7e286c0996f850d8132dfe81b0265bf903604cb7ea06c0996fc40d8132dfe61b0265bf8c3604cb7d186c0996fd30d8132df261b0265bf0c3604cb7f906c0996fe20d8132df441b0265bf483604cb7c906c0996fc20d8132dfeea302653fdd4604cb7f3a8c0994fe7518132dfaea302653f5d4604cb7e3a8c0994fc7518132dfee8302653fdd0604cb7f3a0c0994fe7418132dfae8302653f5d0604cb7e3a0c0994fc7418132dfea830265bf950604cb7eaa0c0996fc5418132dfee630265bf5cc604ca7eb98c0996ff5318132dfca630265bf54c604cb7e298c0996ff4318132dfc8630265bf50c604cb7e218c0996ff7218132dfae4302653f5c8604cb7fa90c0996fe5218132dfaa430265bf148604cb7fa10c0996fe4218132dfa8430265bf108604cb7f990c0996fe3218132dfa6430265bf0c8604cb7fb88c0996fe71181329fce230265bf5c4604ca7eb88
  | 29 => 0x4c1996ff2098332dfc4130665be88260ccb7e904c1996f92098332df84130665bfdd560cca7fbaac1996fe75583329fceab0665bf5d560cca7ebaac1996fc75583329f8eab0665bfdd160cca7fba2c1996fe74583329fce8b0665bf5d160cca7eba2c1996fc74583329f8e8b0665bfd5160ccb7f2a2c1996fd5458332df8a8b0665bf9cd60ccb7e39ac1994fc7358332dfea6b0665bf94d60ccb7ea9ac1996fc5358332dfe86b0665bf90d60ccb7ea1ac1996fc4358332dfee4b06653fdc960ccb7eb92c1996ff5258332dfca4b0665bf54960ccb7e292c1996ff4258332dfc84b0665bf50960ccb7e212c1996ff3258332dfc64b0665bf4c960ccb7e192c1996ff71583329fee2b0665bf9c560ccb7eb8ac1996fc71583329f8e2b0665bfd4560ccb7f28ac1996fd5158332df8a2b0665bfd0560ccb7f20ac1996fd4158332df882b0665bfcc560ccb7f18ac1996fd3158332df862b0665bfc8560ccb7f10ac1996fd2158332df842b0665bfdc160ccb7db82c1996ff5058332dfca0b0665bf54160ccb7e282c1996ff4058332dfc80b0665bf50160ccb7e202c1996ff3058332df660b0665bf8c160ccb7e982c1996fc3058332df060b0665bfc8160ccb7f102c1996fa2058332dfa40b0665be48160ccb7e102c1996ff75982329feeb30465bf9d6608ca7f3acc1196fd75982329faeb30465bf1d6608ca7e3acc1196ff74982329fee930465bf9d2608ca7f3a4c1196fd74982329fae930465bf1d2608ca7e3a4c1196ff5498232dfca930465bf552608cb7e2a4c1196ff7398232dfae7304653f5ce608cb7fa9cc1196fe5398232dfaa730465bf14e608cb7fa1cc1196fe4398232dfa8730465bf10e608cb7f394c1194fe7298232df8e530465bfd4a608cb7f294c1196fd5298232df8a530465bfd0a608cb7f214c1196fd4298232df88530465bfcca608cb7f194c1196fd3298232df86530465bfdc6608cb7f38cc1194fe7198232dfae3304653f5c6608cb7e38cc1196ff5198232dfca330465bf546608cb7e28cc1196ff4198232dfc8330465bf506608cb7e20cc1196ff3198232dfc6330465bf4c6608cb7e18cc1196ff2198232dfc4330465bf486608cb7e10cc1196fe7098232df4e130465bfd42608cb7f284c1196fd5098232df8a130465bfd02608cb7f204c1196fd4098232df88130465bfcc2608cb7f184c1196fa3098232dfa6130465be4c2608cb7e184c1196ff2098232df64130465bf882608cb7e904c1196fc2098232df04130465bfdd5608ca7fbaac1196fe75582329fceab0465bf5d5608ca7ebaac1196fc75582329f8eab0465bfdd1608ca7fba2c1196fe74582329fce8b0465bf5d1608ca7eba2c1196fc74582329f8e8b0465bfd51608cb7f2a2c1196fd5458232df8a8b0465bfdcd608ca7fb9ac1196fd7358232dfea6
  | 30 => 0xa90b2c398b173d02aa2ab400a9040aa8a9649659451651519498a38a38c38c2cd030d40d41452b42a48aaaa28aaaab2aaaa38ea9042aa9664f42d4009649659451651519498a38a38c38c2b0cb0cb638aacd32d12ac390b50d4f8e2b16b4f44ed500259259651459454652638a28b58a68e30e30b43503158e2ab34cb44a40e40f42d3b4b2c5cf44ecd00259259651459454652628e28e30e30acd2cccd44d53248b40a40e40f42b3e592a5b33d13ab40092b9299249659451651519498a38a38c38c2ab4b2b351354aaa2aa2aa390ad0cceaaaa973d139339338e3b338138e3a59259459459628e28e38c30cf8c708d39454e30d3ce2922ce3ce3ce598cd13cf38aa8aa8e3ab3802aa2a59259459459628e28e38c30cf8c70ac32c32caaaa8a2cea922acaaa3ceace598ad13cf3ad38032c30cb0cb0e3a59259459459628e28e38c30cf8c708d3ac52c30cb4f38a2ce4922acaad390b2cb0e3ce62c5d13cf38aa8aa8e3ab3802aa2a59259459459628e28e38c30cf8c70b231434eaaa2aa2aaaacaaa3ceace598ad13cf3b53809649651651658a38a38e30c33e31c2d0c50d3aaccf2d32ce3ce3ceb518e2b16d4f3ceb4e02592594594592d8a68e38a28e38c30cf8c70ac32c32ccab3cb4cb3acb0f3b542cb2c5cf3ceace0259259459459628e28e38c30cf8c70aad2cacd54d3aaa8aa8b964a8f3ab3b346592a5ab3cf3b33819249649339291651658a38a38e30c33e31c2b32b3535534ecce2922e594e3ce3cead0ab2a973cf38e40e0659659644659659638e38e38e388f8e38e389041040e38e3e59659638e389041040e38e3e59659638e388000000e38e38e4659659638e38965965965965eff75983329feeb30665bf9d660cca7f3acc1996fd75983329faeb30665bf1d660cca7e3acc1996ff74983329fee930665bf9d260cca7f3a4c1996fd74983329fae930665bf1d260cca7e3a4c1996ff5498332dfca930665bf55260ccb7e2a4c1996fe73983329fce730665bf1ce60ccb7fa9cc1996fe5398332dfaa730665bf14e60ccb7fa1cc1996fe4398332dfa8730665bf10e60ccb7fb94c1996fd72983329fae530665bfd4a60ccb7f294c1996fd5298332df8a530665bfd0a60ccb7f214c1996fd4298332df88530665bfcca60ccb7f194c1996fd3298332df86530665bfdc660ccb7f38cc1994fe7198332dfae3306653f5c660ccb7e38cc1996ff5198332dfca330665bf54660ccb7e28cc1996ff4198332dfc8330665bf50660ccb7e20cc1996ff3198332dfc6330665bf4c660ccb7e18cc1996ff2198332dfc4330665bf48660ccb7e10cc1996fe7098332df4e130665bfd4260ccb7f284c1996fd5098332df8a130665bfd0260ccb7f204c1996fd4098332df88130665bfcc260ccb7d984c1996fe3098332dfa6130665bf0c260ccb7c18
  | 31 => 0xca44a44a28ac4a04a2a59259452e52651459628e28e30e30cb29454a30d2ca2ca2cb28e44a598c532cb28d28d28a2ad28128a96496514b9499451658e28a2b629a38c38c2b4ab0d2ca2ca2cabcb28e3cab912acb9662d4cb2cab4a04a28d28d28a2a59259452e52651459628e28e30e30cb2ac54a30d2ad2922cb28a2cb2ca38f29044ab2c62c5d32cb28f28f28a2af28128a96496514b9499451658a38a38c38c2c4a50d2ca2ca2cab4a3af2aeb2cb9662f4cb2cad4a0259259452e52651459628e28e30e30b529434b28b28b2aec4f42d4e592c5b52cb2ad28096496514b949945164b629a38e28a38c38c2b4ab0d2ca2ca2cac2f3d0d52b2cb172cb28a48a0659659644e51642e59451658e38e38e38e38e38e249249228a28b9659658e38e249249228a28b9659658e38e200000028a28a2939659658e38e25965964ce4ce38ecce04e38e9649651651658a38a38c38c231434f38a48b38f38ec9660aa8aa8e3ab3802aa2a59259459459628e28e30e308cb0cb2a2aa2acaaa3ceaaa598b4e00cb0c32c32c38e9649651651658a38a38c38c232c32d38a48ab2b3acb0e62c58aa8aa8e3ab3802aa2a59259459459628e28e30e308c50d3aa2aa2aaaacaaaa8e3ab390aaa598b4e9649651651658a38a38c38c232c32d8e2ab33cb4cab0f3acb16b4f3b53a59259459459638a28b58a68e30e308c50d3e38aaccf2d32ce3ce3e38b4b2c5cf3b33a59259459459628e28e30e30acd2cccd54d3ce2922ce3ce3aa5b33ceace92b9299249651651658a38a38c38c2ab4b2b35534ea8aa8aa8f3ab964aaaa973ce4d04d0410cd00504109649651651658a38a38c38c231435140a48a40e40e598cce2aa2aa410ad000aa8a9649651651658a38a38c38c232c32ca8aa8ab2aa8e42a598aceb5000cb0c32c32c4109649651651658a38a38c38c232c32d40a48ab2ab1042cb2c38e62c5ce2aa2aa410ad000aa8a9649651651658a38a38c38c2314350a8aa8aaaab2aa8e42a598aced509649651651658a38a38c38c2314350ab344b4ca40e40eb16d4f42d42592594594592d8a68e38a28e30e308cb0cb32ad12d3290b2c3e38acb2c5cf42b4259259459459628e28e30e30aad2cacd54d42a2aa2e592a390aaa5ab3d0cd19249649339291651658a38a38c38c2b32b3535535140a48b96440e40f964ab2a973d038e4659659659659638e38e38e38e38e388e38e3904104659659638e388e38e3904104659659638e388000000e38e3e59659638e38965965965965d0410cd00504104d04a59259651459454652628e28e30e308d40c5504922d140a2903903b25993d02aa2ab400a9040aa8a9649659451651519498a38a38c38c2b2c30cb0d42c52aa8aa8ab2aa8e42aa9664f42c41032c30cb0cb500259259651459454652628e28e30e308cb0cb122d02ac
  | 32 => 0xa44d30eaae6305cd30aaab300a8c30aa8a9649651651658a38a33631c38e30c2aab314a8c32aacca922aaa8a2af32e44d34c38eaaaaaea9664d30aa8aa9452b5002aa92b9299249651651658a38a38e30c35631c2a9432b5638aaa8a2d4a9229039039662b35534c3ae3ae514bd400eba59259459459628e28e38c30d58c708c50cbd58e2c122922aabae38f52e40eaae598bcd54d3315004304304305149649651651658a38a38e30c35631c2c0c33033051556389350a2b249229150e3b04103aab98c1735534c2aa2aa514ad400aaa59259459459628e28e38c30d58c70aa50cad58e2aaa2aa2aeb8eb8eaaaaae598acd54d30c3140659659659659623628e38e28a38e38e25638e38e230c30c5145159659658e38e230c30c5145159659658e38e200000030c50c30d9659658e38e244a44a28ac4a04a2a59259459459628e28e30e30ca50d2ca2ca2e594a3912b059834a34a28ab4a04a2a59259459459638a28ad8a68e30e30cab0d2ca2ca2e594a3af2acbac598b4a04a28d28d28a2a59259459459628e28e30e30cab0d2ca2ca2e594a3912acb18b163ca3ca28abca04a2a59259459459628e28e30e30ca50d2cb28a2af2922e594a3af2aeb2cbae598b4a9649651651658a38a38c38c32ac34b8e328b28b964bb13d0b16b4b2b52a59259459459638a28b58a68e30e30ca50d2e38ca2ca2e592ec4f465934b2c5cb290c10c124b14804309649651651658a38a38c38c2314352c0a48a40e40e598c4a32c32c492b5200cb259259459459638a28ad8a68e30e308cb0cb2c2922ae3ae3acb9662d2ad48032c32c32c4929649651651658a38a38c38c232c32cb1248ab2c28a40e40eb2c62c5ca3ae3ae492bd200eba59259459459628e28e30e308c50d4ae2922ae3ae3aeb2cb9662f2b54a59259459459628e28e30e308c50d4922922aec4f42c5b52d2b52964965165164b629a38e28a38c38c232c32c48ab0ac2f3d18e2b2cb172d228a4e59659651659459638e38e38e38e38e388a28a2924924e59659638e388a28a2924924e59659638e388000000a28a2e59659638e3896596590c31480c12490c109649659451651539498a38a38c38c2352314c0a48b964c1040e45238ec1664b48cb2d480b1248cb0c9649659451651539498e28a2b629a38c38c2b2c30cb0d4ac52c2922e592eb8eb8eb2eb1664b4ac49232c30cb2d4809649659451651539498a38a38c38c232c32c48ab0b96440e40eb2c62c5cb48ebaf480b9248eb8e9649659451651539498a38a38c38c2c5230d48d49452eb8a2ae4922e592d4ae40ebae38ebacb2eb9664b4ad4809649659451651539498a38a38c38c2b0cb0cb638ac2922d3964bb144ed4b8e2b16b4b4cad520259259651459454e52638a28b58a68e30e30b43523158e248a48b4e592ec513ad2b4b2c5cb4
  | 33 => 0x8e251534c51438e38e38f9059659059658e38838e38838e38e25965163179659658e38e228a2e59659638e388a28a2904119659658e38e244e44f88a28a28b9659658e38e228a28a28b39041044f9059659059658e38838e38838e38e260c6186159659658e38e228a2e59659638e388a28a2904119659658e38e244e44f88a28a28b9659658e38e228a28a28b39041044f9059659059658e38838e38838e38e25965163179659658e38e34124659659638e389329328e2cb9659658e38e238e38f2e23ca38f9659658e38e32924924ca38e38e38f9059659059658e38838e38838e38e260c6186159659658e38e24914659659638e38932932ca38b9659658e38e238e38f2e23ca38f9659658e38e32924924ca38e38e38f9059659059658e38838e38838e38e26185183199659658e38e33923e59659638e38932932ca40b9659658e38e244e44f2cf8ca4104659659659638e38ca4924932ce4104113e41659641659638e20e38e20e38e389659458c5e59659638e38ce29238b9659658e38e24ca4cb28e40a3e59659638e38913913cb3e32904119659659658e38e32924924cb39041044f9059659059658e38838e38838e38e25965163179659658e38e228a28b9659658e38e228a28a38e38f9659658e38e238e38e28a2e228a2e59659659638e388a28a28a28e38e38e3e59041659641646642638e20e38e20e38e38983186185659659638e388a28a28a2e59659638e388a28a28e38e38e3e59659638e388e38e38a28b88a28b9659659658e38e228a28a28a38e38e38e2aa2aa514ad400aaa4ae4a649259459459628e28e30e30aa50caaa2aa2903903aa5983ae3ae514bd400eba59259459459628e28e30e308c50cb922922ae3ae3aabae598c54010c10c10c145259259459459628e28e30e308cc0c5122922903903aab98c162aa2aa514ad400aaa59259459459628e28e30e30aaa9452a30caaa2aa2ae3ae3aaaaabaa5982aa2aa30cacc00aaa4ae4a649259459459628e28e30e30ab30cae38aa2aa2cc39131662b30f30f30c32f30130c9649651651658a38a38c38c234c34d8e330a48b30ebccaae598bccc4c04c31131130c3259259459459628e28e30e30cc30d30cc4c5638cc2922cc39132ab98c1730aa8aa8c32b3002aa9649651651658a38a38c38c2acc32b8e2a8aa8b30ebccaaaaae598acc3143659659659659638a38e28e38e38e38e389451450c30c3659659638e389451450c30c3659659638e388000000c30c3659659638e388aaab300a8c30aa8a92b9299249651651658a38a33631c38e30c2acc32aa8aa8b31044d34c38ea9664d34c32f30130c30f30e9649651651658a38a33631c38e30c234c34cc4c4922cd30a2aabcd30eaaeb9664d34c30c44c44c3313009649651651658a38a33631c38e30c234c34c48b30
  | 34 => 0x838e38838e38e32942e59659638e389234d9659658e38e38cb34a61061860f9659658e38e254d3152924ca4939659658e38e251534c5152924924cb9059659059658e38838e38838e38e230c3659659638e388a28b9659658e38e22e228a5963964179659658e38e230c30c28a28a28b9659658e38e230c30c30c28a28a28b9059659059658e38838e38838e38e230c3659659638e388a28b9659658e38e22e228a61061860f9659658e38e230c30c28a28a28b9659658e38e230c30c30c28a28a28b9059659059658e38838e38838e38e328c2e59659638e38924939659658e38e234b8ca6183984199659658e38e230c30d2924ca30c3659659659638e388c30c30c34a4924932e41659641659638e20e38e20e38e38ca30b9659658e38e24924e59659638e388d2e329658e5905e59659638e388c30c34a49328c30d9659659658e38e230c30c30d2924924cb9059659059658e38838e38838e38e25134939659658e38e228a28b9659658e38e228a2e25963964179659658e38e254d31428a28a28a2e59659638e38e389454d31450a28a28a2e41659641659638e20e38e20e38e38d24944e59659638e388a28a2e59659638e388a28b8984186183e59659638e389534c50a28a28a28b9659658e38e38e251534c51428a28a28b9059659059658e38838e38838e38e250f3e59659638e389658a5925e59659638e389534c54c40d9659658e38e38cd34e44e44e4119659658e38e251534c51539041044f9059659059658e38838e38838e38e33943e59659638e38984986182e59659638e389534c51034d9659658e38e38cd34e44e44e4119659658e38e251534c51539041044f9059659059658e38838e38838e38e230c3659659638e389658a5925e59659638e388c30c30e38f9659658e38e236230c38e38e30d9659658e38e230c30c30c38e38e38f9059659059658e38838e38838e38e230c3659659638e38984986182e59659638e388c30c30e38f9659658e38e236230c38e38e30d9659658e38e230c30c30c38e38e38f9059659059658e38838e38838e38e230c3659659638e389860a6126659659638e388c30c3104119659658e38e230d88c44e44e30c3659659638e38e388c30c30c34e4104113e41659641659638e38820e25e21e20e38e388c30c30d9659658e38e25962964979659658e38e230c30c4104659659638e388c36231139138c30d9659658e38e38e230c30c30d39041044f9059659059658e38838e38838e38e25114119659658e38e25962964979659658e38e254d31438d30d9659658e38e23cd36238e38e38e3e59659638e38e389454d31450e38e38e3e41659641659638e20e38e20e38e388d4103144659659638e38984986182e59659638e389534c54c30e3659659638e388f34d88e38e38e38f9659658e38e3
  | 35 => 0x1010062c0ba00601101540180ab0018104052006012805000e01501c801002c0a100c005800001e000017805e009000011800200302a885800a0f7096823c18002a002032403a02805781b4012048012813c18c00000416f40e600200c80e006a02600080000c622c00503ac00209e0008044056000005800400001900100ac0020385d1000004003650a8000010881058800814e001038801c00c0000000004000001000000002600002900000c61a600100b406629f000801800c00104301a80bc008005017400600001180b800400300100d00140a900001a400402b00380b409c00300389ec02c000057807804605403b878401000501b03f0000001009004c00400d004802000600c00e9d6800c046000001c00000708e829c02400000715f400a00000d8018010046000003801402703a802006e002020802809e194053000004c13b011803400a00000100000dc001001009c6a00090038ac0000007003011c00200500000dc002107001000004804400582c0000003006003c05e1d1000009804000304d023802800a00b000806e000007000806a00200005ac00013e009809400002902600e005000100a8004132002002001c28002f045007800601900c0078010000002000007a06001800300080d1000000c286a5100f817808a003000829c01e0732b0808801e0020d0002000205b02280146a8039006810806005b000000000c03100d81800960720208030052069023806800000a02a005c06c01803280080120000008010000066067802400e0b102a83400a200007f016c01a0080038048004020003000405400000080a800000c00c803000a01403e002c0740011fb027008008e000008c03e022000000c17600000a005c046013337002400203303d006800200300b00000a000d00a808c05803c00e00d800001900e0dd403c00100280540080000000000096000251021800001200c0090006010000005012c2f5000005805800d00095640540190088034114000002802c016004076006825c00301b800004e032000007c00c00b0138100008000001801c04a04b12e00140d80de01d002c14a02600880040aa002008803419c00500e06c8030001000000401800200100000001930df00140080e90c0800003a2d600600081f401607c00142b001101200601e40060ba836c06a005001806c0060b100180540820380390128004006004801c0620ef01003c400a11304107240220d10030bcc1ae045000001008e00d004002404a00000180d8002000038000000400e002800c0040390290004252007003000401802a00e84980019059659059658e38838e38838e38e250b2e59659638e38cc48d9659658e38e38cb34a5963964179659658e38e254d3152924ca4939659658e38e251534c5152924924cb9059659059658e38
  | 36 => 0x480320050018fc800000101b011c00200400001bc22e00c02983840be0010040a1d02601708780700001e7005802c36901101b81c80020ab08c00640000710f0802009a05001e078c0020e600002c007e03300b846803811f0040f1c04e02f000012c2f804504f80d020405411f80700d209e099813423e00103b82e004422402f0000aa2039007004014a03800a80001e20102a380000001d707e80dc15006d01101d0076047053924cb3e00200b09b044603903e012cbc40b8258000c07805700a953002600200a80e80b6047003023016e003098806410600c007801850a00104181602b00100a6960800003206d006c008002003857401c2b500000000e605e02200f020200419c80e828a072103863006600003380d800000300102a41d4000016004c002f2401c010c09e0ec03d05d804c128223802412403100f81a409206301584240e0068004002400001b00000640060000350048642004001000002a0020c1002028c00313e04f820800200e01fc0b8dbe28c2e3008400303b805c1b202f000004410e03b0ad801009c18d00b805002a0001f7809c02a00006603e42c602800d000c00e0f6012009810000187384ec12c1bd006000411e0e20b002103620040032adc3aaedd0e8800c5d20f8032012409400071d81a402a1cb007802020202400002ac02a000076802404f1230dc86d01c40af627000c0a804b01e803c042028077004401628200880a810e01d62600a003401402a001c0000000059ec000809017d88500042bf02a00e4102000004119400200200081c01f018002d004401224200a80102ae034001000001403602b09dc0020f900408a8000008022817400e00500603c001605600503f0500003007812400200c00781641c42ec09b80f800801500d82a9d4e01f035000412e00307280ec052053002000800200200081e403a0195ea0981916018014004020200901201a0084005000802407a005003003833604926e1ad802401702080a007c09000b0610348002000801002403d704800804c00d0008090020006000001005802200000500000120a9a9fc576008018031c04600700007d8aa819701480a000e08603a02ac0e453101e8290012003002000400408706800000dc05000781900de0840d6007000001e003001c00403100b00005840020c400a000c00209b0000092031005035800021d000004033201301400804a2007007004c0460290578004cc001100100fc0000cf0080050010008013016800000004281b40781fe00201b000000f01580cc0e000900319a93f61ed00c801002623e20280400740000010048024000002800000212f038804001000014880a402402c00302a41e604c007802800c03c0608828004025012800003c09a000000400406f04981900820800cb000c0120100e7002c0400
  | 37 => 0x8a9b23752c846c8b4e59893c43af05cf162472f028c3814f440135da112447789631ca82f459a957605d4d754abce7f428c8135b3d5a93eb0f925dcc1625a6487d15d49311d647393b58d6d00f92a850750f402c4728283cca901ccbc058c17a344e4b742838d005df14d0126c8c42d6c4e719b8ffc3ad50062620d7e29ed358222847c4b795792180a1f3b0147850282e9415156339d466427b44cb21316112860e243fb561b17698331324b672d48a5e2dc053f30a8e411ce0e3d23357ae06241cd3e4c622108d4aa0e2122c3f947a91fb56df549481201495cd08cc9bd08545831d3423119e82033d789d50d8580a09e544d32591544ce801c33f0fbd52dc5563c1843c5238bec43b07c51d3d50152610b2508d3bd265d82a0ea1561601cf0e2f695924fc07292c54d8f21e8a7a61d5794071951938742c315208df34e958b39e0353607d7eb41b80751c000a44b2c2992770de333e13c516d0d6923c82d54d112985b70cf96334b552ec44ab5408d66296104c2cb161e03306d606f017c617c6ca014174404448871bc55de307185326d00d01d397ba020277051007802ca86002d3acb4c0210098b74004fb4524800000000100301e80e2478038a5080061a800c0aba49003c3d080100e00010968b8c00400108185bc00428304f1f8400c0e703680000080cf2cd03bc00433d06906bccd2162000005444a24397700b818a065000000c00000103001210aa0008cc02445ee1570a800980001fb000037552812f000869836418e0e18008c5606600500e040200301a0d140020943fc005c0f88c8042915008e2bf01e898411a0130d68054c66290000004431c001404838c03407103400043cc00530a881803a68d7a6bcec8140e500082e43b29d402f04300d009c00a8358c2417b02a003437415c080801c0040020043e7074c3ce0258b1001e00401e01b1af220e63f86940ae025000095422400204d89c40b002d01a0275cd801602aa0980b20421f6804cc1447c01001b812000700180ec0003c704dacd832000000080180ee22d11e01d4072930455804007e06806680342762ec0aa01d89ae96300f857800404f08c03b641ad6f03ccaf80000001b7003c13297106b311c4cc00600d93cc188004026b9340042630ef80bc03401d000002c02800224b82488ba0000160084a180040748cb800007655608f9d6a01200911001acd8c02c00d05ba01901d008c04000037b000c06c0000062d100040000b002440141b80e2006000000c00180981e2008002802c00a0a000003700601b84ec050801600128a039d50a03a19188acb7807800500900662cb011801c0e80000e780040cc3f103205fc1741fe08a868c06e0c205b83701626e2043009c0b019800082e83521c300009502c201708ea31c2fe0000020da8e4200a00c0e44b7200103e8
  | 38 => 0x423440855eb47ca53503af361d4b2434c59512b4f3d5f787374fd4a2345b08905e0904a48195b440405df15353511360944077122224c179104b92683fcd05a046c482169c0dc5ee0c6627041693c012175bb491c00ccb7314990b310304a837442f16040e2b0ca16821ab433818d91cf2ae0a2e59206070f0422247586df636d23209a0c41187c1f831bcefa26c58f103c0ebb4380cfe42fd46b20509c30cc501c1f354c1399811e507d74727c536e63c4d281af82c83b540bb50b1690157d2ac14648c71a2ca1b46d58f12d8ca15154d23c45314cf2f98f67577514d4ebd3042a94e9d1d21081462536633286b54c34d64585c0c61b1d065543154e333103a555d32838d4bb902255e23a40b592d097da48b83032fad8b4185c2aa593027844a41a2336848f3c80117111816d2658bdb0708c4f5cd476860a4fee5f1d18e19356f816e97834c497c4489491310b81a44f204bd284d0a221f8b5e02ac15623d900c6148779272d8f10af56c60434e7e4814fae6068eb1604c96d5c64d83325c1991b44de8573c6414898b4b2738932251cea439404cf2bf48f10da04c45bd965558c833453e0d5725f500d5b5d84c144508417f023d3d591725c380c561ac9cf21b80aa2b805e701b1558571973b544831c051d035546d02537dd49f0d3558e600c7c95dc821753f865408e18680400c9e28480800c1c9995c052891220eb71b8c8e502cd5a71810e072db135d5e1cbd2278557b51f57db4e8d2d11b9d81d5e3d32d3af859210b46902b3d4215674c4530440c20100141512c5b0334d4604df122747c096c3aace2a48fc80317e988719a588c2c782b54914563356d192498418845ccf4009551361ec8fd1394427e0788fef08209fa21c8f3711758ed02f81b23d30c8f0e6442122b0b37232413d4cac6c0173000a1374b3d067103041a419363c44d1373569c121ce710a884794e149c63df03ae5e288bf21cc34e294cbbb3b6c18b5d74c2f622095132cc6880ec472b350815f1c487f540898f13e00b022f7517f23986f243743c34ad104562ac5353e111475610d803c04dde14298f12e84cfb01e4ecc5fd072e532c1f643d8d1b3f907fb42410732e418553a5011330b83f42e3d03f0738e6e063d041250894c0a7474617b8475498d1c2052c7f159948c60e40b011b247811aed48105c83ea168d6ac16fd4321a8006f54f02bc49fcf1735050c90fec3823a1463e47447ef29186f5281043f450443a40ec5cd059c5d42acc08a1fc170d5eac61a5ff946e29688cf04ecbb532316d54f8470d0cc09f00eb14bf14d92484be883618b95d95df539a1a3c3f14bdc89958b50bd212c8e92721796098c7a40c60e8b17618ec11d81103ab087848ec234195d60837209014b9c5f81910ce03d4caad4558d6816856e7493c5723ea931a0a7087f3bf49e0254
  | 39 => 0x8c4675014c7a579d1d96371275277518d215138e5f3c1b130fd5c43bb4b0c2ae849842b1510368839a02506ed14d044b5f444cd3014e8225dc3275948c3d295128525ed6d432f186719e45121a490ba398d6db423483e4adc5b13eacb133698ccf0ad15f53c7062f34b97b957f0c0c3c517a95ae4dc30c05822316457b45d154d6008fbf49989af07f805e4e30cdc56c983f04717c01fc84e6567d31917c97d61808d700b046970d00e531244d2441914ea11712e33bcd6ff0ffd0e729c143d30953684a75000220553311c18e945c408443e173c574561510c87f3457146d0e2481607c58a51fa976214080cd07c821a15bd52806fc0985770cc1024007b4c1c9853e883b33d455ae0f50f323574e562790341127984a07a533063c41d334c82c530086a418a118c52accce03dc5090494def5f1453c44ed53a2b18d7636a8e875e6884453dd8e11a549c934dc0222250b9155214d915a96c11b857393920ad145110d805906451be82ce570875854395f80f115904a4823b0bf064f0e5159a397580f52b42df2e1cd711e10e025c6189042a0ce23748aed622d5ab0aa585749e15a05f85272560ca9a04bc2f34b5971a5cac2b64c45181357896f25b91a259286cc2f21862037887100603fd11d0e1323010a661ecd5239808a95a748973b68f855d9c5501dc426d0cd44e928c45972f6485f32c8a146120d740da48401df098f60b0d795db47a608f1544437cba540914805d2404a022181b63b952b285800b45246cd3dc874e093c1bd3074e3b0a347a02e4d75406088172728dd43bf058631a0e3631353f311fd7093a0106639ac32d48e827735bd2dc4e9524d2a142601f2d4530e90dd6529507e11a96f2100cb0840f515e34653a13e8577b06b0ca146947cc1a090445e017fa0cf894160d864858dc40e3c9c6b804189a446c573722f95b935446775a957a41e500e4445c92c02049f6443139b4ee4a6660112cd228804c3b14b25478ccb10fe025c1c50d1c07e89373cb900b54ecc8d11340661c68b1d34ad2ff2d0071635c8af93d1c31a61c095d1d250fc6324a8107acc1860e451807615800ced50701591d711bcf4650b977017cc82337247e404689cd54154fd5fd807d50c041728688741f80eb020fc1512428f632dbd607171d24415517e813889ad3b4011f0959337182cd331f78b7542f17e625e053a1ed98a72ad572209e812728152d75b844222aa49ba2cb459e18f131d4860cae4ba540f0ee0351147d74248b458544b031e404d1974bd1166353527a5d144ae3f3c04d14b8ee923043955e780fe4c2823743d4c4805249e94cd01e63b6439d198c1d44074c6c2bec8fe4daca4b056cea219f06ae46f92d2097439b40d12570b1c99d0ed0e0c277ccf50f0952e2d997d01b114b810a4bb7341d4444d1902950e54683a64d7c1e1526
  | 40 => 0x5a4fa4d903520f8a0d2865e23916ba12b0dc13ef96f1186d1555c3123012a908c1e84603169534c5ed40c304a954a5550bd33e7cf5c2cf84b64f955fe341569a4ec8e5f3a858453978850058508e0c313615a04fd733a49fe07907154fec98d1d087c23c54bc552447d9134c5e534f96f902dc674542d6a126384731104d841d440eb0830a2b28309844b08b104028dc4578c1e03b5ce161b5d8440184dcb4e2852806192a43900c0f549c0341a88cd127d49764b8014205e13313a357071dc8a5f3b214e44f680cf2dac3be4384b883ee57d25f214af3c9835b331889f47c4f9a20b462d230cbba4714dfb02b90700a0c34718c07911ee0c1e0a54a104ffd24c1258ff6214c0870e4c70a4cf15db3b504155dfd88402a11062ac85b707282c030510fb1bad7b020bd26a24b987910a027400b4d9e0464ceb5f8cd3c4e60ccb448d88142ad283167498b38b57763c88da137690602a39562622949a468033661b114f2274f1d5f5c64c2b417a0625461120694642cc905b62e46422d886ab2fd153d13787fa50251bd103d76b034454231394822ed0b291064659135c8e3204052a4c9c2945230c8b3ddd753623c52c2890d785cd14a951217c1229430d156ca3f4fb0b1723281da09247094ba8a6824516c2152c0075bf8df411e879a0c4918b61856e241fc51b37801ec316cb0362482d93118d101f855ec4f30b112b1137f09a82691df4cc25d793a70c38b213d404545e7093f03b82475474bae30f93380e88b9735f52f338602812c887e345a978c5e050f757c8a9f4f7108927a875213ed34754254a854f9711595ce45413c7c86050d7a58e973254a97ef27ac28723dc7363af42615c6cc3636dc5c256c06b34f80cfa15450a0216864a1c19384095d2343eed07a34346141fd139544208392e9d3160801068254020600c17d41b2cc2c52d885728e060103c412c467c485504cf6009217e01294c370d0cda53d253083950d8d3bd826408606dd1630a17151578e2bc5472005091205ace033374c2135ed5cb5ba4a211eb55df343c66c3cf02ea492481b2e146a847b0f5a2a017b63e0c10260c89ee3e740e60360438390d3e61160f5d048c51000046721738d9621855942f3c0ac5da97b259684b43ab57955bcc18e19bd0cc408c0e927dc54961e125d007463b1700c8809315033f383b65a54cbe1211689530cdf843910a14f3c06a60dd61a2fc8ca0539d60653384ea4becb2a0ed45054ddcfb32d3c0ed22809b20e8d5665cb12374b30e884da547662b502d49d01840a596e43cecf61356897152d029b1df983d5b4d48f38512c12ca01220388d31237806d36a11d05224e9c3d205b84d64a4909b823a4fb80835da44522210c6115756802410bd750a426b61f8c44606121e32ac286211cf860fc90e907597f55c088910edcd2601649a72a
  | 41 => 0x8992d837b0461482cc125d707623810a720c598e345392e21a454025afcb7b15a03482f24a960b3d05717209534a809ab17d4ab730212d05a6d3a8027d8d814213792f54dfc090c13e5cc519157f58743ed8f0f4f7d75959ed06c61a81484b9890b358cdbe109d6465ce17a54a346ec18fd3db1e18a910d6019b22843f557fd4513cd8a5641f0a486195523077d2554a117771608bdc036525f15dcf2b3ff819f209436552e8fd93190a41208493e191d6e6186088e3f047201a1488954c0cfd4351341528433d2e8905127c83cc14ac92d4208e2300158852779343138c0ba13c47832e8d24e00ace9257ac7f726f088801f0838207ca6b56fcc5809c949c3e4010e2c1558c494020a54dc2700cad77544449a85f648352f883ec0c6d8273e716b54fe15a146b4b8b575c3a112045cb4d34e7029845c35dd01f504c1658116c27c5bac1c8588d72e1340fc5632812d0648ae707d15aa296ce2e1144bcc5b9444f1250a793bc86244f5966b396556d465189a4ca43ee2618f4d2c80d1529f0398608cb964cf8ae922c185d08386da5310ee01ad92da5574d61174d4e14b3845a378939262642a6430870750bcb0957493ca61b44501a7575f0e714143ce421016346732a24d50351942659b03a9094166854bd399383cb6444c16a609cd19b2218fdc17456ee4c513ba2fecdcc1068e6429d06380a905620bf57ba3a2457c0934e721c9897941852b554511872214f2917a131007450f031e45db01240b93a552f91b4ce11481023937018e203d4d0e103407f16d9666490c8ae50913b113d159344f4df313e018a105848b41496633b197660324b540b882d2141d71d55807c119d4e9e3b243e8372846c32b0e6f1b08da4524d1db05f8b433f58c6730d442a44655b5280cb896138bd600a8ed35ef8c7039a009c639c2da58a02711f0c5664c9814406d58a62a9133524083491e1c3df12fd0153000e3153c09ec228c9100010e2059818015ffd1fc24bcb68257c94602c80a515001581c603255334a3a13394560cb85b30ff951e52c449f0c213532cb93be4dd83da5394284076491145d85904c54d97092d81716010cb36f0f7043883a7230923949607f611c589663a89c23be53170711114002479955c957a070d5be4120e5b53556c90b783334d549fd0c5d7c318e91372ec04a15ff0000195943f3ec017d4a5d0492e7ce473f8c54e17257a82b1d4585cf8364455d3c9299c63131517034bf015c37857ea5d28928260c37b1bfd3912098e214670a8d1dbc7983124ded252884d2d70fa541b43bf06b974349b0fa607789a0506d7aa04dd1c901d85fe57ed54124745152d451ff2af58302820d4c4c0c7b541dd6054bbd8c542c4db95a2d10332890a423a0e3f28a88dc0b44c833348c5628e519d3bc51a71e481ba10b128b1f748f91940468357d3
  | 42 => 0xc7e13fcd275508f5448812e15bd422f060515d0fc10ef47485440d5c711192c86353015c9460853b55250593b7842522a0b8c42f957f08713c2107843e16f57294decc32340cebf42e569e19d890d1d54de60a78f311a69199505c92257213f222d077a5d5c9900c01396553004153287dc61c8ff2393938962f184701905bb4fe876b432049a34b099e10c43b261718d2427d0362da97ed21ed11b4ee08ff5b40d6562015150b9d11e318d88240e01ad2a6176400e8ce562783972e687ae34454a321284561e252fd18d499f257867b3ca953f58d94bc4df97d32190abf0ca90af457c03c2b715f62e040df10d98d151148f8075c311162801a129851e51f975a3dcce973ae11dc2648d2f4100eee501084928943cb10d0fe138a149d2580be44cd89cc2d0562a580127d458822a25145ae53594fa20dd897410c67d257036c59dc0fd0d191283fed37114301fb249535b19a86460650412607016f308116519482e04e755240de01242c701743f190d24640a0d00853bb21d95b855cd3d52988bed5130b1442ed83e3ff4c773e814b561a55a8613c6683f548045d6d3d704e0b3349dd7a763a151a5738bf60b188025ef58865db92a501b98203dd145e149c9b761407bd1e2979d1c64cd81e885de011964d5f242c20880a9d28643773d6567161f173f63bc5a80da882b2c982fb468c9272af94d3086c83042c11b05b297e7393503c1044fec20b863315c50c1264485d22e15f002185552ecc7b950c516b202117e4c2c85848203321d9478c5658d953f0ccf64c048bc15801341cf42d709389aa14e51fa266c6bf54615ca5c2ccaf3b8cb0e4bb93ad41c55165e40fd83828f422a1cb4d24651583a80add423c00d52f9357342d72d05404fd4050a90588404857cc5aa185967e44098a446208e113b8acb183d03245c13184d7c52961503220c9091b2c901b447046b93dc49093e6d179463c7e930a560e4ccc74a019cf02054934b0170c151358f0353bd35600646092d3091f120d8b11d8d16e2c61093617808e60658af5d1897055ad4f146accc5552d1e51e401a114705f42fb876a0b842b21218c19565418c43710f1513cada54b4a091d857892cd4a630e7d0eb29a8d9b347c2f52bf84045c483155d41477514164e5bc07693de520c2b0c0d649680c72900bde066150f1d516313b3d8d53fa122461450d54be0fde3f317061621841337c5e0184cff71ac55c31dd589113550b612a574f4d415e1053d6cb3f6c7f925e90460db54dd3ec92f0471c9230f197415d54f7e41d511c34191bc27d1585620c2eb5cc17dd16a54c9422caf422e492617dd68d6225372431c5d547e540e49c0c16392d8a230a18065e8916f54e584904d96d60f616b225d49c51edd33d60b56985ed0b042c3d80d15e4ca536d41be17e4c4c247811d57903722ce92db3
  | 43 => 0x5f5429158296bc45e85ec18200f631f414d346822847381070a7c6a54eb08bb07b500104543e95c84c740dd8c0625954f531fccbd3d2d04e30917cb3224cf23c3155c34d894d529953138b055247853f411b8af805689343a58c42472cba0362400322c94a0460d68641ec880017461931b419d02651bb62a11af48710ad39d88d04e510d636fca0006e083c3bfceb92590795500533f2d2151f1e58a5d37e85934f4d22b1c5cb2b4bb44594f004dc4e0d4d7475476656ed019015c0c1442d1483e203851d6930c2b04d1651c43cf3e78cb92f8c7e7470c6c80f1c2b8335818d1add0022064d731c2cf97317c681356178d351d0d017842b161591cc5a0d21500386e53e3401611a542d541815e499c25a009c7c735708d42bcc42460d413f12d423552187f85d214f44de0b7f4d28c0432655ef13ac0db1cb0d1313a102a088caea16607572d189e21d749821cb539f49f14c83d292e819680bc4ecc8924d782d438e108a63c12d347ad17c3ed546508157f862c802e0b2d7c610d585918f492b15b4e000be96e300f564215648560c84f1b2ef963e22797af58883751469588114c855240139e0b4d6d213317143cf84a336d98de3d88ac941f4e5820ec8b35c203130c0953520786e44edd7bf255c4402768fa745a0f3f5070c223004de7256974b48e0cf131400f21af45d74414d433fd46a3252017319394db3e313cd3260d122fcd68e2cf00e043680355de0d4f51254f9282d05e19fc68e58b07b00f14266290c25b3fe10c624e9100420d5e51e6d14a3ee132f24812075f7d604482556c17bc02813e91601eecf2845008fd15d8cd904513d83ec56c70f90cad59bc4c137c513e4eb93d44d503cd38f913a02300ec46e04da008c36f33009f9016cf7f55d49fc276cc84003cae357c478b30e0c7b3648bbc3431678077471f1dfc1a751b0f98039544233dc6e200087532de54875eb11ee1870ed8516c8cc56b13252b7895b0ec0ac210dc2ee44481ea4bacc946160171627d3a40b4167f20388b63c204934ed0f9912cca224a080f43c1c6b41c0874503390113f500b65c3d26e631868a0b59352287897c0bc186e1281017293d8bb534859611958e438250d12f454bb36b0c9c5d6134521c0a593cd4ee442e11770e58ff41814b3b34a46151438d4e554caab0b24191236c213189835e12485300f6583c03ed0f24098faf0bb50ea28186f72fc079e21dcae524856b018351011c395d64b54efb23b929a1801037040d74e3db94e8220cb8439f123e17415c1548928f194ccb721d497353d8a2c43940a653c80911dd02bf5344c8704a16c05a88bd01a1d8250dc06ac2090f242208410203572a403c8a60810371043c37f0020fe04618a9e12bc89b0e3001717ec7fc2c283674d20d4520a06e8208870326293813c7cdf95a5c18038e8f4e2fe4
  | 44 => 0x48450bdd3e747bcf6449cd7b3484027b0a4d6be587c3593b2c32615e132213d4eea12308d95d48db424cd3802e6cc51465562e083cd6b40616ef2c58a6d34e00395f38e6521096390890c921f5132414f4bf801a05af04144f033b4a3448c40b009b138806ccee753a5309238885c2270c75531c3ce0ab0d59159d0850acc0b40a00ed25378fd01638e7345150e62a802975a28c8027cd2c53f694da580d65328710d9243189b44b589c01a50c05a507bc03691b70965675484c4c662a8cff5bf52164acd7253cc0c401bb92f230ad20f5c711425e1063753fccdb0be46f82f7d31c42556fc47cc2d81d70df5411c28553f0b9d34ed36a41712f52f191b429f44724d8088f4de856e28bcc3908fca6420d14b00f78b4a1668012327d1ed08ac4012f1d71f051534f38a5271639407234f54274e989d73c113ef3268936480d8a339496852dc957756d86dc0aa0a512d6073437656ad29b96731235571316959b4dc054f47f463946018311a2454c0d0874c4ea4c3b16d5109189c7d83db58155e18f9428a447732391e01c855681ce807402fd78530381e83ee8d4a35b03d73de03a548a457f4e4108851e87d73ae81a835244a4637d7164a407e53180d39141006320c40d250950031cd5521631145537147ec4f1d0803d6c0b8155d3e857a15d51394b305c5c1fc0ca4ce12fdd656550c48a57dc5743fa4fdd4ad96a04db575624d55e054d0ab6517469e0c4109250e8e9a2bc0d6e3680b5647a938d41d16c83ed12c92b3497236048f348bd11303fd2b938714ee5adcaa628ec1cb433c5652e398432fa41900b903d519604574b0c41b243967c3b94ac513ccbcb300c2dd04c81c906a94672db4aa25c9d1f65af4660602c0f829e0c9b03206c522f58be53080360658e3936e065c60d150a006c5200fe51d325598dd0ba056c3068cc711aca832dd91d45de959e06e57f32e0963b4ab9877219d1850e991101e9c41843fc1b761f4be04af0809026c61220a8a022ce0b951ded1a926013f70a4176305a8788589d793178d20a1c70fff510585b591d1a405551981c3035d3a30bd83740c9537a98c732e106349950ee16105d92a490a71eacd4061c43c029711aa1b98e42538d4c53df5613430d76f35809b50df4c4b03a96bb33c13bc07dc94f068ce1f34b44d43a113eb5a4c7764ac00af4720aa8596d4462420ece5ccc86b42a82ec14049c044816d956347fe219480f0f858ce256530620e929901543f34e5d12b518d55f52b0ce34788d302bc86982b5d4df62dc62307051d822691cd31a488b260431d305c19a0e2936c1d1c5473edcba84c004f626b119315f4a841c04f552a30ca7600140631ad5d3117ce912e00e1a089d42a32d83fc3ad89052d94e7a50441d25d8151c4014cbb2c192ad5400629492851736c95d012f84b02898c075aa98d3
  | 45 => 0xb19957b15031565389c33747c96dd2418c093a9cfd204e53b011394bd2798ef8639825f62d8c431cf8a7646cd24136bc6fe2bdc08d179965d5398386292878e5eed24658807d215cd0e330288da2a640a73450c135864ab41bccf182ffcb44590d70a0bc932e324545a4a3088c17d8ad53e3d651436d3051f44ee129ccbca611928a055cc1b4a58f5f13dcf6861d86f018ad60934fd73613bcdae36183231cc086a37f4df612dc69658e15a429498c31eb0a8f5de51152b6c2bb376c8685ab89242e34f69410948524ec64301e0c0b1f7ca750c7ca1145b42ef38d0ec21d2c86913f88d72ac11c018292f632913fc2de8be116449b8142c2465a2160d3a9948d0b346d92a28f0951a4afc0e3cdb30fdd55a0928e9b2da4a474a04a6923150b55a9127e29bc0d03f2c66d071cbaa3bd0d0951d0d9f2bd8a8b562525259f416062b161c118824408855ea5330f3a469923310cca655db117819848aa4328fdf32a05382ec91ac352ca934a18bef3cb48af425c829560560c54b08a70a808d3259d840450d7714d8c0251bd929f0a2d79953ed30249a57405b0cd6a44854e00090e33032972f0420ddd5ae032c515d76548515401ddd42210e4ddf268406b3098acc4a007a802813201a0ccb4304109d456418360bc92a39d01350878ea558f5704101cd1d0c502113c44a94596409362840c41cc51da415566931b81e354d82ca501c61d0f4d0794268f6560146e92074c475b348ad44cd7f93b3496a43158730b6ca712aecd9d366509e549918a426c2450a8cb7d0518b1f2e641e12ac414c30b43e52a08a35105149000bca4423d4499217819e26ec7434af55fa365065d0a94b0754a56a84eac6e03d5ca375e6c9a3140cbbd36f49b3238030f337967a0a691dd007925b4f78cb031c908713c91a148455da1c9d050170460c1a353ce201d56435587230d54c78044915119c0a3d61e8fc23ce0ad62d80f82566036638bcf9525f861e3e58e01635871b1a6c97f40b9667232c1a504252b84fc4dd823e96842f3813323d13400ee827d46686de47102a14c3805a13801761450d0162a4a571ccd2bb03a02b95b801c51664de90ea8be81c74e3208b895518b0ad95558b8a3e2d8e059b54354f1884329f8e3c013ca4d0b7147f0dccfca18a85701abcc5e5acc8414efd3dd08594ed1ba89e859c80533888251315d1342c2caeb43cd01b0d510042cd166e0d114284a853e41a3094931480f359843502744f6a3f24e863b705811a9c93d62b92a205dcc340a298da556d12a417d8b84dbc14e513899a099ccc42b90a361c955825fc4c302a2102f50612a909bd0ce02f476c1ea8f3461814e249ac01f6260ba96300ec329144f93840bc3246915a55a98423bb06fd3e2525c2500a2739ed5bd5a8d2d94f647400fd92951128ca32ab87ee46e81bb14c43d2195
  | 46 => 0x888c8243cb1908c0ad450dd5b105942760f400e723f12560018e77335437c12f12c70258e7934a98b530c409d3f20e492710095022d55944383b9393135c1d593ea17f53b65d303d13eb504d0e797cc5970fa84b3c2af2c4849d178816e34092125248aef5f94c4a5ad156e2e98db05b386940ae926f59784445258e8111e06324b7c8d5449d40324e4447023cf870e1086d25a43634ca8ab908b148b526405f26614b3177055c3bdc10a1d054544fd826242dc3e31894cef42455a30c2d6442d7cc760af806000c521a364510d51896911528a3e29093934790aa73a8c6d82eb05a4458ca4e44615a50e80b310dd0dce4c8cbe519449380460212348533b2dc47d051ecd9358d16a711f92590f5920229551613b7c77049795bc5f88b8301f958a32fd07204815504f0d43c20c86f4542143312014a23fad0310f99650276579f44c814a43b4d675b304b21019473050079c2aa93d004847c61d1141001943c929b0a4c40f896660ac79f4c6d41619f859f3c407733d0d86460e0fc00bf92bf43f557d564491731f0242020889800fc5d235dc83d0d318cf151806211b40fc034c40517114a70d812a736706cf0c804c7407cda30fb41cf31746bc0cf180c55440dd00b023e0108f751840d23149548439a524b480476d6044f23035113f3c4c2b0145803731c41ee4a798cc166d10f26883ad2d1d2ca2efc8d651d50944d24f1e4a1ca95218916901c002036c5624551d2940db86ba39856f413644084e089b05c8c1ef34954430e2c6c348657280aad21f3ccc1a93b106fc261c03222c447d0b1052d2a5c2a7488cce8118c1d529806403f347a32b98aee4f2c6620b3058b1de0f524dd18b03de88ce56b55553bd4c933c3582626709a946e443b3dec8ab5148345487548a12e84ed0bfd5995e5c9893fc47c028b4dab21212aa21f081c5a494360730e6a3b99447202d020119055e5ba07be2eac7c41aa480a32a911a148963c1b6d7ec10f49f83cbc44c2b601164540cd42fe97dc4fe47da22d589d17c09a6024833936ece8f06ad4eb5fc944a0a2568c4e8886639298b310c007a537038e43a0edd366815411251522a7055a0c1816c58bc35f117943458093c1158468444e02b707e478f14348934174ddc16e4f454c3d8bf3ef07ba2be924246b8ace2d247d3253825e1e4d57838217a6623849c1bbc79d5fec78d061c6801c2099559d90fe2e186934a6d22a3a4c44545ed5974b1161826f968f035566458405b208752be141819737b8b2f49d90ae41ac83360e8deb3dac76e3c845a0112040b44f0bfe16f87db393d5b33f987bf2bd4aff506410c5700d850f6c70f4498d1e5434d444cc833a1c4c36b317187f3b4488d2b4871e1e5d23d05991fe041085946a164f4b515f953b11df4a200a959c0f6c58484ca32d4ca663212ba5080fe2545c4b
  | 47 => 0x7c1ebcc6a1561494341067144b8d2026945c542941702e9073f4728c2359d0f441698c331484e7d03bc35251703e24b94489038d3aa258432f2258d2207401db125ce6c52e57262d14f2c459d8bd314cb7716f0baf42d120e1c10a3c28c0e444d38f915c14851479952023ec0a143105644d90d1846780a247ec75b081cdf05894b7e385512f07fd04b5254bfc4aad65f0a3828f386d640013841d5fc06fb0e0ceb442591e7525cc8a51bc98c16b138f12e48010c250624d0929311547101ffd8d00c282651070bd401616d1387802901dd5e938c15322460f813630d0a3fa869905ed2a64c4d00e47a543b3f1c0e11288be709485d65aa547c035c2ad1fad2dd5abd14b2cd8fa4427009756190985fdd5e659504c0635d6c433cc4263818dd72b7ccee0f20fa9465936710292b127bc2262e78043150457e541169627593651b4042f52905eb0bd825462e8cc83588420520c4900e4890337c959c5e840541f595b741e0993330c9b93b040ad245562b494d86f4ff94c6320466b179058f245897440e52ec2fa8bf1172960b00987b12c00b940054cf455d15a616886f95e48d1725a024041592511ecc15305e920d2000fa314bd01201441b62360abc57d183b56bc5332760780339d513571d6013d0412b5e6095457309b606145dd62517ee2c355ba1d90aa10ab880c396955e2054da94800a2058d4eeb56898084264dcf15e93fd23bca3344953391b1882c5ff4d8a01c562608096146084129526d2215548195319549e36203fa144c7603ba0495522024134210531cf0ea915acf585d84b6153cd17555198c20f709431a701e51e0813107f42e5409cff04ed545f1d7941e13205241c88b5a55f83ab5df88b71aa8e574c7ca8645900b5216d028362cb98082d40b0404724211921b55c01a010013e2383560f3a0cc625001863137c9ae32149291a98ec71b4838d23b04a72b28ce61d40bf503003044df4d550c6528e6134eaf3a3853e1b3840963acf76056563f57b87cf374ca1d510016837f92e408508d2252d38760582980268537371906f0de4f1960396165b78e5525ad0fa161c69f0de8bb8183813c5cf52a34dd4ac01f3943813b170044c403b5b60b920d6946a13903e007c03bd10092916024fe738651161998da7320875f206041f08c8ccd4e18a320df92283b29021398910444741f334d49bf2abd1bf2588f6633b124050ad64b2c8d0766090eef5c8086c1308fc443343560cfcc1f59044c3110863436b54151f98ac82f34ce40498dd5451876713f0e05265188d17b50860960ee2110c48e0a30d7f2db906a35514ae48d41af5ba9153632c606256100842a4a50279d538069932149e48ba4bf927b40b0532148cefe3ab91846168e2555a493c3e38e46209c8114e815870e009ff15a510a136c04b16503dd47d0b504b1940d1f
  | 48 => 0xfbc3053154ae85198b1a5e2d2c02d4d41258746d4354c9d01a198122bb017f29fc13a33250de0be0b5711ec15d011454344d53ed1ac9470079c5002ce49e562804665b147b41ff400c6198c902f09461011169f5914ae12f108f020152365d44fd3327568709d57ca03e822d042c6a1239ce6d0b997d83838f1257b434f45f56b13c68ea847e16ec3bc06d506c0282385d0583c94bad57617102d756f708248060e1c7054dcc8794f8d8d405e582e447c82023a8b7c3218e67274c9073acceaa0f291b65be89d22ab167955145c612e16da553c50f2c9c84f3a6138b08d8b9c1ac089517a956f4f491c64cb0a075f095115714cea49815d46364e5c0278bfd43e49fb401ca0127518932ed8d340a4827f086572418808a43dbd39c050c6215c797b714741c05ef112208345ff199c65b167084e271d8c140ac73b38494d8104c6781fa0e9f3c2d41a40cc16312c56fb16b4c7321480cb30f0a2823ac4c54c791e80804a771cc80105924c0d2f04e8a5fa44e10d2cc2760780112b4cf05278d06737fd6b647d44d24988dc717a4f4f17c486f3794362441d7cd0eec0f92c6c2294bc47d5094ccd04058de44a70d9810acffa502115b335d0d73709633382d45950f984b32e803816ac2254950649406973a5e2158f011c28851e5629118035c5c4d2b20e452475f90b781e94eb230e83eb47dc8ed5c546c10f9cb3f5d343bc197d8283c58e372828ae23638d823fe5009087c2e340796ab4d8926d36e95673c295
  | _ => 0

def mainK8 : Nat → Nat
  | 0 => 0x8310ff48310ff08310ffd9610bfd9610ff99610bf99610ff59610bf59610ff19610bf19610ffd9210bfd9210ff99210bf99210ff59210bf59210ff19210bf19210ffd5210ff95210ff55210ff15210ffd8e10bfd8e10ff98e10bf98e10ff58e10bf58e10ff18e10bf18e10ffd4e10ff94e10ff54e10ff14e10ffd0e10ff90e10ff50e10ff10e10ffd8a10bfd8a10ff98a10bf98a10ff58a10bf58a10ff18a10bf18a10ffd4a10ff94a10ff54a10ff14a10ffd0a10ff90a10ff50a10ff10a10ffcca10ff8ca10ff4ca10ff0ca10bf58610ffd4610ff94610ff54610ff14610ffd0610ff90610ff50610ff10610ffcc610ff8c610ff4c610ff0c610ffc8610ff88610ff48610ff08610bf98210ffd4210ff94210ff54210ff14210ffd0210ff90210ff50210ff10210ffcc210ff8c210ff4c210ff0c210ffc8210ff88210ff48210ff08210ffc4210fec4210fdc4210ffd9510dfd9510bfd95109fd9510ff99510bf99510ff59510bf59510ff19510df19510bf195109f19510ffd9110bfd9110ff99110bf99110ff59110bf59110ff19110bf19110ffd5110ff95110ff55110ff15110ffd8d10bfd8d10ff98d10bf98d10ff58d10bf58d10ff18d10bf18d10ffd4d10ff94d10ff54d10ff14d10ffd0d10ff90d10ff50d10ff10d10ffd8910bfd8910ff98910bf98910ff58910bf58910ff18910bf18910ffd4910ff94910ff54910ff14910ffd0910ff90910ff50910ff10910ffcc910ff8c910ff4c910ff0c910ffd4510ff94510ff54510ff14510ffd0510ff90510ff50510ff10510ffcc510ff8c510ff4c510ff0c510ffc8510ff88510ff48510ff08510ffd4110ff94110ff54110ff14110ffd0110ff90110ff50110ff10110ffcc110ff8c110ff4c110ff0c110ffc8110ff88110ff48110ff08110ffc4110fec4110ff84110fd84110ffd9410bfd9410ff99410bf99410ff59410bf59410ff19410bf19410ffd9010bfd9010ff99010ef99010bf99010af99010ff59010ef59010bf59010af59010ff19010bf19010ffd5010ff95010ff55010ff15010ffd8c10bfd8c10ff98c10bf98c10ff58c10bf58c10ff18c10bf18c10ffd4c10ff94c10ff54c10ff14c10ffd0c10ff90c10ff50c10ff10c10ffd8810bfd8810ff98810bf98810ff58810bf58810ff18810bf18810ffd4810ff94810ff54810ff14810ffd0810ff90810ff50810ff10810ffcc810ff8c810ff4c810ff0c810bf98410ffd4410ff94410ff54410ff14410ffd0410ff90410ff50410ff10410ffcc410ff8c410ff4c410ff0c410ffc8410ff88410ff48410ff08410bf98010ffd4010ff94010ff54010ff14010ffd0010ff90010ff50010ff10010ffcc010ff8c010ff4c010ff0c010ffc8010ff88010ff48010ff08010ffc4010fdc4010ff84010fe84010ff44010fe44010fd44010
  | 1 => 0xffc8620ff88620ff48620ff08620bf98220ffd4220ff94220ff54220ff14220ffd0220ff90220ff50220ff10220ffcc220ff8c220ff4c220ff0c220ffc8220fec8220fbc8220ffd9520dfd9520bfd95209fd9520ff99520bf99520ff59520bf59520ff19520df19520bf195209f19520ffd9120bfd9120ff99120bf99120ff59120bf59120ff19120bf19120ffd5120ff95120ff55120ff15120ffd8d20bfd8d20ff98d20bf98d20ff58d20bf58d20ff18d20bf18d20ffd4d20ff94d20ff54d20ff14d20ffd0d20ff90d20ff50d20ff10d20ffd4920ff94920fb94920ff54920fb54920ff14920ffd0920ff90920ff50920ff10920ffcc920ff8c920ff4c920ff0c920ffd8520bfd8520ff98520ff58520ff18520bf18520ffd4520ff94520ff54520ff14520ffd0520ff90520ff50520ff10520ffcc520ff8c520ff4c520ff0c520ffc8520ff88520ff48520ff08520ffd4120ff94120ff54120ff14120ffd0120ff90120ff50120ff10120ffcc120ff8c120ff4c120ff0c120ffc8120fec8120ff88120fb88120ffd9420bfd9420ff99420df99420bf994209f99420ff59420df59420bf594209f59420ff19420bf19420ffd9020bfd9020ff99020bf99020ff59020bf59020ff19020bf19020ffd5020ff95020ff55020ff15020ffd8c20bfd8c20ff98c20bf98c20ff58c20bf58c20ff18c20bf18c20ffd4c20ff94c20ff54c20ff14c20ffd0c20ff90c20ff50c20ff10c20bf98820ffd4820ff94820ff54820ff14820ffd0820ff90820ff50820ff10820ffcc820ff8c820ff4c820ff0c820ffd8420ff98420bf98420ff58420bf58420ff18420ffd4420ff94420ff54420ff14420ffd0420ff90420ff50420ff10420ffcc420ff8c420ff4c420ff0c420ffc8420ff88420ff48420ff08420bf98020ffd4020ff94020ff54020ff14020ffd0020ff90020ff50020ff10020ffcc020ff8c020ff4c020ff0c020ffc8020fbc8020ff88020fe88020ff48020fe48020fb48020ffd9710bfd9710ff99710bf99710ff59710bf59710ff19710bf19710ffd9310bfd9310ff99310bf99310ff59310bf59310ff19310bf19310ffd5310ff95310ff55310ff15310ffd8f10bfd8f10ff98f10bf98f10ff58f10bf58f10ff18f10bf18f10ffd4f10ff94f10ff54f10ff14f10ffd0f10ff90f10ff50f10ff10f10ffd8b10bfd8b10ff98b10bf98b10ff58b10bf58b10ff18b10bf18b10ffd4b10ff94b10ff54b10ff14b10ffd0b10ff90b10ff50b10ff10b10ffccb10ff8cb10ff4cb10ff0cb10ffd4710ff94710ff54710ff14710ffd0710ff90710ff50710ff10710ffcc710ff8c710ff4c710ff0c710ffc8710ff88710ff48710ff08710ffd4310ff94310ff54310ff14310ffd0310ff90310ff50310ff10310ffcc310ff8c310ff4c310ff0c310ffc8310ff8
  | 2 => 0xd8930ff98930ff58930ff18930bf18930ffd4930ff94930ff54930ff14930ffd0930ff90930ff50930ff10930ffcc930ff8c930ff4c930ff0c930ffd8530bfd8530ff98530ff58530ff18530bf18530ffd4530ff94530ff54530ff14530ffd0530ff90530ff50530ff10530ffcc530ff8c530ff4c530ff0c530ffc8530ff88530ff48530ff08530ffd4130ff94130ff54130ff14130ffd0130ff90130ff50130ff10130ffcc130fecc130ff8c130f78c130ffd9430bfd9430ff99430bf99430ff59430bf59430ff19430bf19430ffd9030bfd9030ff99030ef99030bf99030af99030ff59030ef59030bf59030af59030ff19030bf19030ffd5030ff95030ff55030ff15030bf98c30ffd4c30ff94c30ff54c30ff14c30ffd0c30f7d0c30ff90c30ff50c30ff10c30f710c30ffd8830ff98830bf98830ff58830bf58830ff18830ffd4830ff94830ff54830ff14830ffd0830ff90830ff50830ff10830ffcc830ff8c830ff4c830ff0c830ffd8430ff98430bf98430ff58430bf58430ff18430ffd4430ff94430ff54430ff14430ffd0430ff90430ff50430ff10430ffcc430ff8c430ff4c430ff0c430ffc8430ff88430ff48430ff08430bf98030ffd4030ff94030ff54030ff14030ffd0030ff90030ff50030ff10030ffcc030f7cc030ff8c030fe8c030ff4c030fe4c030f74c030ffd9720bfd9720ff99720bf99720ff59720bf59720ff19720bf19720ffd9320bfd9320ff99320bf99320ff59320bf59320ff19320bf19320ffd5320ff95320ff55320ff15320ffd8f20bfd8f20ff98f20bf98f20ff58f20bf58f20ff18f20bf18f20ffd4f20ff94f20ff54f20ff14f20ffd0f20ff90f20ff50f20ff10f20ffd4b20ff94b20fb94b20ff54b20fb54b20ff14b20ffd0b20ff90b20ff50b20ff10b20ffccb20ff8cb20ff4cb20ff0cb20ffd8720ff98720bf98720ff58720bf58720ff18720ffd4720ff94720ff54720ff14720ffd0720ff90720ff50720ff10720ffcc720ff8c720ff4c720ff0c720ffc8720ff88720ff48720ff08720ffd4320ff94320ff54320ff14320ffd0320ff90320ff50320ff10320ffcc320ff8c320ff4c320ff0c320ffd9620bfd9620ff99620bf99620ff59620bf59620ff19620bf19620ffd9220bfd9220ff99220bf99220ff59220bf59220ff19220bf19220ffd5220ff95220ff55220ff15220ffd8e20bfd8e20ff98e20bf98e20ff58e20bf58e20ff18e20bf18e20ffd4e20ff94e20ff54e20ff14e20ffd0e20ff90e20ff50e20ff10e20bf58a20ffd4a20ff94a20ff54a20ff14a20ffd0a20ff90a20ff50a20ff10a20ffcca20ff8ca20ff4ca20ff0ca20ffd8620ff98620bf98620ff58620bf58620ff18620ffd4620ff94620ff54620ff14620ffd0620ff90620ff50620ff10620ffcc620ff8c620ff4c620ff0c62
  | 3 => 0x21fdc8521ff88521fb88521ffd8121bfd8121ff98121ff58121ff18121bf18121ffd4121ff94121ff54121ff14121ffd0121ff90121ff50121ff10121ffd9421bfd9421ff99421bf99421ff59421bf59421ff19421bf19421ffd9021bfd9021ff99021bf99021ff59021bf59021ff19021bf19021ffd5021ff95021ff55021ff15021ffd8c21bfd8c21ff98c21bf98c21ff58c21bf58c21ff18c21bf18c21ffd4c21ff94c21ff54c21ff14c21ffd0c21ff90c21ff50c21ff10c21bf98821ffd4821ff94821ff54821ff14821ffd0821ff90821ff50821ff10821ffcc821ff8c821ff4c821ff0c821bf98421ffd4421ff94421ff54421ff14421ffd0421ff90421ff50421ff10421ffcc421ff8c421ff4c421ff0c421ffc8421fbc8421ff88421fd88421ff48421fd48421fb48421ffd8021ff98021bf98021ff58021bf58021ff18021ffd4021ff94021ff54021ff14021ffd0021ff90021ff50021ff10021ffd9730bfd9730ff99730bf99730ff59730bf59730ff19730bf19730ffd9330bfd9330ff99330bf99330ff59330bf59330ff19330bf19330ffd5330ff95330ff55330ff15330ffd4f30ff94f30ff54f30ff14f30ffd0f30ff90f30ff50f30ff10f30ffd8b30ff98b30bf98b30ff58b30bf58b30ff18b30ffd4b30ff94b30ff54b30ff14b30ffd0b30ff90b30ff50b30ff10b30ffccb30ff8cb30ff4cb30ff0cb30ffd8730ff98730bf98730ff58730bf58730ff18730ffd4730ff94730ff54730ff14730ffd0730ff90730ff50730ff10730ffcc730ff8c730ff4c730ff0c730ffc8730ff88730ff48730ff08730ffd4330ff94330ff54330ff14330ffd0330ff90330ff50330ff10330ffd9630bfd9630ff99630bf99630ff59630bf59630ff19630bf19630ffd9230bfd9230ff99230bf99230ff59230bf59230ff19230bf19230ffd5230ff95230ff55230ff15230bf58e30ffd4e30ff94e30ff54e30ff14e30ffd0e30f7d0e30ff90e30ff50e30ff10e30f710e30ffd8a30ff98a30bf98a30ff58a30bf58a30ff18a30ffd4a30ff94a30ff54a30ff14a30ffd0a30ff90a30ff50a30ff10a30ffcca30ff8ca30ff4ca30ff0ca30ffd8630ff98630bf98630ff58630bf58630ff18630ffd4630ff94630ff54630ff14630ffd0630ff90630ff50630ff10630ffcc630ff8c630ff4c630ff0c630ffc8630ff88630ff48630ff08630bf98230ffd4230ff94230ff54230ff14230ffd0230ff90230ff50230ff10230ffcc230fecc230f7cc230ffd9530bfd9530ff99530bf99530ff59530bf59530ff19530bf19530ffd9130efd9130bfd9130afd9130ff99130bf99130ff59130bf59130ff19130ef19130bf19130af19130ffd5130ff95130ff55130ff15130ffd4d30ff94d30ff54d30ff14d30ffd0d30ff90d30ff50d30ff10d30ffd8930bf
  | 4 => 0xf99431bf99431ff59431bf59431ff19431bf19431ffd9031bfd9031ff99031bf99031ff59031bf59031ff19031bf19031ffd5031ff95031ff55031ff15031bf98c31ffd4c31ff94c31ff54c31ff14c31ffd0c31ff90c31ff50c31ff10c31ffd8831ff98831bf98831ff58831bf58831ff18831ffd4831ff94831ff54831ff14831ffd0831ff90831ff50831ff10831ffcc831ff8c831ff4c831ff0c831bf98431ffd4431ff94431ff54431ff14431ffd0431ff90431ff50431ff10431ffcc431f7cc431ff8c431fd8c431ff4c431fd4c431f74c431ffd8031ff98031bf98031ff58031bf58031ff18031ffd4031ff94031ff54031ff14031ffd0031ff90031ff50031ff10031ffd9721bfd9721ff99721df99721bf997219f99721ff59721df59721bf597219f59721ff19721bf19721ffd9321bfd9321ff99321bf99321ff59321bf59321ff19321bf19321ffd5321ff95321ff55321ff15321ffd8f21bfd8f21ff98f21bf98f21ff58f21bf58f21ff18f21bf18f21ffd4f21ff94f21ff54f21ff14f21ffd0f21ff90f21ff50f21ff10f21ffd4b21ff94b21ff54b21ff14b21ffd0b21ff90b21ff50b21ff10b21ffccb21ff8cb21ff4cb21ff0cb21ffd4721ff94721ff54721ff14721ffd0721ff90721ff50721ff10721ffcc721ff8c721ff4c721ff0c721ffd8321ff98321bf98321ff58321bf58321ff18321ffd4321ff94321ff54321ff14321ffd0321ff90321ff50321ff10321ffd9621bfd9621ff99621bf99621ff59621bf59621ff19621bf19621ffd9221bfd9221ff99221bf99221ff59221bf59221ff19221bf19221ffd5221ff95221ff55221ff15221ffd8e21bfd8e21ff98e21bf98e21ff58e21bf58e21ff18e21bf18e21ffd4e21ff94e21ff54e21ff14e21ffd0e21ff90e21ff50e21ff10e21bf58a21ffd4a21ff94a21ff54a21ff14a21ffd0a21ff90a21ff50a21ff10a21ffcca21ff8ca21ff4ca21ff0ca21bf98621ffd4621ff94621ff54621ff14621ffd0621ff90621ff50621ff10621ffcc621ff8c621ff4c621ff0c621ffc8621fdc8621fbc8621ffd8221ff98221bf98221ff58221bf58221ff18221ffd4221ff94221ff54221ff14221ffd0221ff90221ff50221ff10221ffd9521bfd9521ff99521bf99521ff59521bf59521ff19521bf19521ffd9121bfd9121ff99121bf99121ff59121bf59121ff19121bf19121ffd5121ff95121ff55121ff15121ffd8d21bfd8d21ff98d21bf98d21ff58d21bf58d21ff18d21bf18d21ffd4d21ff94d21ff54d21ff14d21ffd0d21ff90d21ff50d21ff10d21ffd4921ff94921ff54921ff14921ffd0921ff90921ff50921ff10921ffcc921ff8c921ff4c921ff0c921ffd4521ff94521ff54521ff14521ffd0521ff90521ff50521ff10521ffcc521ff8c521ff4c521ff0c521ffc85
  | 5 => 0x132ffd9432bfd9432ff99432bf99432ff59432bf59432ff19432bf19432ffd9032bfd9032ff99032bf99032ff59032bf59032ff19032bf19032ffd5032ff95032ff55032ff15032bf98c32ffd4c32ff94c32ff54c32ff14c32ffd0c32ff90c32ff50c32ff10c32bf98832ffd4832ff94832ff54832ff14832ffd0832ff90832ff50832ff10832ffcc832f7cc832ff8c832fb8c832ff4c832fb4c832f74c832ffd8432ff98432bf98432ff58432bf58432ff18432ffd4432ff94432ff54432ff14432ffd0432ff90432ff50432ff10432ffd8032ff98032bf98032ff58032bf58032ff18032ffd4032ff94032ff54032ff14032ffd0032ff90032ff50032ff10032ffd9731bfd9731ff99731bf99731ff59731bf59731ff19731bf19731ffd9331bfd9331ff99331bf99331ff59331bf59331ff19331bf19331ffd5331ff95331ff55331ff15331ffd4f31ff94f31ff54f31ff14f31ffd0f31ff90f31ff50f31ff10f31ffd8b31ff98b31bf98b31ff58b31bf58b31ff18b31ffd4b31ff94b31ff54b31ff14b31ffd0b31ff90b31ff50b31ff10b31ffccb31ff8cb31ff4cb31ff0cb31ffd4731ff94731ff54731ff14731ffd0731ff90731ff50731ff10731ffd8331ff98331bf98331ff58331bf58331ff18331ffd4331ff94331ff54331ff14331ffd0331ff90331ff50331ff10331ffd9631bfd9631ff99631bf99631ff59631bf59631ff19631bf19631ffd9231bfd9231ff99231ef99231bf99231af99231ff59231ef59231bf59231af59231ff19231bf19231ffd5231ff95231ff55231ff15231bf58e31ffd4e31ff94e31ff54e31ff14e31ffd0e31ff90e31ff50e31ff10e31ffd8a31ff98a31bf98a31ff58a31bf58a31ff18a31ffd4a31ff94a31ff54a31ff14a31ffd0a31ff90a31ff50a31ff10a31ffcca31ff8ca31ff4ca31ff0ca31bf98631ffd4631ff94631ff54631ff14631ffd0631ff90631ff50631ff10631ffcc631fdcc631f7cc631ffd8231ff98231bf98231ff58231bf58231ff18231ffd4231ff94231ff54231ff14231ffd0231ff90231ff50231ff10231ffd9531bfd9531ff99531bf99531ff59531bf59531ff19531bf19531ffd9131bfd9131ff99131bf99131ff59131bf59131ff19131bf19131ffd5131ff95131ff55131ff15131ffd4d31ff94d31ff54d31ff14d31ffd0d31ff90d31ff50d31ff10d31ffd8931bfd8931ff98931ff58931ff18931bf18931ffd4931ff94931ff54931ff14931ffd0931ff90931ff50931ff10931ffcc931ff8c931ff4c931ff0c931ffd4531ff94531ff54531ff14531ffd0531ff90531ff50531ff10531ffcc531fdcc531ff8c531f78c531ffd8131bfd8131ff98131ff58131ff18131bf18131ffd4131ff94131ff54131ff14131ffd0131ff90131ff50131ff10131ffd9431bfd9431f
  | 6 => 0xa4a92a5094a4f294a518c620000054a4b294a518c62c030052a532148b224a4214a518c4318c4318c62529545314b294a518c62594a528c631294a5294e54165294a318c400000a52953294a518c62058165294a52824294a4294a3188631886318c4e63a8e639e5294a318c4e7394e93965294a318c4000025294a318c4e739ce739e5294a318c580601806024294a4294a3188631886318c506429064225294a318c508415094165294a318c4000011294a518c6283a0e83a0e794a528c63102c0b02c0b39c129085294852448918c4318c4318c628321083215294a518c6284a0a8420b294a518c6200001294a518c6283a0e83a0f294a518c62c0300c030073a11214a5214a518c6210c4f11c4318c62731d4731cf294a518c62739ca749cb294a518c6200000794a528c63139ce739ce744a5294631881605816059ce739ce0ffd9732bfd9732ff99732bf99732ff59732bf59732ff19732bf19732ffd9332bfd9332ff99332bf99332ff59332bf59332ff19332bf19332ffd5332ff95332ff55332ff15332ffd4f32ff94f32ff54f32ff14f32ffd0f32ff90f32ff50f32ff10f32ffd4b32ff94b32ff54b32ff14b32ffd0b32ff90b32ff50b32ff10b32ffd8732ff98732bf98732ff58732bf58732ff18732ffd4732ff94732ff54732ff14732ffd0732ff90732ff50732ff10732ffd8332ff98332bf98332ff58332bf58332ff18332ffd4332ff94332ff54332ff14332ffd0332ff90332ff50332ff10332ffd9632bfd9632ff99632bf99632ff59632bf59632ff19632bf19632ffd9232bfd9232ff99232bf99232ff59232bf59232ff19232bf19232ffd5232ff95232ff55232ff15232bf58e32ffd4e32ff94e32ff54e32ff14e32ffd0e32ff90e32ff50e32ff10e32bf98a32ffd4a32ff94a32ff54a32ff14a32ffd0a32ff90a32ff50a32ff10a32ffcca32fbcca32f7cca32ffd8632ff98632bf98632ff58632bf58632ff18632ffd4632ff94632ff54632ff14632ffd0632ff90632ff50632ff10632ffd8232ff98232bf98232ff58232bf58232ff18232ffd4232ff94232ff54232ff14232ffd0232ff90232ff50232ff10232ffd9532bfd9532ff99532bf99532ff59532bf59532ff19532bf19532ffd9132bfd9132ff99132bf99132ff59132bf59132ff19132bf19132ffd5132ff95132ff55132ff15132ffd4d32ff94d32ff54d32ff14d32ffd0d32ff90d32ff50d32ff10d32ffd4932ff94932ff54932ff14932ffd0932ff90932ff50932ff10932ffcc932fbcc932ff8c932f78c932ffd8532bfd8532ff98532ff58532ff18532bf18532ffd4532ff94532ff54532ff14532ffd0532ff90532ff50532ff10532ffd8132bfd8132ff98132ff58132ff18132bf18132ffd4132ff94132ff54132ff14132ffd0132ff90132ff50132ff10
  | 7 => 0x900005c0280100101206c0400000608c038390000081f81509e0f8198080002f41080a00603c1980001e024020040340280d80004e1d42402e07c228000190a80300500a18a014030240540e8128ab0082740080c11800c000100a4198008070040003502c0060dc0392d1940540004040200c0200100000c0001a90a5290a528c6218c6218c63194a528c63194a528c6314a4e94265294a318c5290240994a528c63190a5290a528c6218c6218c63134a52946318965294a318c4a6294a72a0b294a518c625280a02ca52946318c85294852946310c6310c6318ca52946318ca5294631898c529906318f294a518c626018c604a52946318c85294852946310c6310c6318a65294a318c4b294a518c625294a5314a53950594a528c631294050165294a318c64294a4294a3188631886318c65294a318c5082a12894a528c631518ca94a528c631420080225294a318c64294a4294a318c42189a23886318c4d294a518c626314c934a5294631898c631e5294a318c4c6398c0300d294a518c63214a5214a518c4318c4318c63294a518c626498c62ca5294631898c634a5294631898c6318063181294a518c63214a5214a518c4318c4318c62894a528c63139ca749e5294a318c546328d294a518c627398c631ce701c0794a528c63190a459125210a528c6218c6218c631294aa298a594a528c63194a528c631294a594a528c63141d07294050165294a318c64294a4294a3188631886318c4e63a8e639e5294a318c51294a518c6292a4a594a528c63139ce7294e7380e03ca52946318c85294852946310c6310c6318a0c8420c854a52946318ca52946318a4a92ca52946318a0e8394a73a0084201294a518c63214a5214a518c4318c4318c62529545314b294a518c62594a528c631294a53ca529463189ce7394a5294a7294050165294a318c64294a4294a3188631886318c65294a318c54a2a92a94a528c631518ca528ea42a5294a318c546328000025294a318c64294a4294a3188631886318c4d294a518c631898c5324d294a518c626318c631cc834a5294631898c63000002a5294a318c4c60485294852944d11c4318c6210c6318ca529463189926318b294a518c626318c6418c63ca5294631898c63000004a5294631898c634852948529463188431544710c6318aa5294a318c631528aa4aa5294a318c5463294a3a90a94a528c631518ca0000034a52946318a946318c090a5290a528c6218c6218c631294aa298a594a528c63194a5294a318c4a5294a53950594a528c63100000294a594a528c6316018090a5290a528c6218c6218c6314992a4992994a528c6314ca52946318a4a92a5274a13294a518c620000054a4a594a528c63102c0b2941290852948524c8918c4318c4318c629325293255294a518c63294a52946318
  | 8 => 0xea73f67829e4a72e46904962dc1791406570d45cf1816a65f320f1310f536375976b33429a22500b14338816f6106fa6ce5c21db10833532857942e6a21b25de34c27c05b5754920dc5bd22a11f51a0a20337560ef79872311c6953437152ea77461b5db4680f26d479216821013c6d003e0ae24777026e12d76745237a04e07761e26226c0d91fd00145637278c2d23032b93445af44409020135b3d57120491b61b542a3cd2e91553090a71ee53e5983ab6b32bd0e02cb0a166a56e2ad1c60423e17550052212332e628c10a6e21ab4b633f3cf5d870d29c46b07252d3af2ba6ef50553a17d4133b81744bf5731d25746f25041b75a33d742867223d3c92425e11e66d512661c4e84606382862646de35257e03054758a4d33140414177586084f82836180433cb2b83613931866eb03f2b715a6bb3066d96ae2de6bf43305433070113605d52335434943d2ab6415a916414c58d57751e15765352943868921947b2c14dc6043db64e7062cd1b929140756f7891612150ab2e532a7a316761460c1ad3562467a11f41064dd42c6854cb1c85604c436f44a06326a18b35023c2ee4227141eb4f566107a4752362d878d2200324405874162b56c315b35347026709f41f4837a465f3570824ec0bc41812b4df4f233214944839200109a11c2103001e144a21f702e26c009940b6094e54160340580000495e059f882a72600000b991262000e84f1309d4f787628c05c0cab602e01cac8650020005c81c222014004ce00a0a47a0213749400180015544c0001e0146d8829fe01e094188db00a04c039d10dc4e1312cf00019c0205508ca58038dc3960a05e8431743301306f0242580d00007e4480104309e0201d0d915e0281b8b5008515a1b77086010000000680501600f2500782901d01a3f0ae05e07a1883280202c0500780c2ec018171f54d0130078c326a0001488602e0003480a0a45c404032000038020b40001e90888331a0401001a05a0fd3880401c0c80607f01a1ccb8001034028070072040000888d0006a8b807a0002a8bf00c21c024120008a6028211a6000000ac013002035cc8051140014c8041b40044700033a024009ba00002cc800002a010000171181cc1d00112c0081d018046098588b10007e8000050024a80d8100040dc0d808004180040550461d8000020140640806501c14004803036034011240b2024038d60000ec020010e20e801012004030090940520980280012202c1f0470000580602f06a0040401900a1880080003c0b0e9a9a09a0000280105400031824004034138050000b45580019c0643e0ee00400c130170000381909000011c0bac600e02c0000018e0180086f00002c0500c064034208050000340900e05c0041c83501a0101101b0001b00d800008090480320000140181f0ca21001807162000
  | 9 => 0x445014d36033b7a43fe3bf29b47e6165b84ba7a42d33ce3f10de5677a46ed27747822d4f641e2783d61e309c74059b00957b7a454b1734ae1ae3da1356b912306b5627a44865d51a70e43553d26a81844d50d548c48f66452000a72a78464714a20245328279c6b62925806271322a82271fb1c15566292006623647816734d94362c662453b4f96e373830a1470aa1c703901723a7a417e69a0526673460d049a0b86057026df31806f0fd3ff14f46957635e45a7375ab0bb3426ad6b44514be0a45be7174fc3797a458e0691d604d7242f76cc2755f92da0a527923e50d5ca4fd74a7a438734d5d471f3401626450ba1110f94f318362660e1e83f01f722f00242d4746fc46f3f41f36ff44d27b25b0704670db1d106c5ce2eb0073ad4976717085854c26801ef33966552575c2371bc53917f26f60d65541a5c521f79500d2c95365b049c4e17427967304ab2cc48d5f03044494ef23177c45e44543162363a0fe3ba5951cb18c11772d6354d475338b38321a55376c5320376bd1c962071a0e156b6115212fc43a79e10765165e79b52e49e5bc3943fa6420152d60786c708c4241d355f34b5f65171800e625970f6884cf11939176373625e52c2564200731fc72e57051628e1a31246f33670982e216655105f6d23734b97615aa20a53336b3cc5e508940e21e33600e63f19e20b3701b80e85923053004e719c0fc74706860333d49d68a1710d25d17071871a46284372054435d21c012208a2aa3b104404630e32c22e1dd0b13c05b11ed68412815373464b0833212f00f815d25c2c83b444f62c67a3740c90113b040a24354278e04f25d5122f330b58f02937528f4612733e815f6e61984d721863606100631263e6aa1e15454c62112887910ee0361ce37802c77f3376773e952b2531c24f151f57869e5b438f22b5962b141940d41b01e5274e94e52f64e44002124a311812908709339946201224b5a527a2693e43d96661881a507420632b4c123f24f1502383ca05a5fc46e1092a60fb2ae54977e3a90af60f0b40471e27315573b269c67b4035435b71a13c507f21353f16d2e019270a04c12578f4576c50fa1c33d001023060a2242d13955f555501640f69467f37c4eb3a56791943de78628a3663f802a4bb0262d41163485593dc5483a164d62a20876266b02b5f476609a32f3455467576b81a05d765454a17b6b071e46348526139800009514210b73e1762975fd42603b76d39f11d1e70224591d754156949b4c01456d831709668f42f2093fb05967c2656c90c426d16a32340127e2492283710bf06d5c36af3bd73555a4aa1bd38657f64f38443451051107d2af4cc3ee4c550366d34f0cd3021f943c7785fe6f637b74501c0e52a241c5244a450238c45f3e52c46f95fb6740a309e2934db1382ce6483163bb43e47f6996dd1
  | 10 => 0x35c3337971bb6581374885d60a604808676029509d1132bf2740d85a614462f4a002025479f2e32a94795b35c438d6c15911964b77a46a93c43f53a83dd35831e5225e06f52a171d4bd7a477d68c7a46971b06920d730146c3c70cc50e19b1a20e752f4844950214f03683aa4992a312a43f3820eb7931595636fd3203ec5a250112f59a61d1d041d7107640250557697265e313d57256d2e84d14de6d72ed69b03d19d2a05c066f2221cd0b51f504503827f1106605933f262144b7330d35ff63b0e37a40c04775e60f61cf6a325520c0df2d03f306553416c0273651de7754322043134a91d845b4ed75a47c1145ef47d6ca5cd7a474668734a73b50f57c6db4466527a45c834e3f736216903502859e0976be6c672f57d7734ac2a57a441232e2bc7292070a80f46e04411be4ce7416a065645841037f63038a5ac2f156149311223b48a4761e931b7a45df53d6a125f6a52a73f97a41ec1f04ea5081411e013a44213b27d2d57725401512847a47a413f1784556a772766c7a442739e0b33c34b07a403c08d1046016063df5070dd71177770e6ec7440925062f24d65ad1a87881561e459030c3d83317a47a47a47a44ee43b4663b569d27236a33a0ff64632d10f7a47a46cd40c74f62b09105c2dd4c92f56f17795dd50912776e21619f58c4e236e72c61550c7a46ee13e0136ea76f1724d202d7a47a44735f859f4bc7a41031770857a463974874951d2874b10566f72c52346707a44a65892407280ac2517a456c7a40f357105754d56a4af05e7034c85e856840475e43961704a6344a86120f111b3772e726648e23953855d0c55c767e64c74c2ec69f3265ea5507a41d918261306a3515ee1cc55e31d0751da12c77a1024804d81bf4f719a06e3a76f009411a1890f02234827132b257a2f87a24a51214875a800c7a47a45b275162d74b39a39626316b5da21d33c60b0241012450d146d2fb58416e24c5eb6194e05543bc5e23f65e94b41af4111ba2ca7434fb69618e0794cd01f17a26007c73a3fc61a7995dc2487a442b4290996cf6b50da3c26d351c64975f5bf2a45d008e1465970345262df74d5cb17c7801ac1543b90032351df72572016008065b4350d61a939b71b4ad58158233875021c4725ba35f2f94897165522172ac33e02e0b63b61957a02fd40b3d43e634165a2293a22c05861914ff0081dc51903172b5c62985cc5ae31906459c01838e0c35881755180c625873268e61f79066e47a0e21c529454f2bb12e4985b54fe3e042328d1003ed5f720e50b7712ff2817392854306da6834903763805b94f42140c26fb31c04b0be2b36d66a47a44056753ae1392d949468d5fa7765586504c75e77a475d4a10ad5d967d4086e76f44b35991201ff35d3ea6bc78729f6ab2b631146470b5654fa0ec7a416550076848136c2717a
  | 11 => 0x2e12c245c3fd4e358b10e0535137043071b33c60ca18f6815a46c839c0816406e95a75ed3904477852fe2f41f175403a0661f238907e1f652868b37e3e33810766c23eb6cb30808f7832966327a422624a20d46578b4093a02fa3250196ac4b54b853153044c09b14e63d37d06779d0ce65c65d58349f6c462508b45d6e51aa3b706032976a1b47a453526b5f20580c87a40c16691f854462e6c054c44e15c6931a62c72cf6ba2577a47947a402f67663111e4d00620bd1632323b300429d2415c16437a41937a46fe55c53776556477b1ca39d0a013066336d4da69814b41428025a35a49168270c64a2995b601d2db5666330716862be0844b272263c1d47197a422c46a0512c34214153977a43a60cb6376dc6226e83d37000cf7520c75a102348b0884063e71e579a2502b410d13431059d6681fa55b7093d150a3692762705941853c818a5d30b275b3be13351b10560964469131a4e60a93226d14c318d4a23c13ac3ef5e438524d78a15801407b0e96f832400f0b015e7a40f74020405152446b74ca6b15f17822b019774e7a45141156074256e110c5ec5a01991d50ed5c971c1487a40ea31515219024e2d753c25220360028952a29030d1c473c3a33a431f2ef6e45bb1b10b947135960201b30f65972173d3277053477186b254e0b74541fe17021b05026828b3e201a
  | _ => 0

def mainK9 : Nat → Nat
  | 0 => 0x2c2cc1f0a69abc70f093c2e117b24e8803c1899e2e226c52050f019568b098774f1e1462d8725786478876a918266a433c78f1e2442ddc9d5624e2d780469e60408c00a107478200640010e6420c55aa55aa5500aa550000aa55000000ffaa7f953faa9fc54ffa9ff94ffaa7fc53ffa1ff90ffa87fc43ffa97f94bfaa5fc52ffa17f90bfa85fc42ff997f8cbfa65fc32ffa8ff947faa3fc51ffa0ff907fa83fc41ff98ff8c7fa63fc31ff90ff887fa43fc21ffa87f943faa1fc50ffa07f903fa81fc40ff987f8c3fa61fc30ff907f883fa41fc20ff887f843fa21fc10
  | _ => 0

def mainK10 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def mainN (k : Nat) : Nat :=
  match k with
  | 5 => 36
  | 6 => 1324
  | 7 => 6385
  | 8 => 1956
  | 9 => 60
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
  | 5 => packedAt mainK5 (2196+i*8) 8
  | 6 => packedAt mainK6 (66200+i*7) 7
  | 7 => packedAt mainK7 (249015+i*6) 6
  | 8 => packedAt mainK8 (54768+i*5) 5
  | 9 => packedAt mainK9 (1020+i*2) 2
  | _ => 0

def mainI (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt mainK5 (2538+((h/9+packedAt mainK5 (2484+(h % 9)*6) 6) % 46)*7) 7
  | 6 => packedAt mainK6 (79109+((h/331+packedAt mainK6 (75468+(h % 331)*11) 11) % 1378)*12) 12
  | 7 => packedAt mainK7 (308073+((h/1596+packedAt mainK7 (287325+(h % 1596)*13) 13) % 6393)*14) 14
  | 8 => packedAt mainK8 (69927+((h/489+packedAt mainK8 (64548+(h % 489)*11) 11) % 2012)*12) 12
  | 9 => packedAt mainK9 (1245+((h/15+packedAt mainK9 (1140+(h % 15)*7) 7) % 74)*7) 7
  | 10 => packedAt mainK10 (7+((h/1+packedAt mainK10 (6+(h % 1)*1) 1) % 2)*2) 2
  | _ => 2

def mainPos : Nat → Bits
  | 0 => 0x9edfdfffccce4f97fa037bb27b7f7fff
  | 1 => 0x76b9797ed138b8fca3765ec5dae5e5fb
  | 2 => 0xfbd2bfcb6391d3f80cbbe31bef4aff2d
  | 3 => 0x7dffd295ba21fd015fdc8ccdf7ff4a56
  | 4 => 0xa12004003fff22021ffffffe84801000
  | 5 => 0x400420203ffffffff020102100108080
  | _ => 0

def mainNeg : Nat → Bits
  | 0 => 0x70739c00003c39f001f30001c1ce7
  | 1 => 0x7e38383e003c381c003f1fc1f8e0e0f8
  | 2 => 0x7fc03fc003c1c3e0003fe001ff00ff00
  | 3 => 0x7fffc0003c01fc001fc00001ffff0000
  | 4 => 0x800000003ffe00001ffffffe00000000
  | 5 => 0x3fffffffe000000000000000
  | _ => 0

def mainAtlas : Atlas := ⟨10, rawDecor 63 mainPos mainNeg, 0xfeeaeac8fca0a880, mainN, mainR, mainH, mainI, [(neg (inputs.getD 4 zero), 9), ((inputs.getD 5 zero), 9), ((inputs.getD 4 zero), 8), (neg (inputs.getD 5 zero), 8), (neg (inputs.getD 2 zero), 7), ((inputs.getD 3 zero), 7), (neg (inputs.getD 1 zero), 7), ((inputs.getD 1 zero), 7), ((inputs.getD 2 zero), 7), (neg (inputs.getD 3 zero), 7), (neg (inputs.getD 0 zero), 6), ((inputs.getD 0 zero), 6)], []⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a0p3_0 : Interval s0a0Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a0p4_0 : Interval s0a0Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a0p5_0 : Interval s0a0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a0Complete : Complete s0a0Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a0p3_0 i (Nat.zero_le i) hi
  · exact s0a0p4_0 i (Nat.zero_le i) hi
  · exact s0a0p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a0Pair : properPairs (target s0a0Atlas) (asRow s0a0Pos) (asRow s0a0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a0Lower :
    Lower true (roots s0a0Atlas) (target s0a0Atlas) 6 := by
  have ready : Ready s0a0Atlas (asRow s0a0Pos) (asRow s0a0Neg) := by
    refine ⟨s0a0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 1, 5), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a1p2_0 : Interval s0a1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a1p3_0 : Interval s0a1Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a1p4_0 : Interval s0a1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a1Complete : Complete s0a1Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a1p2_0 i (Nat.zero_le i) hi
  · exact s0a1p3_0 i (Nat.zero_le i) hi
  · exact s0a1p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a1Pair : properPairs (target s0a1Atlas) (asRow s0a1Pos) (asRow s0a1Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a1Lower :
    Lower true (roots s0a1Atlas) (target s0a1Atlas) 5 := by
  have ready : Ready s0a1Atlas (asRow s0a1Pos) (asRow s0a1Neg) := by
    refine ⟨s0a1Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a1Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a2p2_0 : Interval s0a2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a2p3_0 : Interval s0a2Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a2p4_0 : Interval s0a2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a2Complete : Complete s0a2Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a2p2_0 i (Nat.zero_le i) hi
  · exact s0a2p3_0 i (Nat.zero_le i) hi
  · exact s0a2p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a2Pair : properPairs (target s0a2Atlas) (asRow s0a2Pos) (asRow s0a2Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a2Lower :
    Lower true (roots s0a2Atlas) (target s0a2Atlas) 5 := by
  have ready : Ready s0a2Atlas (asRow s0a2Pos) (asRow s0a2Neg) := by
    refine ⟨s0a2Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a2Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a3p2_0 : Interval s0a3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a3p3_0 : Interval s0a3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a3p4_0 : Interval s0a3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a3Complete : Complete s0a3Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a3p2_0 i (Nat.zero_le i) hi
  · exact s0a3p3_0 i (Nat.zero_le i) hi
  · exact s0a3p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a3Pair : properPairs (target s0a3Atlas) (asRow s0a3Pos) (asRow s0a3Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a3Lower :
    Lower true (roots s0a3Atlas) (target s0a3Atlas) 5 := by
  have ready : Ready s0a3Atlas (asRow s0a3Pos) (asRow s0a3Neg) := by
    refine ⟨s0a3Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a3Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 9, 11), (inputs.getD 3 zero, 3, 11), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a4p2_0 : Interval s0a4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a4p3_0 : Interval s0a4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a4p4_0 : Interval s0a4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a4Complete : Complete s0a4Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a4p2_0 i (Nat.zero_le i) hi
  · exact s0a4p3_0 i (Nat.zero_le i) hi
  · exact s0a4p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a4Pair : properPairs (target s0a4Atlas) (asRow s0a4Pos) (asRow s0a4Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a4Lower :
    Lower true (roots s0a4Atlas) (target s0a4Atlas) 5 := by
  have ready : Ready s0a4Atlas (asRow s0a4Pos) (asRow s0a4Neg) := by
    refine ⟨s0a4Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a4Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a5p2_0 : Interval s0a5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a5p3_0 : Interval s0a5Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a5p4_0 : Interval s0a5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a5Complete : Complete s0a5Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a5p2_0 i (Nat.zero_le i) hi
  · exact s0a5p3_0 i (Nat.zero_le i) hi
  · exact s0a5p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a5Pair : properPairs (target s0a5Atlas) (asRow s0a5Pos) (asRow s0a5Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a5Lower :
    Lower true (roots s0a5Atlas) (target s0a5Atlas) 5 := by
  have ready : Ready s0a5Atlas (asRow s0a5Pos) (asRow s0a5Neg) := by
    refine ⟨s0a5Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a5Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 3, 11)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a6p3_0 : Interval s0a6Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a6Complete : Complete s0a6Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a6p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a6Pair : properPairs (target s0a6Atlas) (asRow s0a6Pos) (asRow s0a6Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a6Lower :
    Lower true (roots s0a6Atlas) (target s0a6Atlas) 4 := by
  have ready : Ready s0a6Atlas (asRow s0a6Pos) (asRow s0a6Neg) := by
    refine ⟨s0a6Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a7p3_0 : Interval s0a7Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0a7Complete : Complete s0a7Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0a7p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a7Pair : properPairs (target s0a7Atlas) (asRow s0a7Pos) (asRow s0a7Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0a7Lower :
    Lower true (roots s0a7Atlas) (target s0a7Atlas) 4 := by
  have ready : Ready s0a7Atlas (asRow s0a7Pos) (asRow s0a7Neg) := by
    refine ⟨s0a7Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s0a7Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p3_0 : Interval s0Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_0 : Interval s0Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_64 : Interval s0Atlas 4 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_128 : Interval s0Atlas 4 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_192 : Interval s0Atlas 4 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_256 : Interval s0Atlas 4 256 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_320 : Interval s0Atlas 4 320 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_384 : Interval s0Atlas 4 384 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_448 : Interval s0Atlas 4 448 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_512 : Interval s0Atlas 4 512 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_576 : Interval s0Atlas 4 576 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p4_640 : Interval s0Atlas 4 640 36 := block_range (n:=36) (by decide +kernel)
theorem s0q4_0_128 : Interval s0Atlas 4 0 128 := concat s0p4_0 s0p4_64
theorem s0q4_128_128 : Interval s0Atlas 4 128 128 := concat s0p4_128 s0p4_192
theorem s0q4_256_128 : Interval s0Atlas 4 256 128 := concat s0p4_256 s0p4_320
theorem s0q4_384_128 : Interval s0Atlas 4 384 128 := concat s0p4_384 s0p4_448
theorem s0q4_512_128 : Interval s0Atlas 4 512 128 := concat s0p4_512 s0p4_576
theorem s0q4_0_256 : Interval s0Atlas 4 0 256 := concat s0q4_0_128 s0q4_128_128
theorem s0q4_256_256 : Interval s0Atlas 4 256 256 := concat s0q4_256_128 s0q4_384_128
theorem s0q4_512_164 : Interval s0Atlas 4 512 164 := concat s0q4_512_128 s0p4_640
theorem s0q4_0_512 : Interval s0Atlas 4 0 512 := concat s0q4_0_256 s0q4_256_256
theorem s0q4_0_676 : Interval s0Atlas 4 0 676 := concat s0q4_0_512 s0q4_512_164
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_0 : Interval s0Atlas 5 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_64 : Interval s0Atlas 5 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_128 : Interval s0Atlas 5 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_192 : Interval s0Atlas 5 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_256 : Interval s0Atlas 5 256 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_320 : Interval s0Atlas 5 320 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_384 : Interval s0Atlas 5 384 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_448 : Interval s0Atlas 5 448 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_512 : Interval s0Atlas 5 512 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_576 : Interval s0Atlas 5 576 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_640 : Interval s0Atlas 5 640 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_704 : Interval s0Atlas 5 704 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_768 : Interval s0Atlas 5 768 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_832 : Interval s0Atlas 5 832 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_896 : Interval s0Atlas 5 896 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_960 : Interval s0Atlas 5 960 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1024 : Interval s0Atlas 5 1024 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1088 : Interval s0Atlas 5 1088 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1152 : Interval s0Atlas 5 1152 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1216 : Interval s0Atlas 5 1216 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1280 : Interval s0Atlas 5 1280 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1344 : Interval s0Atlas 5 1344 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1408 : Interval s0Atlas 5 1408 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1472 : Interval s0Atlas 5 1472 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1536 : Interval s0Atlas 5 1536 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1600 : Interval s0Atlas 5 1600 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1664 : Interval s0Atlas 5 1664 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1728 : Interval s0Atlas 5 1728 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1792 : Interval s0Atlas 5 1792 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1856 : Interval s0Atlas 5 1856 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1920 : Interval s0Atlas 5 1920 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_1984 : Interval s0Atlas 5 1984 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2048 : Interval s0Atlas 5 2048 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2112 : Interval s0Atlas 5 2112 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2176 : Interval s0Atlas 5 2176 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2240 : Interval s0Atlas 5 2240 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2304 : Interval s0Atlas 5 2304 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2368 : Interval s0Atlas 5 2368 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2432 : Interval s0Atlas 5 2432 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2496 : Interval s0Atlas 5 2496 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2560 : Interval s0Atlas 5 2560 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2624 : Interval s0Atlas 5 2624 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2688 : Interval s0Atlas 5 2688 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2752 : Interval s0Atlas 5 2752 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2816 : Interval s0Atlas 5 2816 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p5_2880 : Interval s0Atlas 5 2880 41 := block_range (n:=41) (by decide +kernel)
theorem s0q5_0_128 : Interval s0Atlas 5 0 128 := concat s0p5_0 s0p5_64
theorem s0q5_128_128 : Interval s0Atlas 5 128 128 := concat s0p5_128 s0p5_192
theorem s0q5_256_128 : Interval s0Atlas 5 256 128 := concat s0p5_256 s0p5_320
theorem s0q5_384_128 : Interval s0Atlas 5 384 128 := concat s0p5_384 s0p5_448
theorem s0q5_512_128 : Interval s0Atlas 5 512 128 := concat s0p5_512 s0p5_576
theorem s0q5_640_128 : Interval s0Atlas 5 640 128 := concat s0p5_640 s0p5_704
theorem s0q5_768_128 : Interval s0Atlas 5 768 128 := concat s0p5_768 s0p5_832
theorem s0q5_896_128 : Interval s0Atlas 5 896 128 := concat s0p5_896 s0p5_960
theorem s0q5_1024_128 : Interval s0Atlas 5 1024 128 := concat s0p5_1024 s0p5_1088
theorem s0q5_1152_128 : Interval s0Atlas 5 1152 128 := concat s0p5_1152 s0p5_1216
theorem s0q5_1280_128 : Interval s0Atlas 5 1280 128 := concat s0p5_1280 s0p5_1344
theorem s0q5_1408_128 : Interval s0Atlas 5 1408 128 := concat s0p5_1408 s0p5_1472
theorem s0q5_1536_128 : Interval s0Atlas 5 1536 128 := concat s0p5_1536 s0p5_1600
theorem s0q5_1664_128 : Interval s0Atlas 5 1664 128 := concat s0p5_1664 s0p5_1728
theorem s0q5_1792_128 : Interval s0Atlas 5 1792 128 := concat s0p5_1792 s0p5_1856
theorem s0q5_1920_128 : Interval s0Atlas 5 1920 128 := concat s0p5_1920 s0p5_1984
theorem s0q5_2048_128 : Interval s0Atlas 5 2048 128 := concat s0p5_2048 s0p5_2112
theorem s0q5_2176_128 : Interval s0Atlas 5 2176 128 := concat s0p5_2176 s0p5_2240
theorem s0q5_2304_128 : Interval s0Atlas 5 2304 128 := concat s0p5_2304 s0p5_2368
theorem s0q5_2432_128 : Interval s0Atlas 5 2432 128 := concat s0p5_2432 s0p5_2496
theorem s0q5_2560_128 : Interval s0Atlas 5 2560 128 := concat s0p5_2560 s0p5_2624
theorem s0q5_2688_128 : Interval s0Atlas 5 2688 128 := concat s0p5_2688 s0p5_2752
theorem s0q5_2816_105 : Interval s0Atlas 5 2816 105 := concat s0p5_2816 s0p5_2880
theorem s0q5_0_256 : Interval s0Atlas 5 0 256 := concat s0q5_0_128 s0q5_128_128
theorem s0q5_256_256 : Interval s0Atlas 5 256 256 := concat s0q5_256_128 s0q5_384_128
theorem s0q5_512_256 : Interval s0Atlas 5 512 256 := concat s0q5_512_128 s0q5_640_128
theorem s0q5_768_256 : Interval s0Atlas 5 768 256 := concat s0q5_768_128 s0q5_896_128
theorem s0q5_1024_256 : Interval s0Atlas 5 1024 256 := concat s0q5_1024_128 s0q5_1152_128
theorem s0q5_1280_256 : Interval s0Atlas 5 1280 256 := concat s0q5_1280_128 s0q5_1408_128
theorem s0q5_1536_256 : Interval s0Atlas 5 1536 256 := concat s0q5_1536_128 s0q5_1664_128
theorem s0q5_1792_256 : Interval s0Atlas 5 1792 256 := concat s0q5_1792_128 s0q5_1920_128
theorem s0q5_2048_256 : Interval s0Atlas 5 2048 256 := concat s0q5_2048_128 s0q5_2176_128
theorem s0q5_2304_256 : Interval s0Atlas 5 2304 256 := concat s0q5_2304_128 s0q5_2432_128
theorem s0q5_2560_256 : Interval s0Atlas 5 2560 256 := concat s0q5_2560_128 s0q5_2688_128
theorem s0q5_0_512 : Interval s0Atlas 5 0 512 := concat s0q5_0_256 s0q5_256_256
theorem s0q5_512_512 : Interval s0Atlas 5 512 512 := concat s0q5_512_256 s0q5_768_256
theorem s0q5_1024_512 : Interval s0Atlas 5 1024 512 := concat s0q5_1024_256 s0q5_1280_256
theorem s0q5_1536_512 : Interval s0Atlas 5 1536 512 := concat s0q5_1536_256 s0q5_1792_256
theorem s0q5_2048_512 : Interval s0Atlas 5 2048 512 := concat s0q5_2048_256 s0q5_2304_256
theorem s0q5_2560_361 : Interval s0Atlas 5 2560 361 := concat s0q5_2560_256 s0q5_2816_105
theorem s0q5_0_1024 : Interval s0Atlas 5 0 1024 := concat s0q5_0_512 s0q5_512_512
theorem s0q5_1024_1024 : Interval s0Atlas 5 1024 1024 := concat s0q5_1024_512 s0q5_1536_512
theorem s0q5_2048_873 : Interval s0Atlas 5 2048 873 := concat s0q5_2048_512 s0q5_2560_361
theorem s0q5_0_2048 : Interval s0Atlas 5 0 2048 := concat s0q5_0_1024 s0q5_1024_1024
theorem s0q5_0_2921 : Interval s0Atlas 5 0 2921 := concat s0q5_0_2048 s0q5_2048_873
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_0 : Interval s0Atlas 6 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_64 : Interval s0Atlas 6 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_128 : Interval s0Atlas 6 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_192 : Interval s0Atlas 6 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_256 : Interval s0Atlas 6 256 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_320 : Interval s0Atlas 6 320 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_384 : Interval s0Atlas 6 384 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_448 : Interval s0Atlas 6 448 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_512 : Interval s0Atlas 6 512 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_576 : Interval s0Atlas 6 576 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_640 : Interval s0Atlas 6 640 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_704 : Interval s0Atlas 6 704 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_768 : Interval s0Atlas 6 768 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_832 : Interval s0Atlas 6 832 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_896 : Interval s0Atlas 6 896 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p6_960 : Interval s0Atlas 6 960 56 := block_range (n:=56) (by decide +kernel)
theorem s0q6_0_128 : Interval s0Atlas 6 0 128 := concat s0p6_0 s0p6_64
theorem s0q6_128_128 : Interval s0Atlas 6 128 128 := concat s0p6_128 s0p6_192
theorem s0q6_256_128 : Interval s0Atlas 6 256 128 := concat s0p6_256 s0p6_320
theorem s0q6_384_128 : Interval s0Atlas 6 384 128 := concat s0p6_384 s0p6_448
theorem s0q6_512_128 : Interval s0Atlas 6 512 128 := concat s0p6_512 s0p6_576
theorem s0q6_640_128 : Interval s0Atlas 6 640 128 := concat s0p6_640 s0p6_704
theorem s0q6_768_128 : Interval s0Atlas 6 768 128 := concat s0p6_768 s0p6_832
theorem s0q6_896_120 : Interval s0Atlas 6 896 120 := concat s0p6_896 s0p6_960
theorem s0q6_0_256 : Interval s0Atlas 6 0 256 := concat s0q6_0_128 s0q6_128_128
theorem s0q6_256_256 : Interval s0Atlas 6 256 256 := concat s0q6_256_128 s0q6_384_128
theorem s0q6_512_256 : Interval s0Atlas 6 512 256 := concat s0q6_512_128 s0q6_640_128
theorem s0q6_768_248 : Interval s0Atlas 6 768 248 := concat s0q6_768_128 s0q6_896_120
theorem s0q6_0_512 : Interval s0Atlas 6 0 512 := concat s0q6_0_256 s0q6_256_256
theorem s0q6_512_504 : Interval s0Atlas 6 512 504 := concat s0q6_512_256 s0q6_768_248
theorem s0q6_0_1016 : Interval s0Atlas 6 0 1016 := concat s0q6_0_512 s0q6_512_504
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p7_0 : Interval s0Atlas 7 0 29 := block_range (n:=29) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0p8_0 : Interval s0Atlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem s0Complete : Complete s0Atlas := by
  intro k hk i hi
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s0p2_0 i (Nat.zero_le i) hi
  · exact s0p3_0 i (Nat.zero_le i) hi
  · exact s0q4_0_676 i (Nat.zero_le i) hi
  · exact s0q5_0_2921 i (Nat.zero_le i) hi
  · exact s0q6_0_1016 i (Nat.zero_le i) hi
  · exact s0p7_0 i (Nat.zero_le i) hi
  · exact s0p8_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Pair : properPairs (target s0Atlas) (asRow s0Pos) (asRow s0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Lower (allSlice : ∀ j : Fin 8, Slice true (roots s0Atlas) (target s0Atlas) (sliceDomain s0Atlas j.val) (sliceBound s0Atlas j.val)) :
    Lower true (roots s0Atlas) (target s0Atlas) 9 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨s0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip s0Atlas k i % 16 - 1, ht⟩
  exact frozen ready s0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 3, 11), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a0p2_0 : Interval s2a0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a0p3_0 : Interval s2a0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a0p4_0 : Interval s2a0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s2a0Complete : Complete s2a0Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s2a0p2_0 i (Nat.zero_le i) hi
  · exact s2a0p3_0 i (Nat.zero_le i) hi
  · exact s2a0p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a0Pair : properPairs (target s2a0Atlas) (asRow s2a0Pos) (asRow s2a0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a0Lower :
    Lower true (roots s2a0Atlas) (target s2a0Atlas) 5 := by
  have ready : Ready s2a0Atlas (asRow s2a0Pos) (asRow s2a0Neg) := by
    refine ⟨s2a0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s2a0Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 8, 12), (inputs.getD 3 zero, 2, 10), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a1p2_0 : Interval s2a1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a1p3_0 : Interval s2a1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a1p4_0 : Interval s2a1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s2a1Complete : Complete s2a1Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s2a1p2_0 i (Nat.zero_le i) hi
  · exact s2a1p3_0 i (Nat.zero_le i) hi
  · exact s2a1p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a1Pair : properPairs (target s2a1Atlas) (asRow s2a1Pos) (asRow s2a1Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a1Lower :
    Lower true (roots s2a1Atlas) (target s2a1Atlas) 5 := by
  have ready : Ready s2a1Atlas (asRow s2a1Pos) (asRow s2a1Neg) := by
    refine ⟨s2a1Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s2a1Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 0, 8), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a2p2_0 : Interval s2a2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a2p3_0 : Interval s2a2Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a2p4_0 : Interval s2a2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s2a2Complete : Complete s2a2Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s2a2p2_0 i (Nat.zero_le i) hi
  · exact s2a2p3_0 i (Nat.zero_le i) hi
  · exact s2a2p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a2Pair : properPairs (target s2a2Atlas) (asRow s2a2Pos) (asRow s2a2Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a2Lower :
    Lower true (roots s2a2Atlas) (target s2a2Atlas) 5 := by
  have ready : Ready s2a2Atlas (asRow s2a2Pos) (asRow s2a2Neg) := by
    refine ⟨s2a2Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s2a2Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 36, 38), (inputs.getD 2 zero, 1, 5), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a3p2_0 : Interval s2a3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a3p3_0 : Interval s2a3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a3p4_0 : Interval s2a3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s2a3Complete : Complete s2a3Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s2a3p2_0 i (Nat.zero_le i) hi
  · exact s2a3p3_0 i (Nat.zero_le i) hi
  · exact s2a3p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a3Pair : properPairs (target s2a3Atlas) (asRow s2a3Pos) (asRow s2a3Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a3Lower :
    Lower true (roots s2a3Atlas) (target s2a3Atlas) 5 := by
  have ready : Ready s2a3Atlas (asRow s2a3Pos) (asRow s2a3Neg) := by
    refine ⟨s2a3Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s2a3Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1), (inputs.getD 1 zero, 4, 6), (inputs.getD 2 zero, 2, 6), (inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a4p3_0 : Interval s2a4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem s2a4Complete : Complete s2a4Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s2a4p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a4Pair : properPairs (target s2a4Atlas) (asRow s2a4Pos) (asRow s2a4Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a4Lower :
    Lower true (roots s2a4Atlas) (target s2a4Atlas) 4 := by
  have ready : Ready s2a4Atlas (asRow s2a4Pos) (asRow s2a4Neg) := by
    refine ⟨s2a4Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s2a4Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 4, 12), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a5p3_0 : Interval s2a5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem s2a5Complete : Complete s2a5Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s2a5p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a5Pair : properPairs (target s2a5Atlas) (asRow s2a5Pos) (asRow s2a5Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2a5Lower :
    Lower true (roots s2a5Atlas) (target s2a5Atlas) 4 := by
  have ready : Ready s2a5Atlas (asRow s2a5Pos) (asRow s2a5Neg) := by
    refine ⟨s2a5Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s2a5Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p4_0 : Interval s2Atlas 4 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p4_64 : Interval s2Atlas 4 64 1 := block_range (n:=1) (by decide +kernel)
theorem s2q4_0_65 : Interval s2Atlas 4 0 65 := concat s2p4_0 s2p4_64
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p5_0 : Interval s2Atlas 5 0 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p5_64 : Interval s2Atlas 5 64 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p5_128 : Interval s2Atlas 5 128 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p5_192 : Interval s2Atlas 5 192 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
theorem s2q5_0_128 : Interval s2Atlas 5 0 128 := concat s2p5_0 s2p5_64
theorem s2q5_128_128 : Interval s2Atlas 5 128 128 := concat s2p5_128 s2p5_192
theorem s2q5_0_256 : Interval s2Atlas 5 0 256 := concat s2q5_0_128 s2q5_128_128
theorem s2q5_0_288 : Interval s2Atlas 5 0 288 := concat s2q5_0_256 s2p5_256
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p6_0 : Interval s2Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2p7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem s2Complete : Complete s2Atlas := by
  intro k hk i hi
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s2q4_0_65 i (Nat.zero_le i) hi
  · exact s2q5_0_288 i (Nat.zero_le i) hi
  · exact s2p6_0 i (Nat.zero_le i) hi
  · exact s2p7_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Pair : properPairs (target s2Atlas) (asRow s2Pos) (asRow s2Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Lower (allSlice : ∀ j : Fin 6, Slice true (roots s2Atlas) (target s2Atlas) (sliceDomain s2Atlas j.val) (sliceBound s2Atlas j.val)) :
    Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨s2Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip s2Atlas k i % 16 - 1, ht⟩
  exact frozen ready s2Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 1 zero, 8, 10), (inputs.getD 2 zero, 1, 5), (inputs.getD 3 zero, 2, 10), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4a0p3_0 : Interval s4a0Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4a0p4_0 : Interval s4a0Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4a0p5_0 : Interval s4a0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem s4a0Complete : Complete s4a0Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s4a0p3_0 i (Nat.zero_le i) hi
  · exact s4a0p4_0 i (Nat.zero_le i) hi
  · exact s4a0p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4a0Pair : properPairs (target s4a0Atlas) (asRow s4a0Pos) (asRow s4a0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4a0Lower :
    Lower true (roots s4a0Atlas) (target s4a0Atlas) 6 := by
  have ready : Ready s4a0Atlas (asRow s4a0Pos) (asRow s4a0Neg) := by
    refine ⟨s4a0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s4a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4p6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem s4Complete : Complete s4Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s4p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Pair : properPairs (target s4Atlas) (asRow s4Pos) (asRow s4Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Lower (allSlice : ∀ j : Fin 1, Slice true (roots s4Atlas) (target s4Atlas) (sliceDomain s4Atlas j.val) (sliceBound s4Atlas j.val)) :
    Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨s4Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip s4Atlas k i % 16 - 1, ht⟩
  exact frozen ready s4Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11), (inputs.getD 1 zero, 9, 11), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a0p2_0 : Interval s6a0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a0p3_0 : Interval s6a0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a0p4_0 : Interval s6a0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s6a0Complete : Complete s6a0Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s6a0p2_0 i (Nat.zero_le i) hi
  · exact s6a0p3_0 i (Nat.zero_le i) hi
  · exact s6a0p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a0Pair : properPairs (target s6a0Atlas) (asRow s6a0Pos) (asRow s6a0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a0Lower :
    Lower true (roots s6a0Atlas) (target s6a0Atlas) 5 := by
  have ready : Ready s6a0Atlas (asRow s6a0Pos) (asRow s6a0Neg) := by
    refine ⟨s6a0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s6a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a1p2_0 : Interval s6a1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a1p3_0 : Interval s6a1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a1p4_0 : Interval s6a1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s6a1Complete : Complete s6a1Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s6a1p2_0 i (Nat.zero_le i) hi
  · exact s6a1p3_0 i (Nat.zero_le i) hi
  · exact s6a1p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a1Pair : properPairs (target s6a1Atlas) (asRow s6a1Pos) (asRow s6a1Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a1Lower :
    Lower true (roots s6a1Atlas) (target s6a1Atlas) 5 := by
  have ready : Ready s6a1Atlas (asRow s6a1Pos) (asRow s6a1Neg) := by
    refine ⟨s6a1Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s6a1Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a2p3_0 : Interval s6a2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem s6a2Complete : Complete s6a2Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s6a2p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a2Pair : properPairs (target s6a2Atlas) (asRow s6a2Pos) (asRow s6a2Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a2Lower :
    Lower true (roots s6a2Atlas) (target s6a2Atlas) 4 := by
  have ready : Ready s6a2Atlas (asRow s6a2Pos) (asRow s6a2Neg) := by
    refine ⟨s6a2Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s6a2Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a3p3_0 : Interval s6a3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem s6a3Complete : Complete s6a3Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s6a3p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a3Pair : properPairs (target s6a3Atlas) (asRow s6a3Pos) (asRow s6a3Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6a3Lower :
    Lower true (roots s6a3Atlas) (target s6a3Atlas) 4 := by
  have ready : Ready s6a3Atlas (asRow s6a3Pos) (asRow s6a3Neg) := by
    refine ⟨s6a3Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s6a3Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5), (inputs.getD 2 zero, 1, 5), (inputs.getD 4 zero, 4, 20), (inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6p4_0 : Interval s6Atlas 4 0 22 := block_range (n:=22) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6p5_0 : Interval s6Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6p6_0 : Interval s6Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem s6Complete : Complete s6Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s6p4_0 i (Nat.zero_le i) hi
  · exact s6p5_0 i (Nat.zero_le i) hi
  · exact s6p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Pair : properPairs (target s6Atlas) (asRow s6Pos) (asRow s6Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Lower (allSlice : ∀ j : Fin 5, Slice true (roots s6Atlas) (target s6Atlas) (sliceDomain s6Atlas j.val) (sliceBound s6Atlas j.val)) :
    Lower true (roots s6Atlas) (target s6Atlas) 7 := by
  have ready : Ready s6Atlas (asRow s6Pos) (asRow s6Neg) := by
    refine ⟨s6Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip s6Atlas k i % 16 - 1, ht⟩
  exact frozen ready s6Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13), (inputs.getD 2 zero, 9, 13), (inputs.getD 3 zero, 5, 13), (inputs.getD 4 zero, 5, 21), (inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a0p2_0 : Interval s8a0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a0p3_0 : Interval s8a0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a0p4_0 : Interval s8a0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s8a0Complete : Complete s8a0Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s8a0p2_0 i (Nat.zero_le i) hi
  · exact s8a0p3_0 i (Nat.zero_le i) hi
  · exact s8a0p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a0Pair : properPairs (target s8a0Atlas) (asRow s8a0Pos) (asRow s8a0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a0Lower :
    Lower true (roots s8a0Atlas) (target s8a0Atlas) 5 := by
  have ready : Ready s8a0Atlas (asRow s8a0Pos) (asRow s8a0Neg) := by
    refine ⟨s8a0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s8a0Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a1p2_0 : Interval s8a1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a1p3_0 : Interval s8a1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a1p4_0 : Interval s8a1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s8a1Complete : Complete s8a1Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s8a1p2_0 i (Nat.zero_le i) hi
  · exact s8a1p3_0 i (Nat.zero_le i) hi
  · exact s8a1p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a1Pair : properPairs (target s8a1Atlas) (asRow s8a1Pos) (asRow s8a1Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a1Lower :
    Lower true (roots s8a1Atlas) (target s8a1Atlas) 5 := by
  have ready : Ready s8a1Atlas (asRow s8a1Pos) (asRow s8a1Neg) := by
    refine ⟨s8a1Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s8a1Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9), (inputs.getD 1 zero, 0, 2), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a3p3_0 : Interval s8a3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem s8a3Complete : Complete s8a3Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s8a3p3_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a3Pair : properPairs (target s8a3Atlas) (asRow s8a3Pos) (asRow s8a3Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8a3Lower :
    Lower true (roots s8a3Atlas) (target s8a3Atlas) 4 := by
  have ready : Ready s8a3Atlas (asRow s8a3Pos) (asRow s8a3Neg) := by
    refine ⟨s8a3Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s8a3Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8p4_0 : Interval s8Atlas 4 0 22 := block_range (n:=22) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8p5_0 : Interval s8Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8p6_0 : Interval s8Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem s8Complete : Complete s8Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s8p4_0 i (Nat.zero_le i) hi
  · exact s8p5_0 i (Nat.zero_le i) hi
  · exact s8p6_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Pair : properPairs (target s8Atlas) (asRow s8Pos) (asRow s8Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Lower (allSlice : ∀ j : Fin 5, Slice true (roots s8Atlas) (target s8Atlas) (sliceDomain s8Atlas j.val) (sliceBound s8Atlas j.val)) :
    Lower true (roots s8Atlas) (target s8Atlas) 7 := by
  have ready : Ready s8Atlas (asRow s8Pos) (asRow s8Neg) := by
    refine ⟨s8Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip s8Atlas k i % 16 - 1, ht⟩
  exact frozen ready s8Complete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3), (inputs.getD 1 zero, 1, 3), (inputs.getD 3 zero, 1, 9), (inputs.getD 4 zero, 1, 17), (inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10a0p2_0 : Interval s10a0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10a0p3_0 : Interval s10a0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10a0p4_0 : Interval s10a0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem s10a0Complete : Complete s10a0Atlas := by
  intro k hk i hi
  change k ≤ 4 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s10a0p2_0 i (Nat.zero_le i) hi
  · exact s10a0p3_0 i (Nat.zero_le i) hi
  · exact s10a0p4_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10a0Pair : properPairs (target s10a0Atlas) (asRow s10a0Pos) (asRow s10a0Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10a0Lower :
    Lower true (roots s10a0Atlas) (target s10a0Atlas) 5 := by
  have ready : Ready s10a0Atlas (asRow s10a0Pos) (asRow s10a0Neg) := by
    refine ⟨s10a0Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact False.elim (Nat.not_lt_zero _ ht)
  exact frozen ready s10a0Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18), (inputs.getD 2 zero, 16, 20), (inputs.getD 4 zero, 2, 18), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10p5_0 : Interval s10Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem s10Complete : Complete s10Atlas := by
  intro k hk i hi
  change k ≤ 5 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact s10p5_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Pair : properPairs (target s10Atlas) (asRow s10Pos) (asRow s10Neg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Lower (allSlice : ∀ j : Fin 1, Slice true (roots s10Atlas) (target s10Atlas) (sliceDomain s10Atlas j.val) (sliceBound s10Atlas j.val)) :
    Lower true (roots s10Atlas) (target s10Atlas) 6 := by
  have ready : Ready s10Atlas (asRow s10Pos) (asRow s10Neg) := by
    refine ⟨s10Pair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip s10Atlas k i % 16 - 1, ht⟩
  exact frozen ready s10Complete (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26), (inputs.getD 2 zero, 24, 28), (inputs.getD 3 zero, 18, 26), (inputs.getD 4 zero, 10, 26), (inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp5_0 : Interval mainAtlas 5 0 36 := block_range (n:=36) (by decide +kernel)
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
theorem mainp6_384 : Interval mainAtlas 6 384 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_448 : Interval mainAtlas 6 448 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_512 : Interval mainAtlas 6 512 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_576 : Interval mainAtlas 6 576 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_640 : Interval mainAtlas 6 640 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_704 : Interval mainAtlas 6 704 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_768 : Interval mainAtlas 6 768 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_832 : Interval mainAtlas 6 832 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_896 : Interval mainAtlas 6 896 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_960 : Interval mainAtlas 6 960 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_1024 : Interval mainAtlas 6 1024 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_1088 : Interval mainAtlas 6 1088 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_1152 : Interval mainAtlas 6 1152 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_1216 : Interval mainAtlas 6 1216 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp6_1280 : Interval mainAtlas 6 1280 44 := block_range (n:=44) (by decide +kernel)
theorem mainq6_0_128 : Interval mainAtlas 6 0 128 := concat mainp6_0 mainp6_64
theorem mainq6_128_128 : Interval mainAtlas 6 128 128 := concat mainp6_128 mainp6_192
theorem mainq6_256_128 : Interval mainAtlas 6 256 128 := concat mainp6_256 mainp6_320
theorem mainq6_384_128 : Interval mainAtlas 6 384 128 := concat mainp6_384 mainp6_448
theorem mainq6_512_128 : Interval mainAtlas 6 512 128 := concat mainp6_512 mainp6_576
theorem mainq6_640_128 : Interval mainAtlas 6 640 128 := concat mainp6_640 mainp6_704
theorem mainq6_768_128 : Interval mainAtlas 6 768 128 := concat mainp6_768 mainp6_832
theorem mainq6_896_128 : Interval mainAtlas 6 896 128 := concat mainp6_896 mainp6_960
theorem mainq6_1024_128 : Interval mainAtlas 6 1024 128 := concat mainp6_1024 mainp6_1088
theorem mainq6_1152_128 : Interval mainAtlas 6 1152 128 := concat mainp6_1152 mainp6_1216
theorem mainq6_0_256 : Interval mainAtlas 6 0 256 := concat mainq6_0_128 mainq6_128_128
theorem mainq6_256_256 : Interval mainAtlas 6 256 256 := concat mainq6_256_128 mainq6_384_128
theorem mainq6_512_256 : Interval mainAtlas 6 512 256 := concat mainq6_512_128 mainq6_640_128
theorem mainq6_768_256 : Interval mainAtlas 6 768 256 := concat mainq6_768_128 mainq6_896_128
theorem mainq6_1024_256 : Interval mainAtlas 6 1024 256 := concat mainq6_1024_128 mainq6_1152_128
theorem mainq6_0_512 : Interval mainAtlas 6 0 512 := concat mainq6_0_256 mainq6_256_256
theorem mainq6_512_512 : Interval mainAtlas 6 512 512 := concat mainq6_512_256 mainq6_768_256
theorem mainq6_1024_300 : Interval mainAtlas 6 1024 300 := concat mainq6_1024_256 mainp6_1280
theorem mainq6_0_1024 : Interval mainAtlas 6 0 1024 := concat mainq6_0_512 mainq6_512_512
theorem mainq6_0_1324 : Interval mainAtlas 6 0 1324 := concat mainq6_0_1024 mainq6_1024_300
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
theorem mainp7_3264 : Interval mainAtlas 7 3264 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3328 : Interval mainAtlas 7 3328 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3392 : Interval mainAtlas 7 3392 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3456 : Interval mainAtlas 7 3456 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3520 : Interval mainAtlas 7 3520 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3584 : Interval mainAtlas 7 3584 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3648 : Interval mainAtlas 7 3648 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3712 : Interval mainAtlas 7 3712 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3776 : Interval mainAtlas 7 3776 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3840 : Interval mainAtlas 7 3840 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3904 : Interval mainAtlas 7 3904 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_3968 : Interval mainAtlas 7 3968 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4032 : Interval mainAtlas 7 4032 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4096 : Interval mainAtlas 7 4096 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4160 : Interval mainAtlas 7 4160 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4224 : Interval mainAtlas 7 4224 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4288 : Interval mainAtlas 7 4288 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4352 : Interval mainAtlas 7 4352 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4416 : Interval mainAtlas 7 4416 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4480 : Interval mainAtlas 7 4480 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4544 : Interval mainAtlas 7 4544 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4608 : Interval mainAtlas 7 4608 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4672 : Interval mainAtlas 7 4672 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4736 : Interval mainAtlas 7 4736 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4800 : Interval mainAtlas 7 4800 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4864 : Interval mainAtlas 7 4864 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4928 : Interval mainAtlas 7 4928 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_4992 : Interval mainAtlas 7 4992 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5056 : Interval mainAtlas 7 5056 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5120 : Interval mainAtlas 7 5120 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5184 : Interval mainAtlas 7 5184 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5248 : Interval mainAtlas 7 5248 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5312 : Interval mainAtlas 7 5312 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5376 : Interval mainAtlas 7 5376 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5440 : Interval mainAtlas 7 5440 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5504 : Interval mainAtlas 7 5504 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5568 : Interval mainAtlas 7 5568 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5632 : Interval mainAtlas 7 5632 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5696 : Interval mainAtlas 7 5696 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5760 : Interval mainAtlas 7 5760 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5824 : Interval mainAtlas 7 5824 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5888 : Interval mainAtlas 7 5888 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_5952 : Interval mainAtlas 7 5952 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_6016 : Interval mainAtlas 7 6016 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_6080 : Interval mainAtlas 7 6080 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_6144 : Interval mainAtlas 7 6144 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_6208 : Interval mainAtlas 7 6208 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_6272 : Interval mainAtlas 7 6272 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp7_6336 : Interval mainAtlas 7 6336 49 := block_range (n:=49) (by decide +kernel)
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
theorem mainq7_3200_128 : Interval mainAtlas 7 3200 128 := concat mainp7_3200 mainp7_3264
theorem mainq7_3328_128 : Interval mainAtlas 7 3328 128 := concat mainp7_3328 mainp7_3392
theorem mainq7_3456_128 : Interval mainAtlas 7 3456 128 := concat mainp7_3456 mainp7_3520
theorem mainq7_3584_128 : Interval mainAtlas 7 3584 128 := concat mainp7_3584 mainp7_3648
theorem mainq7_3712_128 : Interval mainAtlas 7 3712 128 := concat mainp7_3712 mainp7_3776
theorem mainq7_3840_128 : Interval mainAtlas 7 3840 128 := concat mainp7_3840 mainp7_3904
theorem mainq7_3968_128 : Interval mainAtlas 7 3968 128 := concat mainp7_3968 mainp7_4032
theorem mainq7_4096_128 : Interval mainAtlas 7 4096 128 := concat mainp7_4096 mainp7_4160
theorem mainq7_4224_128 : Interval mainAtlas 7 4224 128 := concat mainp7_4224 mainp7_4288
theorem mainq7_4352_128 : Interval mainAtlas 7 4352 128 := concat mainp7_4352 mainp7_4416
theorem mainq7_4480_128 : Interval mainAtlas 7 4480 128 := concat mainp7_4480 mainp7_4544
theorem mainq7_4608_128 : Interval mainAtlas 7 4608 128 := concat mainp7_4608 mainp7_4672
theorem mainq7_4736_128 : Interval mainAtlas 7 4736 128 := concat mainp7_4736 mainp7_4800
theorem mainq7_4864_128 : Interval mainAtlas 7 4864 128 := concat mainp7_4864 mainp7_4928
theorem mainq7_4992_128 : Interval mainAtlas 7 4992 128 := concat mainp7_4992 mainp7_5056
theorem mainq7_5120_128 : Interval mainAtlas 7 5120 128 := concat mainp7_5120 mainp7_5184
theorem mainq7_5248_128 : Interval mainAtlas 7 5248 128 := concat mainp7_5248 mainp7_5312
theorem mainq7_5376_128 : Interval mainAtlas 7 5376 128 := concat mainp7_5376 mainp7_5440
theorem mainq7_5504_128 : Interval mainAtlas 7 5504 128 := concat mainp7_5504 mainp7_5568
theorem mainq7_5632_128 : Interval mainAtlas 7 5632 128 := concat mainp7_5632 mainp7_5696
theorem mainq7_5760_128 : Interval mainAtlas 7 5760 128 := concat mainp7_5760 mainp7_5824
theorem mainq7_5888_128 : Interval mainAtlas 7 5888 128 := concat mainp7_5888 mainp7_5952
theorem mainq7_6016_128 : Interval mainAtlas 7 6016 128 := concat mainp7_6016 mainp7_6080
theorem mainq7_6144_128 : Interval mainAtlas 7 6144 128 := concat mainp7_6144 mainp7_6208
theorem mainq7_6272_113 : Interval mainAtlas 7 6272 113 := concat mainp7_6272 mainp7_6336
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
theorem mainq7_3072_256 : Interval mainAtlas 7 3072 256 := concat mainq7_3072_128 mainq7_3200_128
theorem mainq7_3328_256 : Interval mainAtlas 7 3328 256 := concat mainq7_3328_128 mainq7_3456_128
theorem mainq7_3584_256 : Interval mainAtlas 7 3584 256 := concat mainq7_3584_128 mainq7_3712_128
theorem mainq7_3840_256 : Interval mainAtlas 7 3840 256 := concat mainq7_3840_128 mainq7_3968_128
theorem mainq7_4096_256 : Interval mainAtlas 7 4096 256 := concat mainq7_4096_128 mainq7_4224_128
theorem mainq7_4352_256 : Interval mainAtlas 7 4352 256 := concat mainq7_4352_128 mainq7_4480_128
theorem mainq7_4608_256 : Interval mainAtlas 7 4608 256 := concat mainq7_4608_128 mainq7_4736_128
theorem mainq7_4864_256 : Interval mainAtlas 7 4864 256 := concat mainq7_4864_128 mainq7_4992_128
theorem mainq7_5120_256 : Interval mainAtlas 7 5120 256 := concat mainq7_5120_128 mainq7_5248_128
theorem mainq7_5376_256 : Interval mainAtlas 7 5376 256 := concat mainq7_5376_128 mainq7_5504_128
theorem mainq7_5632_256 : Interval mainAtlas 7 5632 256 := concat mainq7_5632_128 mainq7_5760_128
theorem mainq7_5888_256 : Interval mainAtlas 7 5888 256 := concat mainq7_5888_128 mainq7_6016_128
theorem mainq7_6144_241 : Interval mainAtlas 7 6144 241 := concat mainq7_6144_128 mainq7_6272_113
theorem mainq7_0_512 : Interval mainAtlas 7 0 512 := concat mainq7_0_256 mainq7_256_256
theorem mainq7_512_512 : Interval mainAtlas 7 512 512 := concat mainq7_512_256 mainq7_768_256
theorem mainq7_1024_512 : Interval mainAtlas 7 1024 512 := concat mainq7_1024_256 mainq7_1280_256
theorem mainq7_1536_512 : Interval mainAtlas 7 1536 512 := concat mainq7_1536_256 mainq7_1792_256
theorem mainq7_2048_512 : Interval mainAtlas 7 2048 512 := concat mainq7_2048_256 mainq7_2304_256
theorem mainq7_2560_512 : Interval mainAtlas 7 2560 512 := concat mainq7_2560_256 mainq7_2816_256
theorem mainq7_3072_512 : Interval mainAtlas 7 3072 512 := concat mainq7_3072_256 mainq7_3328_256
theorem mainq7_3584_512 : Interval mainAtlas 7 3584 512 := concat mainq7_3584_256 mainq7_3840_256
theorem mainq7_4096_512 : Interval mainAtlas 7 4096 512 := concat mainq7_4096_256 mainq7_4352_256
theorem mainq7_4608_512 : Interval mainAtlas 7 4608 512 := concat mainq7_4608_256 mainq7_4864_256
theorem mainq7_5120_512 : Interval mainAtlas 7 5120 512 := concat mainq7_5120_256 mainq7_5376_256
theorem mainq7_5632_512 : Interval mainAtlas 7 5632 512 := concat mainq7_5632_256 mainq7_5888_256
theorem mainq7_0_1024 : Interval mainAtlas 7 0 1024 := concat mainq7_0_512 mainq7_512_512
theorem mainq7_1024_1024 : Interval mainAtlas 7 1024 1024 := concat mainq7_1024_512 mainq7_1536_512
theorem mainq7_2048_1024 : Interval mainAtlas 7 2048 1024 := concat mainq7_2048_512 mainq7_2560_512
theorem mainq7_3072_1024 : Interval mainAtlas 7 3072 1024 := concat mainq7_3072_512 mainq7_3584_512
theorem mainq7_4096_1024 : Interval mainAtlas 7 4096 1024 := concat mainq7_4096_512 mainq7_4608_512
theorem mainq7_5120_1024 : Interval mainAtlas 7 5120 1024 := concat mainq7_5120_512 mainq7_5632_512
theorem mainq7_0_2048 : Interval mainAtlas 7 0 2048 := concat mainq7_0_1024 mainq7_1024_1024
theorem mainq7_2048_2048 : Interval mainAtlas 7 2048 2048 := concat mainq7_2048_1024 mainq7_3072_1024
theorem mainq7_4096_2048 : Interval mainAtlas 7 4096 2048 := concat mainq7_4096_1024 mainq7_5120_1024
theorem mainq7_0_4096 : Interval mainAtlas 7 0 4096 := concat mainq7_0_2048 mainq7_2048_2048
theorem mainq7_4096_2289 : Interval mainAtlas 7 4096 2289 := concat mainq7_4096_2048 mainq7_6144_241
theorem mainq7_0_6385 : Interval mainAtlas 7 0 6385 := concat mainq7_0_4096 mainq7_4096_2289
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
theorem mainp8_896 : Interval mainAtlas 8 896 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_960 : Interval mainAtlas 8 960 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1024 : Interval mainAtlas 8 1024 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1088 : Interval mainAtlas 8 1088 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1152 : Interval mainAtlas 8 1152 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1216 : Interval mainAtlas 8 1216 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1280 : Interval mainAtlas 8 1280 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1344 : Interval mainAtlas 8 1344 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1408 : Interval mainAtlas 8 1408 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1472 : Interval mainAtlas 8 1472 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1536 : Interval mainAtlas 8 1536 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1600 : Interval mainAtlas 8 1600 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1664 : Interval mainAtlas 8 1664 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1728 : Interval mainAtlas 8 1728 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1792 : Interval mainAtlas 8 1792 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1856 : Interval mainAtlas 8 1856 64 := block_range (n:=64) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp8_1920 : Interval mainAtlas 8 1920 36 := block_range (n:=36) (by decide +kernel)
theorem mainq8_0_128 : Interval mainAtlas 8 0 128 := concat mainp8_0 mainp8_64
theorem mainq8_128_128 : Interval mainAtlas 8 128 128 := concat mainp8_128 mainp8_192
theorem mainq8_256_128 : Interval mainAtlas 8 256 128 := concat mainp8_256 mainp8_320
theorem mainq8_384_128 : Interval mainAtlas 8 384 128 := concat mainp8_384 mainp8_448
theorem mainq8_512_128 : Interval mainAtlas 8 512 128 := concat mainp8_512 mainp8_576
theorem mainq8_640_128 : Interval mainAtlas 8 640 128 := concat mainp8_640 mainp8_704
theorem mainq8_768_128 : Interval mainAtlas 8 768 128 := concat mainp8_768 mainp8_832
theorem mainq8_896_128 : Interval mainAtlas 8 896 128 := concat mainp8_896 mainp8_960
theorem mainq8_1024_128 : Interval mainAtlas 8 1024 128 := concat mainp8_1024 mainp8_1088
theorem mainq8_1152_128 : Interval mainAtlas 8 1152 128 := concat mainp8_1152 mainp8_1216
theorem mainq8_1280_128 : Interval mainAtlas 8 1280 128 := concat mainp8_1280 mainp8_1344
theorem mainq8_1408_128 : Interval mainAtlas 8 1408 128 := concat mainp8_1408 mainp8_1472
theorem mainq8_1536_128 : Interval mainAtlas 8 1536 128 := concat mainp8_1536 mainp8_1600
theorem mainq8_1664_128 : Interval mainAtlas 8 1664 128 := concat mainp8_1664 mainp8_1728
theorem mainq8_1792_128 : Interval mainAtlas 8 1792 128 := concat mainp8_1792 mainp8_1856
theorem mainq8_0_256 : Interval mainAtlas 8 0 256 := concat mainq8_0_128 mainq8_128_128
theorem mainq8_256_256 : Interval mainAtlas 8 256 256 := concat mainq8_256_128 mainq8_384_128
theorem mainq8_512_256 : Interval mainAtlas 8 512 256 := concat mainq8_512_128 mainq8_640_128
theorem mainq8_768_256 : Interval mainAtlas 8 768 256 := concat mainq8_768_128 mainq8_896_128
theorem mainq8_1024_256 : Interval mainAtlas 8 1024 256 := concat mainq8_1024_128 mainq8_1152_128
theorem mainq8_1280_256 : Interval mainAtlas 8 1280 256 := concat mainq8_1280_128 mainq8_1408_128
theorem mainq8_1536_256 : Interval mainAtlas 8 1536 256 := concat mainq8_1536_128 mainq8_1664_128
theorem mainq8_1792_164 : Interval mainAtlas 8 1792 164 := concat mainq8_1792_128 mainp8_1920
theorem mainq8_0_512 : Interval mainAtlas 8 0 512 := concat mainq8_0_256 mainq8_256_256
theorem mainq8_512_512 : Interval mainAtlas 8 512 512 := concat mainq8_512_256 mainq8_768_256
theorem mainq8_1024_512 : Interval mainAtlas 8 1024 512 := concat mainq8_1024_256 mainq8_1280_256
theorem mainq8_1536_420 : Interval mainAtlas 8 1536 420 := concat mainq8_1536_256 mainq8_1792_164
theorem mainq8_0_1024 : Interval mainAtlas 8 0 1024 := concat mainq8_0_512 mainq8_512_512
theorem mainq8_1024_932 : Interval mainAtlas 8 1024 932 := concat mainq8_1024_512 mainq8_1536_420
theorem mainq8_0_1956 : Interval mainAtlas 8 0 1956 := concat mainq8_0_1024 mainq8_1024_932
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainp9_0 : Interval mainAtlas 9 0 60 := block_range (n:=60) (by decide +kernel)
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
  · exact mainq6_0_1324 i (Nat.zero_le i) hi
  · exact mainq7_0_6385 i (Nat.zero_le i) hi
  · exact mainq8_0_1956 i (Nat.zero_le i) hi
  · exact mainp9_0 i (Nat.zero_le i) hi
  · exact mainp10_0 i (Nat.zero_le i) hi
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainPair : properPairs (target mainAtlas) (asRow mainPos) (asRow mainNeg) := by
  unfold properPairs
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mainLower (allSlice : ∀ j : Fin 12, Slice true (roots mainAtlas) (target mainAtlas) (sliceDomain mainAtlas j.val) (sliceBound mainAtlas j.val)) :
    Lower true (roots mainAtlas) (target mainAtlas) 11 := by
  have ready : Ready mainAtlas (asRow mainPos) (asRow mainNeg) := by
    refine ⟨mainPair, raw_faithful _ _ _, ?_⟩
    · intro k i hi hn ht
      exact allSlice ⟨tip mainAtlas k i % 16 - 1, ht⟩
  exact frozen ready mainComplete (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7), (inputs.getD 1 zero, 5, 7), (inputs.getD 2 zero, 3, 7), (inputs.getD 3 zero, 3, 11), (inputs.getD 4 zero, 5, 21), (inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem s0Slices : ∀ a : Fin 8, Slice true (roots s0Atlas) (target s0Atlas) (sliceDomain s0Atlas a.val) (sliceBound s0Atlas a.val) := by
  intro a
  fin_cases a
  · exact slice_correct (ms:=fixRows 16 8) (base:=roots s0a0Atlas) (G:=target s0a0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a0Lower
  · exact slice_correct (ms:=fixRows 16 1) (base:=roots s0a1Atlas) (G:=target s0a1Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a1Lower
  · exact slice_correct (ms:=fixRows 16 2) (base:=roots s0a2Atlas) (G:=target s0a2Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a2Lower
  · exact slice_correct (ms:=fixRows 20 0) (base:=roots s0a3Atlas) (G:=target s0a3Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a3Lower
  · exact slice_correct (ms:=fixRows 24 0) (base:=roots s0a4Atlas) (G:=target s0a4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a4Lower
  · exact slice_correct (ms:=fixRows 48 0) (base:=roots s0a5Atlas) (G:=target s0a5Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a5Lower
  · exact slice_correct (ms:=fixRows 16 4) (base:=roots s0a6Atlas) (G:=target s0a6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a6Lower
  · exact slice_correct (ms:=fixRows 16 32) (base:=roots s0a7Atlas) (G:=target s0a7Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a7Lower

theorem s2Slices : ∀ a : Fin 6, Slice true (roots s2Atlas) (target s2Atlas) (sliceDomain s2Atlas a.val) (sliceBound s2Atlas a.val) := by
  intro a
  fin_cases a
  · exact slice_correct (ms:=fixRows 17 0) (base:=roots s2a0Atlas) (G:=target s2a0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s2a0Lower
  · exact slice_correct (ms:=fixRows 16 2) (base:=roots s2a1Atlas) (G:=target s2a1Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s2a1Lower
  · exact slice_correct (ms:=fixRows 24 0) (base:=roots s2a2Atlas) (G:=target s2a2Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s2a2Lower
  · exact slice_correct (ms:=fixRows 16 32) (base:=roots s2a3Atlas) (G:=target s2a3Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s2a3Lower
  · exact slice_correct (ms:=fixRows 18 0) (base:=roots s2a4Atlas) (G:=target s2a4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s2a4Lower
  · exact slice_correct (ms:=fixRows 48 0) (base:=roots s2a5Atlas) (G:=target s2a5Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s2a5Lower

theorem s4Slices : ∀ a : Fin 1, Slice true (roots s4Atlas) (target s4Atlas) (sliceDomain s4Atlas a.val) (sliceBound s4Atlas a.val) := by
  intro a
  fin_cases a
  · exact slice_correct (ms:=fixRows 4 32) (base:=roots s4a0Atlas) (G:=target s4a0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s4a0Lower

theorem s6Slices : ∀ a : Fin 5, Slice true (roots s6Atlas) (target s6Atlas) (sliceDomain s6Atlas a.val) (sliceBound s6Atlas a.val) := by
  intro a
  fin_cases a
  · exact slice_correct (ms:=fixRows 34 0) (base:=roots s6a0Atlas) (G:=target s6a0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s6a0Lower
  · exact slice_correct (ms:=fixRows 2 32) (base:=roots s6a1Atlas) (G:=target s6a1Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s6a1Lower
  · exact slice_correct (ms:=fixRows 34 4) (base:=roots s6a2Atlas) (G:=target s6a2Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s6a2Lower
  · exact slice_correct (ms:=fixRows 2 8) (base:=roots s6a3Atlas) (G:=target s6a3Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s6a3Lower
  · exact slice_correct (ms:=fixRows 2 16) (base:=roots s2a4Atlas) (G:=target s2a4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s2a4Lower

theorem s8Slices : ∀ a : Fin 5, Slice true (roots s8Atlas) (target s8Atlas) (sliceDomain s8Atlas a.val) (sliceBound s8Atlas a.val) := by
  intro a
  fin_cases a
  · exact slice_correct (ms:=fixRows 36 0) (base:=roots s8a0Atlas) (G:=target s8a0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s8a0Lower
  · exact slice_correct (ms:=fixRows 4 32) (base:=roots s8a1Atlas) (G:=target s8a1Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s8a1Lower
  · exact slice_correct (ms:=fixRows 38 0) (base:=roots s6a2Atlas) (G:=target s6a2Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s6a2Lower
  · exact slice_correct (ms:=fixRows 12 0) (base:=roots s8a3Atlas) (G:=target s8a3Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s8a3Lower
  · exact slice_correct (ms:=fixRows 20 0) (base:=roots s0a6Atlas) (G:=target s0a6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s0a6Lower

theorem s10Slices : ∀ a : Fin 1, Slice true (roots s10Atlas) (target s10Atlas) (sliceDomain s10Atlas a.val) (sliceBound s10Atlas a.val) := by
  intro a
  fin_cases a
  · exact slice_correct (ms:=fixRows 1 8) (base:=roots s10a0Atlas) (G:=target s10a0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) s10a0Lower

def dualMoves : List Move := [swapRows 50, swapRows 84] ++ (List.range 6).map (fun j =>
  let x := inputs.getD j zero
  (neg x, x, Fin.ofNat 64 (1 <<< j)))

theorem allSlices : ∀ j : Fin 12, Slice true (roots mainAtlas) (target mainAtlas) (sliceDomain mainAtlas j.val) (sliceBound mainAtlas j.val) := by
  intro j
  fin_cases j
  · exact slice_correct (ms:=fixRows 16 0) (base:=roots s0Atlas) (G:=target s0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s0Lower s0Slices)
  · exact sliceDual (ms:=(fixRows 16 0 ++ dualMoves)) (base:=roots s0Atlas) (G:=target s0Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s0Lower s0Slices)
  · exact slice_correct (ms:=fixRows 0 16) (base:=roots s2Atlas) (G:=target s2Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s2Lower s2Slices)
  · exact sliceDual (ms:=(fixRows 0 16 ++ dualMoves)) (base:=roots s2Atlas) (G:=target s2Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s2Lower s2Slices)
  · exact slice_correct (ms:=fixRows 4 0) (base:=roots s4Atlas) (G:=target s4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s4Lower s4Slices)
  · exact sliceDual (ms:=(fixRows 4 0 ++ dualMoves)) (base:=roots s4Atlas) (G:=target s4Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s4Lower s4Slices)
  · exact slice_correct (ms:=fixRows 2 0) (base:=roots s6Atlas) (G:=target s6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s6Lower s6Slices)
  · exact sliceDual (ms:=(fixRows 2 0 ++ dualMoves)) (base:=roots s6Atlas) (G:=target s6Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s6Lower s6Slices)
  · exact slice_correct (ms:=fixRows 0 4) (base:=roots s8Atlas) (G:=target s8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s8Lower s8Slices)
  · exact sliceDual (ms:=(fixRows 0 4 ++ dualMoves)) (base:=roots s8Atlas) (G:=target s8Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s8Lower s8Slices)
  · exact slice_correct (ms:=fixRows 1 0) (base:=roots s10Atlas) (G:=target s10Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s10Lower s10Slices)
  · exact sliceDual (ms:=(fixRows 1 0 ++ dualMoves)) (base:=roots s10Atlas) (G:=target s10Atlas) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (s10Lower s10Slices)

def fullRoots : List Sig := roots mainAtlas
def fullWord : Sig := target mainAtlas
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4238387328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  unfold PEqualNP.Outside.L_meta_45534.Model.Repr at out
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
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [11, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [13, 0]⟩, ⟨.or, [14, 10]⟩, ⟨.and, [15, 8]⟩, ⟨.or, [16, 12]⟩], 17⟩

theorem witness_shape : MetaComplexity.Monotone2 witness := by
  simp [MetaComplexity.Monotone2, witness]

theorem witness_eval : ∀ x, witness.eval (List.ofFn x) = posted x := by decide +kernel

end PEqualNP.Outside.L_meta_45534

open PEqualNP.Outside.L_meta_45534 PEqualNP.Outside.L_meta_45534.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_45534 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4238387328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4238387328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsize, heval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have cut : C.gates.countP (fun g => !isNot g) < C.gates.length := by
      rw [List.countP_eq_length_filter]
      exact (List.length_filter_lt_length_iff_exists (p := fun g => !isNot g)).mpr
        ⟨g, mem, by simp [isNot, op]⟩
    have hb := binaryLower (mainLower allSlices) C.gates C.output hfan heval
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

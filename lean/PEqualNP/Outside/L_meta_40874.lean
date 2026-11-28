import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40874.Model
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

end PEqualNP.Outside.L_meta_40874.Model
namespace PEqualNP.Outside.L_meta_40874
open PEqualNP.Outside.L_meta_40874.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B1

namespace B2
def R : List Sig := vars 15
def T : Sig := 0xa880a880a880a880
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 1) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 6, 7)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B1.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 6, 7)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B2

namespace B3
def R : List Sig := vars 39
def T : Sig := 0xc8c8c8c880808080
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 83, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B2.low
end B3

namespace B4
def R : List Sig := vars 15
def T : Sig := 0xe888e888e888e888
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 5, 13)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 5, 13)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B4

namespace B5
def R : List Sig := vars 15
def T : Sig := 0xea80ea80ea80ea80
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B4.low
end B5

namespace B6
def R : List Sig := vars 26
def T : Sig := 0xffcccc00ffcccc00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B6

namespace B7
def R : List Sig := vars 31
def T : Sig := 0xeac8e8c0eac8e8c0
def P : Nat → Bits
  | 0 => ((0x1ffff8e383ffffc0 : BitVec 64) ++ (0xff07fe07f8fccf9f : BitVec 64))
  | 1 => ((0xe0ffff5ffc0fc7ff : BitVec 64) ++ (0xfff8fff8cf27f3eb : BitVec 64))
  | 2 => ((0xff03ff3ffff007ff : BitVec 64) ++ (0x1fff1ff837c73de4 : BitVec 64))
  | 3 => ((0xfffc00a3fffff800 : BitVec 64) ++ (0x1fffe0073bf83e17 : BitVec 64))
  | 4 => ((0xc3ffffffff : BitVec 64) ++ (0xe0000007c3ffc018 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0xc42891e480b2c9c8 : BitVec 64) ++ (0x27013211544c459f : BitVec 64))
  | 1 => ((0x424120a914054251 : BitVec 64) ++ (0x494844a28d2192a9 : BitVec 64))
  | 2 => ((0x881a4016a95004aa : BitVec 64) ++ (0x1292195572c62d40 : BitVec 64))
  | 3 => ((0x1290725b4e699030 : BitVec 64) ++ (0x1ce48066abb03a16 : BitVec 64))
  | 4 => ((0x1ce3841ff38e273c : BitVec 64) ++ (0x80c01187fbffc000 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
theorem s0 : Slice true R T 0xa0a0a0a0a0a0a0a 4 :=
  slice_correct (ms := fixRows 4 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xff000000ff00 4 :=
  slice_correct (ms := fixRows 16 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def v0 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3, w4]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 10, 11), (0xcccccccccccccccc, 4, 6), (0xf0f0f0f0f0f0f0f0, 2, 6), (0xff00ff00ff00ff00, 3, 11), (0xffff0000ffff0000, 3, 19)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B7

namespace B8
def R : List Sig := vars 47
def T : Sig := 0xeac8eac8ea80ea80
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 84, swapRows 50, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B7.low
end B8

namespace B9
def R : List Sig := vars 23
def T : Sig := 0xeaea8080eaea8080
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67, swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B4.low
end B9

namespace B10
def R : List Sig := vars 55
def T : Sig := 0xeaeac8c8eaea8080
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 84, swapRows 67, swapRows 66, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B7.low
end B10

namespace B11
def R : List Sig := vars 15
def T : Sig := 0xe8a8e8a8e8a8e8a8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 6, 14)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 6, 14)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B11

namespace B12
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
end B12

namespace B13
def R : List Sig := vars 31
def T : Sig := 0xeaa8e8a8eaa8e8a8
theorem low : Lower true R T 7 := by
  exact lower_cubes_two (u := true) (j := 4) (r := 9) (s := 25) (L := 5)
    (z0 := 16) (o0 := 0) (z1 := 0) (o1 := 16)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide)) (proper_of _ (by decide)) (proper_of _ (by decide))
    (lower_weaken B11.low (by decide))
    (lower_weaken B12.low (by decide))
end B13

namespace B14
def R : List Sig := vars 59
def T : Sig := 0xeeaaaa88eeaaaa00
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 84, swapRows 66, swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B13.low
end B14

namespace B15
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
end B15

namespace B16
def R : List Sig := vars 27
def T : Sig := 0xeeaaaa88eeaaaa88
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B15.low
end B16

namespace B17
def R : List Sig := vars 29
def T : Sig := 0xfaaaaa00faaaaa00
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 50, swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B11.low
end B17

namespace B18
def R : List Sig := vars 21
def T : Sig := 0xfafaa0a0fafaa0a0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B18

namespace B19
def R : List Sig := vars 37
def T : Sig := 0xfafafafaa0a0a0a0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 81]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B19

namespace B20
def R : List Sig := vars 15
def T : Sig := 0xeee8eee8eee8eee8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B20

namespace B21
def R : List Sig := vars 45
def T : Sig := 0xfafafafafaa0faa0
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 82, swapRows 33]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B20.low
end B21

namespace B22
def R : List Sig := vars 53
def T : Sig := 0xfafafafafafaa0a0
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67, swapRows 82, swapRows 33]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B20.low
end B22

namespace B23
def R : List Sig := vars 11
def T : Sig := 0x8800880088008800
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 10, 11), (0xcccccccccccccccc, 9, 11), (0xff00ff00ff00ff00, 3, 11)] (by decide +kernel)
end B23

namespace B24
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B24

namespace B25
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B25

namespace B26
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
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 0 w0 w1
def w5 := combineObserved 0 w0 w2
def w6 := combineObserved 0 w1 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w4, w5, w6, w3]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 2 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B23.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 4 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
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
end B26

namespace B27
def R : List Sig := vars 30
def T : Sig := 0xfcc0c000fcc0c000
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B26.low
end B27

namespace B28
def R : List Sig := vars 31
def T : Sig := 0xe888e880e888e880
theorem low : Lower true R T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 16 0) (raw := R)
    (T := T) (xs := [(0xffff0000ffff0000, 3, 19)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B26.low
  have he : (([(0xffff0000ffff0000, 3, 19)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B28

namespace B29
def R : List Sig := vars 62
def T : Sig := 0xfcc0c0c0fcc0c000
theorem low : Lower true R T 8 := by
  exact lower_map (ms := [swapRows 84, swapRows 66, swapRows 32]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B28.low
end B29

namespace B30
def R : List Sig := vars 22
def T : Sig := 0xfcfcc0c0fcfcc0c0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B30

namespace B31
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
theorem s0 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0xcccccccccccccccc 4 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[] ((((0x1442120181102 : Nat) >>> (((h / 8 + (((0xc189 : Nat) >>> ((h % 8) * 2)) &&& 3)) % 25) * 2)) &&& 3))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 3, 11)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B31

namespace B32
def R : List Sig := vars 30
def T : Sig := 0xfcc0c000fcc0c000
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B31.low
end B32

namespace B33
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
theorem s0 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[] ((((0x1442120181102 : Nat) >>> (((h / 8 + (((0xc189 : Nat) >>> ((h % 8) * 2)) &&& 3)) % 25) * 2)) &&& 3))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B33

namespace B34
def R : List Sig := vars 11
def T : Sig := 0xffeeffeeffeeffee
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
end B34

namespace B35
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
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 1 w2 w1
def w5 := combineObserved 1 w3 w1
def w6 := combineObserved 1 w3 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w4, w5, w6]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def w7 := combineObserved 1 w3 w0
def a0 : List Move := [swapRows 32]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v0 a0 a0ok
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w7, w5]
  (fun h => chooseRoute #[(usePool p2), (usePool p1)] #[r0] ((((0x408 : Nat) >>> ((h % 6) * 2)) &&& 3))) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
def p3 : Pool R T := prefixPool s3 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xfefefefefefefefe, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 2 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B34.low
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
end B35

namespace B36
def R : List Sig := vars 23
def T : Sig := 0xfefee8e8fefee8e8
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B33.low
end B36

namespace B37
def R : List Sig := vars 23
def T : Sig := 0xfefee8e8fefee8e8
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B35.low
end B37

namespace B38
def R : List Sig := vars 28
def T : Sig := 0xfff0f000fff0f000
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B38

namespace B39
def R : List Sig := vars 31
def T : Sig := 0xfee8e8a8fee8e8a8
def P : Nat → Bits
  | 0 => ((0xfff003c000f8f8fe : BitVec 64) ++ (0x3ff1ffffffff81c0 : BitVec 64))
  | 1 => ((0xfc707c3fff00ff1f : BitVec 64) ++ (0xc7fe3f41f3398e3f : BitVec 64))
  | 2 => ((0xff8f803fffff001f : BitVec 64) ++ (0xf8ffc7be0cce703f : BitVec 64))
  | 3 => ((0xfffc3ffffffe0 : BitVec 64) ++ (0xfff80000f07fc7 : BitVec 64))
  | 4 => ((0xffffc3fffffff : BitVec 64) ++ (0xff0000000f007ff8 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x4805281040282824 : BitVec 64) ++ (0x9204914a55280c0 : BitVec 64))
  | 1 => ((0x908a85448b00510a : BitVec 64) ++ (0x425212035229061b : BitVec 64))
  | 2 => ((0x2010d68915510012 : BitVec 64) ++ (0x9094842a188c302d : BitVec 64))
  | 3 => ((0x392318ee669a9a40 : BitVec 64) ++ (0xe9200c60f05b46 : BitVec 64))
  | 4 => ((0xc24c6333b8e4e49d : BitVec 64) ++ (0x240000318f006db0 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
theorem s0 : Slice true R T 0x4444444444444444 4 :=
  slice_correct (ms := fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B38.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0x3300330033003300 4 :=
  slice_correct (ms := fixRows 2 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B18.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w5 := combineObserved 0 w1 w2
def w6 := combineObserved 1 w1 w2
def v0 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w5, w6, w3, w4]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 7 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
def p2 : Pool R T := prefixPool s2 [(0, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
theorem s3 : Slice true R T 0x5050505050505050 4 :=
  slice_correct (ms := fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0x3333000033330000 4 :=
  slice_correct (ms := fixRows 2 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
theorem s5 : Slice true R T 0xff000000ff0000 4 :=
  slice_correct (ms := fixRows 8 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p5 : Pool R T := prefixPool s5 [] (by decide +kernel)
theorem s6 : Slice true R T 0x5500550055005500 4 :=
  slice_correct (ms := fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B30.low
def p6 : Pool R T := prefixPool s6 [] (by decide +kernel)
def v1 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w5, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p2), (usePool p1), (usePool p3), (usePool p4), (usePool p5), (usePool p6)] #[v0] ((((((((((0xd345d : Nat) <<< 64) ||| 0x400480a024268000) <<< 64) ||| 0x8041a002e120f401) <<< 64) ||| 0x3742100810482a1b) >>> (((h / 24 + (((((((0x1210 : Nat) <<< 64) ||| 0x908100900000240) <<< 64) ||| 0x10000040120c0186) >>> ((h % 24) * 6)) &&& 63)) % 71) * 3)) &&& 7))) (by decide +kernel)
theorem s7 : Slice true R T 0xffff0000ffff 5 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B11.low
def p7 : Pool R T := prefixPool s7 [] (by decide +kernel)
theorem s8 : Slice true R T 0xffff0000ffff0000 7 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B35.low
def p8 : Pool R T := prefixPool s8 [(1, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def v2 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p3), (usePool p5), (usePool p6), (usePool p7), (usePool p8), (usePool p1), (usePool p4)] #[v0] ((((((((((((0x10500010000 : Nat) <<< 64) ||| 0x1000000000000000) <<< 64) ||| 0x110360000000) <<< 64) ||| 0x100100002000014) <<< 64) ||| 0x720000800062) >>> (((h / 25 + (((((0x108560180020a06 : Nat) <<< 64) ||| 0x40c030802005c01) >>> ((h % 25) * 5)) &&& 31)) % 77) * 4)) &&& 15))) (by decide +kernel)
def w7 := combineObserved 2 w1 w2
def v3 : Closed T 7 := closeState (raw := R) properPN 7 [w7, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p3), (usePool p1), (usePool p5), (usePool p6), (usePool p4)] #[] ((((((((((0x51 : Nat) <<< 64) ||| 0x84505010400480) <<< 64) ||| 0x1821264821904104) <<< 64) ||| 0x902b208280041080) >>> (((h / 24 + (((((0x44 : Nat) <<< 64) ||| 0x74d404526b288600) >>> ((h % 24) * 3)) &&& 7)) % 73) * 3)) &&& 7))) (by decide +kernel)
theorem s9 : Slice true R T 0x5555555555555555 6 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B32.low
def p9 : Pool R T := prefixPool s9 [] (by decide +kernel)
def p10 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s10 : Slice true R T 0xff00ff00ff00ff00 6 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B36.low
def p11 : Pool R T := prefixPool s10 [] (by decide +kernel)
theorem s11 : Slice true R T 0xffff0000ffff0000 6 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B33.low
def p12 : Pool R T := prefixPool s11 [] (by decide +kernel)
def p13 : Pool R T := prefixPool s8 [] (by decide +kernel)
theorem s12 : Slice true R T 0xff00ff00ff00ff00 7 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B37.low
def p14 : Pool R T := prefixPool s12 [] (by decide +kernel)
def a0 : List Move := [swapRows 33]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 7 := rotateClosed v3 a0 a0ok
def v4 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p9), (usePool p10), (usePool p11), (usePool p12), (usePool p13), (usePool p14)] #[v3, r0, v1, v2] ((((((((0x106024542 : Nat) <<< 64) ||| 0x3050408700302094) <<< 64) ||| 0x1003031231455240) >>> (((h / 14 + (((((0x6 : Nat) <<< 64) ||| 0x700cb01c415cc05) >>> ((h % 14) * 5)) &&& 31)) % 41) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 9 :=
  fromClosed v4 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 6, 14), (0xffff0000ffff0000, 6, 22)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B39

namespace B40
def R : List Sig := vars 31
def T : Sig := 0xfeeaea80feeaea80
theorem low : Lower true R T 9 := by
  exact lower_map (ms := [swapRows 50, swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B39.low
end B40

namespace B41
def R : List Sig := vars 11
def T : Sig := 0xaa88aa88aa88aa88
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xff00ff00ff00ff00, 1, 9)] (by decide +kernel)
end B41

namespace B42
def R : List Sig := vars 11
def T : Sig := 0xeecceecceecceecc
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 8, 9), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 1, 9)] (by decide +kernel)
end B42

namespace B43
def R : List Sig := vars 15
def T : Sig := 0xeac8eac8eac8eac8
theorem low : Lower true R T 4 := by
  exact lower_cubes_two (u := true) (j := 2) (r := 2) (s := 6) (L := 2)
    (z0 := 4) (o0 := 0) (z1 := 0) (o1 := 4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (proper_of _ (by decide)) (proper_of _ (by decide)) (proper_of _ (by decide))
    (lower_weaken B41.low (by decide))
    (lower_weaken B42.low (by decide))
end B43

namespace B44
def R : List Sig := vars 23
def T : Sig := 0xeaeac8c8eaeac8c8
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B43.low
end B44

namespace B45
def R : List Sig := vars 27
def T : Sig := 0xeeaaaa88eeaaaa88
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B12.low
end B45

namespace B46
def R : List Sig := vars 15
def T : Sig := 0xfeeafeeafeeafeea
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B1.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B46

namespace B47
def R : List Sig := vars 23
def T : Sig := 0xfefeeaeafefeeaea
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B46.low
end B47

namespace B48
def R : List Sig := vars 25
def T : Sig := 0xffaaaa00ffaaaa00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50, swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B48

namespace B49
def R : List Sig := vars 31
def T : Sig := 0xfeeaeac8feeaeac8
def P : Nat → Bits
  | 0 => ((0x83fffe3801e38fc7 : BitVec 64) ++ (0xfe3ff7fc1e7cfcc0 : BitVec 64))
  | 1 => ((0xfc3e3ff8fe03f1f8 : BitVec 64) ++ (0xefc77c03fd9327c7 : BitVec 64))
  | 2 => ((0xffc03fc73ffc01ff : BitVec 64) ++ (0xff87803e1e3c738 : BitVec 64))
  | 3 => ((0xffffc007fffffe00 : BitVec 64) ++ (0xfff803c0203f83f : BitVec 64))
  | 4 => ((0x7ffffffff : BitVec 64) ++ (0xf00003c003fc003f : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x8804004100200241 : BitVec 64) ++ (0x2209104424244c40 : BitVec 64))
  | 1 => ((0x109054060a019088 : BitVec 64) ++ (0x4442208958912183 : BitVec 64))
  | 2 => ((0x290ca809d4e40152 : BitVec 64) ++ (0xa904156a562c618 : BitVec 64))
  | 3 => ((0x42a80c92674aa400 : BitVec 64) ++ (0xd240238ca03b02d : BitVec 64))
  | 4 => ((0x73313124b99349a4 : BitVec 64) ++ (0x800003a313d80036 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
theorem s0 : Slice true R T 0x5500550055005500 4 :=
  slice_correct (ms := fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B30.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0x3030303030303030 4 :=
  slice_correct (ms := fixRows 2 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B48.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0x5555000055550000 4 :=
  slice_correct (ms := fixRows 1 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 5 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B45.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
def w5 := combineObserved 1 w0 w1
def v0 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2), (usePool p3)] #[] ((((0x1044c0308081108 : Nat) >>> (((h / 9 + (((0x300b0 : Nat) >>> ((h % 9) * 2)) &&& 3)) % 29) * 2)) &&& 3))) (by decide +kernel)
def w6 := combineObserved 1 w0 w2
def v1 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p3), (usePool p2)] #[] ((((((0x10020 : Nat) <<< 64) ||| 0xc800740130933) >>> (((h / 14 + (((0x3cd2 : Nat) >>> ((h % 14) * 1)) &&& 1)) % 43) * 2)) &&& 3))) (by decide +kernel)
theorem s4 : Slice true R T 0xffff0000ffff 4 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B43.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
theorem s5 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B44.low
def p5 : Pool R T := prefixPool s5 [] (by decide +kernel)
def w7 := combineObserved 3 w1 w3
def v2 : Closed T 6 := closeState (raw := R) properPN 6 [w7, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p3), (usePool p1), (usePool p4), (usePool p2), (usePool p5)] #[] ((((((0x20 : Nat) <<< 64) ||| 0x141082800018882) >>> (((h / 9 + (((0x44228 : Nat) >>> ((h % 9) * 3)) &&& 7)) % 28) * 3)) &&& 7))) (by decide +kernel)
theorem s6 : Slice true R T 0xff00ff00ff00ff00 5 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B47.low
def p6 : Pool R T := prefixPool s6 [(1, 0xcccccccccccccccc, 0xff000000ff000000)] (by decide +kernel)
def w8 := combineObserved 0 w3 w4
def v3 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w8, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (joinPools p5 p6), (usePool p4), (usePool p5), (usePool p2), (usePool p3)] #[] ((((((0x1000c6 : Nat) <<< 64) ||| 0x86080c0001800ab0) >>> (((h / 10 + (((0x11084003 : Nat) >>> ((h % 10) * 3)) &&& 7)) % 34) * 3)) &&& 7))) (by decide +kernel)
theorem s7 : Slice true R T 0xf0f0f0f0f0f0f0f 6 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
def p7 : Pool R T := prefixPool s7 [] (by decide +kernel)
def a0 : List Move := [swapRows 67]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 6 := rotateClosed v2 a0 a0ok
def v4 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p3), (usePool p7), (usePool p2)] #[v2, r0, v0, v3, v1] ((((((((0x5402401461000 : Nat) <<< 64) ||| 0x27022002001101) <<< 64) ||| 0x4000100834229004) >>> (((h / 14 + (((0x1800d1e1a47 : Nat) >>> ((h % 14) * 3)) &&& 7)) % 45) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 8 :=
  fromClosed v4 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 2, 6), (0xff00ff00ff00ff00, 1, 9), (0xffff0000ffff0000, 1, 17)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B49

namespace B50
def R : List Sig := vars 31
def T : Sig := 0xfeeafee8feeafee8
theorem low : Lower true R T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 16 0) (raw := R)
    (T := T) (xs := [(0xffff0000ffff0000, 1, 17)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B35.low
  have he : (([(0xffff0000ffff0000, 1, 17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B50

namespace B51
def R : List Sig := vars 59
def T : Sig := 0xffeeeeccffeeee88
theorem low : Lower true R T 8 := by
  exact lower_map (ms := [swapRows 84, swapRows 66, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B50.low
end B51

namespace B52
def R : List Sig := vars 15
def T : Sig := 0xeae8eae8eae8eae8
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 1, 9)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 1, 9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B52

namespace B53
def R : List Sig := vars 60
def T : Sig := 0xfff0f0f0fff0f000
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 83, swapRows 50, swapRows 65, swapRows 32]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B52.low
end B53

namespace B54
def R : List Sig := vars 29
def T : Sig := 0xfffafaa0fffafaa0
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B35.low
end B54

namespace B55
def R : List Sig := vars 31
def T : Sig := 0xfeeefee8feeefee8
theorem low : Lower true R T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 16 0) (raw := R)
    (T := T) (xs := [(0xffff0000ffff0000, 1, 17)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B35.low
  have he : (([(0xffff0000ffff0000, 1, 17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B55

namespace B56
def R : List Sig := vars 61
def T : Sig := 0xfffafafafffafaa0
theorem low : Lower true R T 8 := by
  exact lower_map (ms := [swapRows 84, swapRows 66, swapRows 33]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B55.low
end B56

namespace B57
def R : List Sig := vars 63
def T : Sig := 0xfeeaeac8feeaea80
def P : Nat → Bits
  | 0 => ((0xf8fffff8ffffe0e0 : BitVec 64) ++ (0x13027cfcc09f9fd3 : BitVec 64))
  | 1 => ((0xff0780ff0780ffe3 : BitVec 64) ++ (0xed1d9327c766667f : BitVec 64))
  | 2 => ((0xfff800fff800ff1c : BitVec 64) ++ (0x6de1e3c73878786f : BitVec 64))
  | 3 => ((0xffffff001f : BitVec 64) ++ (0x8efe03f83f807f84 : BitVec 64))
  | 4 => ((0xffffff000000001f : BitVec 64) ++ (0xf0fffc003fff8008 : BitVec 64))
  | 5 => ((0x1fe0 : BitVec 64) ++ (0xffffffc0000030 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x1848a21848a22120 : BitVec 64) ++ (0x1300244c400a8ad1 : BitVec 64))
  | 1 => ((0x6905046905044ac1 : BitVec 64) ++ (0xb60c91218326263f : BitVec 64))
  | 2 => ((0xb2d00ab2d00a952c : BitVec 64) ++ (0x496162c61858586e : BitVec 64))
  | 3 => ((0x10c4a65c0656 : BitVec 64) ++ (0x8cb603b02d807500 : BitVec 64))
  | 4 => ((0xc4a65c000010189b : BitVec 64) ++ (0x60dbd80036f50000 : BitVec 64))
  | 5 => ((0xc46000c4601fff : BitVec 64) ++ (0xedffffffc0000000 : BitVec 64))
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
theorem s0 : Slice true R T 0xff000000ff 5 :=
  slice_correct (ms := fixRows 24 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B3.low
def p0 := cutPrefix s0 []
theorem s1 : Slice true R T 0xcc000000cc 4 :=
  slice_correct (ms := fixRows 24 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B19.low
def p1 := cutPrefix s1 []
theorem s2 : Slice true R T 0xcccccccccccccccc 8 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B56.low
def g0 : Choice := (0,0xff00ff00ff00ff00,0xffff0000ffff0000)
def g1 : Choice := (1,0xff00ff00ff00ff00,0xffff0000ffff0000)
def g2 : Choice := (3,0xff000000ff000000,0xffffff00ffffff00)
def p2 := cutPrefix s2 [g0, g1, g2]
theorem s3 : Slice true R T 0xffffffff 9 :=
  slice_correct (ms := fixRows 32 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B40.low
def g3 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc)
def p3 := cutPrefix s3 [g3, g0, g1, g2]
theorem s4 : Slice true R T 0x5555555555555555 8 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B29.low
def p4 := cutPrefix s4 [g0, g1, g2]
theorem s5 : Slice true R T 0xf0f0f0f0f0f0f0f 7 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B14.low
def p5 := cutPrefix s5 [g0, g1, g2]
theorem s6 : Slice true R T 0xf0f0f0f0f0f0f0f0 8 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B51.low
def p6 := cutPrefix s6 [g0, g1, g2]
def p7 := cutPrefix s3 [g0, g1, g2]
def w6 := combineObserved 0 w3 w4
def w7 := combineObserved 1 w3 w4
def w8 := combineObserved 3 w6 w7
def w9 := combineObserved 3 w0 w1
def g4 : Choice := (1,0xffff0000ffff00,0x5050505050505050)
def p8 := cutPrefix s6 [g0, g1, g2, g4]
def g5 : Choice := (2,0xffff0000ffff00,0x5050505050505050)
def p9 := cutPrefix s6 [g0, g1, g2, g5]
theorem s7 : Slice true R T 0xf0f0f0f00000000 6 :=
  slice_correct (ms := fixRows 4 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
def p10 := cutPrefix s7 [g0, g1, g2]
def g6 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0)
def p11 := cutPrefix s3 [g6, g0, g1, g2]
def g7 : Choice := (3,0x5050505050505050,0xcccccccccccccccc)
def p12 := cutPrefix s6 [g0, g1, g2, g7]
def w10 := combineObserved 3 w0 w2
def w11 := combineObserved 1 w0 w3
def w12 := combineObserved 0 w1 w11
def w13 := combineObserved 2 w3 w4
def w14 := combineObserved 3 w13 w11
theorem s8 : Slice true R T 0xff00ff00 5 :=
  slice_correct (ms := fixRows 32 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B47.low
def g8 : Choice := (0,0xcccccccccccccccc,0xffffffffffff0000)
def p13 := cutPrefix s8 [g8]
def w15 := combineObserved 2 w11 w4
def w16 := combineObserved 1 w4 w5
def g9 : Choice := (1,0xffff0000ffff0000,0xffffffff00000000)
def p14 := cutPrefix s2 [g9]
def p15 := cutPrefix s8 []
def w17 := combineObserved 2 w1 w4
def w18 := combineObserved 2 w17 w5
def w19 := combineObserved 3 w18 w1
def w20 := combineObserved 0 w1 w3
def w21 := combineObserved 1 w0 w20
def w22 := combineObserved 2 w21 w4
def w23 := combineObserved 1 w0 w4
def w24 := combineObserved 0 w1 w4
def w25 := combineObserved 1 w0 w24
def w26 := combineObserved 2 w1 w5
def w27 := combineObserved 2 w4 w3
def w28 := combineObserved 3 w27 w23
theorem s9 : Slice true R T 0xffffffff00000000 8 :=
  slice_correct (ms := fixRows 0 32) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B49.low
def g10 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00)
def g11 : Choice := (2,0xff00ff00ff00ff00,0xffff0000ffff0000)
def g12 : Choice := (3,0xff000000ff00,0xffaaffaaffaaffaa)
def p16 := cutPrefix s9 [g10, g11, g12]
def w29 := combineObserved 0 w2 w11
theorem s10 : Slice true R T 0xffff0000 5 :=
  slice_correct (ms := fixRows 32 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B46.low
def p17 := cutPrefix s10 []
def g13 : Choice := (2,0xffaaffaaffaaffaa,0xffff0000ffff0000)
def p18 := cutPrefix s2 [g10, g13, g9]
def p19 := cutPrefix s9 [g10, g13]
def p20 := cutPrefix s7 [g10, g13]
theorem s11 : Slice true R T 0xffff0000ffff 7 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B8.low
def p21 := cutPrefix s11 [g8]
theorem s12 : Slice true R T 0x33333333 5 :=
  slice_correct (ms := fixRows 34 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B17.low
def p22 := cutPrefix s12 []
theorem s13 : Slice true R T 0xff00ff00ff00ff 7 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
def g14 : Choice := (0,0xcccccccccccccccc,0xffffffffff00ff00)
def g15 : Choice := (1,0xcccccccccc00cc00,0xffff0000ffff0000)
def p23 := cutPrefix s13 [g14, g15]
def g16 : Choice := (1,0xff00ff00ff00ff00,0xffffffff00000000)
def p24 := cutPrefix s4 [g16, g14]
def w30 := combineObserved 1 w3 w5
def w31 := combineObserved 0 w1 w30
def w32 := combineObserved 1 w31 w4
def p25 := cutPrefix s9 []
def p26 := cutPrefix s2 [g16]
def p27 := cutPrefix s5 [g16, g14]
def p28 := cutPrefix s6 [g16, g14]
def w33 := combineObserved 1 w31 w23
def w34 := combineObserved 3 w19 w11
def g17 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xff000000ff000000)
def p29 := cutPrefix s5 [g0, g17, g1]
def g18 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xc0c0c0c0c0c0c0c0)
def p30 := cutPrefix s6 [g0, g17, g1, g18]
def p31 := cutPrefix s4 [g0, g1]
def p32 := cutPrefix s6 [g0, g17, g1]
def g19 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xffaaaaaaffaaaaaa)
def p33 := cutPrefix s6 [g0, g17, g1, g19]
def g20 : Choice := (3,0xc0c0c0c0c0c0c0c0,0xffaaaaaaffaaaaaa)
def p34 := cutPrefix s6 [g0, g17, g1, g20]
def w35 := combineObserved 0 w1 w2
def w36 := combineObserved 1 w0 w6
def g21 : Choice := (1,0xffff0000ffff00,0xc0c0c0c0c0c0c0c0)
def p35 := cutPrefix s6 [g0, g1, g2, g21]
def g22 : Choice := (2,0xffff0000ffff00,0xc0c0c0c0c0c0c0c0)
def p36 := cutPrefix s6 [g0, g1, g2, g22]
def g23 : Choice := (0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0)
def p37 := cutPrefix s3 [g23, g0, g1, g2]
def p38 := cutPrefix s6 [g0, g1, g2, g18]
def p39 := cutPrefix s9 [g0, g17, g1]
def g24 : Choice := (2,0xcccccccccccccccc,0xffffffff00000000)
def p40 := cutPrefix s4 [g24, g0, g1]
def p41 := cutPrefix s3 [g0, g17, g1]
theorem s14 : Slice true R T 0xcccccccc 7 :=
  slice_correct (ms := fixRows 32 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B54.low
def p42 := cutPrefix s14 [g0, g17, g1]
def p43 := cutPrefix s2 [g0, g17, g1]
def p44 := cutPrefix s6 [g24, g0, g17, g1]
def p45 := cutPrefix s13 [g24]
def p46 := cutPrefix s0 [g24]
def p47 := cutPrefix s9 [g0, g1, g2]
def p48 := cutPrefix s14 [g0, g1, g2]
def p49 := cutPrefix s4 [g24, g0, g1, g2]
def p50 := cutPrefix s6 [g24, g0, g1, g2]
def w37 := combineObserved 0 w1 w36
theorem s15 : Slice true R T 0xcc00cc00cc00cc 5 :=
  slice_correct (ms := fixRows 8 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B22.low
def p51 := cutPrefix s15 []
def w38 := combineObserved 2 w1 w36
def w39 := combineObserved 0 w2 w36
def g25 : Choice := (1,0x50505000505050,0xaaaaaaaaaaaaaaaa)
def p52 := cutPrefix s6 [g0, g17, g1, g25]
def w40 := combineObserved 2 w2 w36
def g26 : Choice := (1,0xffff0000ffff00,0xaaaaaaaaaaaaaaaa)
def p53 := cutPrefix s3 [g0, g1, g2, g26]
def w41 := combineObserved 1 w8 w0
def g27 : Choice := (3,0xffff0000ffff00,0xf0f0f0f0f0f0f0f0)
def p54 := cutPrefix s3 [g0, g1, g2, g27]
def g28 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xf00000f0f00000f0)
def p55 := cutPrefix s6 [g0, g1, g2, g28]
def g29 : Choice := (2,0xcccccccccccccccc,0xf00000f0f00000f0)
def p56 := cutPrefix s6 [g0, g1, g2, g29]
def w42 := combineObserved 3 w8 w2
def g30 : Choice := (1,0xffff0000ffff00,0xffffffff00000000)
def p57 := cutPrefix s4 [g0, g1, g2, g30]
def p58 := cutPrefix s2 [g0, g1, g2, g30]
def p59 := cutPrefix s6 [g0, g1, g2, g30]
def w43 := combineObserved 1 w8 w5
def g31 : Choice := (1,0xffffff00ffffff00,0xffffffff00000000)
def p60 := cutPrefix s4 [g0, g1, g2, g31]
def p61 := cutPrefix s2 [g0, g1, g2, g31]
def p62 := cutPrefix s6 [g0, g1, g2, g31]
theorem s16 : Slice true R T 0xff00ff 5 :=
  slice_correct (ms := fixRows 40 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B9.low
def p63 := cutPrefix s16 []
theorem s17 : Slice true R T 0x55005500 4 :=
  slice_correct (ms := fixRows 33 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B30.low
def p64 := cutPrefix s17 []
def w44 := combineObserved 1 w7 w5
def g32 : Choice := (2,0xeeeeeeeeeeaaeeaa,0xffff0000ffff0000)
def p65 := cutPrefix s4 [g16, g14, g32]
def p66 := cutPrefix s12 [g32]
def g33 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xcccccccccc00cc00)
def p67 := cutPrefix s2 [g16, g33, g32, g15]
def w45 := combineObserved 1 w0 w31
def w46 := combineObserved 2 w45 w4
def g34 : Choice := (1,0xcccccccccccc0000,0xff00ff00ff00ff00)
def p68 := cutPrefix s4 [g9, g8, g34]
def w47 := combineObserved 1 w19 w3
def w48 := combineObserved 3 w0 w47
def p69 := cutPrefix s5 []
def g35 : Choice := (1,0x4444444444444444,0xff00ff00ff00ff00)
def p70 := cutPrefix s5 [g3, g35]
def g36 : Choice := (1,0xf0f00000f0f0,0xff44ff44ff44ff44)
def p71 := cutPrefix s6 [g3, g35, g36]
def g37 : Choice := (3,0xf0f00000f0f0,0xff44ff44ff44ff44)
def p72 := cutPrefix s6 [g3, g35, g37]
def p73 := cutPrefix s6 []
def w49 := combineObserved 2 w2 w4
def w50 := combineObserved 1 w9 w3
def p74 := cutPrefix s4 [g35, g9]
def p75 := cutPrefix s4 [g9]
def p76 := cutPrefix s2 [g35, g9]
def p77 := cutPrefix s5 [g9]
def p78 := cutPrefix s6 [g9]
theorem s18 : Slice true R T 0x4444444444444444 5 :=
  slice_correct (ms := fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B53.low
def p79 := cutPrefix s18 [g9]
def p80 := cutPrefix s9 [g3, g35]
def p81 := cutPrefix s11 []
def p82 := cutPrefix s3 [g3, g35]
def g38 : Choice := (2,0x4444444444444444,0xffff0000ffff0000)
def p83 := cutPrefix s4 [g38, g16]
def p84 := cutPrefix s2 [g38, g16]
def p85 := cutPrefix s5 [g16]
def p86 := cutPrefix s6 [g16]
def p87 := cutPrefix s13 []
def g39 : Choice := (1,0x444400004444,0xff00ff00ff00ff00)
def p88 := cutPrefix s2 [g38, g16, g39]
def p89 := cutPrefix s18 [g16]
def p90 := cutPrefix s9 [g3, g38]
def p91 := cutPrefix s3 [g3, g38]
def w51 := combineObserved 2 w9 w4
def p92 := cutPrefix s4 [g16]
def g40 : Choice := (2,0xcccccccccccccccc,0xffff0000ffff0000)
def p93 := cutPrefix s4 [g40, g16]
def p94 := cutPrefix s11 [g16]
def p95 := cutPrefix s8 [g3]
def p96 := cutPrefix s9 [g3, g40]
def p97 := cutPrefix s3 [g3, g40]
def p98 := cutPrefix s10 [g3]
def p99 := cutPrefix s2 [g0, g1]
def p100 := cutPrefix s5 [g0, g1]
def p101 := cutPrefix s6 [g0, g1]
def p102 := cutPrefix s13 [g3]
def p103 := cutPrefix s3 [g0, g1]
def p104 := cutPrefix s3 [g3, g0, g1]
def p105 := cutPrefix s0 [g3]
def p106 := cutPrefix s11 [g3]
def g41 : Choice := (3,0xff00ff00ff00ff00,0xffff0000ffff0000)
def p107 := cutPrefix s2 [g11, g41]
def p108 := cutPrefix s3 [g3, g11, g41]
def p109 := cutPrefix s4 [g11, g41]
def p110 := cutPrefix s5 [g11, g41]
def p111 := cutPrefix s6 [g11, g41]
def p112 := cutPrefix s3 [g11, g41]
theorem s19 : Slice true R T 0x55550000 4 :=
  slice_correct (ms := fixRows 33 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p113 := cutPrefix s19 []
def g42 : Choice := (3,0xffff0000ffff0000,0xffffffffff00ff00)
def p114 := cutPrefix s2 [g16, g42]
def p115 := cutPrefix s3 [g3]
def p116 := cutPrefix s9 [g3]
def p117 := cutPrefix s4 [g16, g42]
def p118 := cutPrefix s5 [g16, g42]
def p119 := cutPrefix s6 [g16, g42]
def p120 := cutPrefix s13 [g42]
def w52 := combineObserved 3 w4 w30
def p121 := cutPrefix s6 [g0, g1, g7]
def p122 := cutPrefix s13 [g6]
def g43 : Choice := (1,0x5050505050505050,0xffffff00ffffff00)
def p123 := cutPrefix s6 [g0, g1, g43]
def g44 : Choice := (3,0x5050505050505050,0xffffff00ffffff00)
def p124 := cutPrefix s6 [g0, g1, g44]
def p125 := cutPrefix s3 [g6, g0, g1]
def p126 := cutPrefix s7 [g0, g1]
def p127 := cutPrefix s11 [g6]
def p128 := cutPrefix s3 [g6, g11, g41]
def p129 := cutPrefix s6 [g11, g41, g7]
def p130 := cutPrefix s7 [g11, g41]
def g45 : Choice := (0,0xcccccccccccccccc,0xffaaffaaffaaffaa)
def p131 := cutPrefix s5 [g10, g45]
def p132 := cutPrefix s6 [g10, g45, g18]
def p133 := cutPrefix s6 [g10]
def g46 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xff00ff00ff00ff00)
def p134 := cutPrefix s6 [g10, g45, g46]
def g47 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xffaaffaaffaaffaa)
def p135 := cutPrefix s6 [g10, g45, g47]
def p136 := cutPrefix s2 []
def p137 := cutPrefix s6 [g10, g45]
def g48 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000)
def g49 : Choice := (1,0xffff0000ffff0000,0xff00ff00ff00ff00)
def p138 := cutPrefix s5 [g48, g49]
def p139 := cutPrefix s6 [g48, g49, g18]
def p140 := cutPrefix s4 [g49]
def p141 := cutPrefix s6 [g48, g49, g46]
def p142 := cutPrefix s13 [g48]
def g50 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xffffaaaaffffaaaa)
def p143 := cutPrefix s6 [g48, g49, g50]
def g51 : Choice := (3,0xc0c0c0c0c0c0c0c0,0xffffaaaaffffaaaa)
def p144 := cutPrefix s6 [g48, g49, g51]
def g52 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xffffff00ffffff00)
def p145 := cutPrefix s6 [g48, g49, g52]
def g53 : Choice := (3,0xc0c0c0c0c0c0c0c0,0xffffff00ffffff00)
def p146 := cutPrefix s6 [g48, g49, g53]
def p147 := cutPrefix s13 [g23]
def p148 := cutPrefix s4 [g23]
def p149 := cutPrefix s5 [g10, g11]
def g54 : Choice := (1,0xff000000ff00,0xc0c0c0c0c0c0c0c0)
def p150 := cutPrefix s6 [g10, g11, g54]
def p151 := cutPrefix s6 [g10, g11, g18]
def p152 := cutPrefix s4 [g11]
def p153 := cutPrefix s6 [g10, g11, g47]
def g55 : Choice := (3,0xc0c0c0c0c0c0c0c0,0xffaaffaaffaaffaa)
def p154 := cutPrefix s6 [g10, g11, g55]
def g56 : Choice := (1,0xffaaffaaffaaffaa,0xffff0000ffff0000)
def p155 := cutPrefix s5 [g10, g56]
def p156 := cutPrefix s6 [g10, g56, g18]
def p157 := cutPrefix s4 [g56]
def p158 := cutPrefix s6 [g10, g56, g46]
def p159 := cutPrefix s13 [g56]
def g57 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xffff0000ffff0000)
def p160 := cutPrefix s6 [g10, g56, g57]
def p161 := cutPrefix s11 [g10]
def g58 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xffffffaaffffffaa)
def p162 := cutPrefix s6 [g10, g56, g58]
def g59 : Choice := (3,0xc0c0c0c0c0c0c0c0,0xffffffaaffffffaa)
def p163 := cutPrefix s6 [g10, g56, g59]
def w53 := combineObserved 1 w11 w4
def p164 := cutPrefix s5 [g10, g13]
def g60 : Choice := (1,0xffaa0000ffaa,0xc0c0c0c0c0c0c0c0)
def p165 := cutPrefix s6 [g10, g13, g60]
def g61 : Choice := (2,0xffaa0000ffaa,0xc0c0c0c0c0c0c0c0)
def p166 := cutPrefix s6 [g10, g13, g61]
def p167 := cutPrefix s6 [g10, g13, g18]
def p168 := cutPrefix s4 [g13]
def p169 := cutPrefix s6 [g10, g13, g46]
def p170 := cutPrefix s13 [g13]
def p171 := cutPrefix s4 [g45, g16]
def p172 := cutPrefix s2 [g10, g16]
def g62 : Choice := (1,0xcc88cc88cc88cc88,0xffff0000ffff0000)
def p173 := cutPrefix s2 [g10, g16, g62]
def p174 := cutPrefix s9 [g10, g45]
def p175 := cutPrefix s7 [g10, g45]
def p176 := cutPrefix s13 [g45]
def p177 := cutPrefix s3 [g10, g45]
def p178 := cutPrefix s13 [g45, g42]
def p179 := cutPrefix s4 [g45, g9]
def p180 := cutPrefix s2 [g10, g9, g62]
def p181 := cutPrefix s2 [g10, g9]
def g63 : Choice := (0,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa)
def p182 := cutPrefix s2 [g10, g63]
def p183 := cutPrefix s2 [g10]
def g64 : Choice := (2,0xcccccccccccccccc,0xf0a0f0a0f0a0f0a0)
def p184 := cutPrefix s6 [g10, g45, g64]
def p185 := cutPrefix s2 [g10, g11]
def p186 := cutPrefix s2 [g10, g13]
def g65 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xcc00cc00cc00cc00)
def p187 := cutPrefix s2 [g48, g65]
def g66 : Choice := (0,0xcccccccccccccccc,0xff00ff00ff00ff00)
def p188 := cutPrefix s3 [g48, g66, g65]
def p189 := cutPrefix s6 [g66, g65]
def p190 := cutPrefix s4 [g66]
def a1 : List Move := [swapRows 67]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def p191 := cutPrefix s4 []
def g67 : Choice := (0,0xcccccccccccccccc,0xffff0000ffff0000)
def g68 : Choice := (3,0xcccc0000cccc0000,0xffaaffaaffaaffaa)
def p192 := cutPrefix s4 [g67, g68]
def p193 := cutPrefix s2 [g10, g68]
def p194 := cutPrefix s3 []
def p195 := cutPrefix s3 [g10, g67, g68]
def w54 := combineObserved 3 w24 w11
def g69 : Choice := (3,0xffff0000ffff0000,0xffaaffaaffaaffaa)
def p196 := cutPrefix s4 [g67, g69]
def p197 := cutPrefix s2 [g10, g69]
def p198 := cutPrefix s5 [g10, g69]
def p199 := cutPrefix s9 [g10, g69]
def p200 := cutPrefix s3 [g10, g67, g69]
def p201 := cutPrefix s3 [g48, g49]
def p202 := cutPrefix s14 [g48, g49]
def p203 := cutPrefix s9 [g48, g49]
def p204 := cutPrefix s4 [g24, g49]
def p205 := cutPrefix s11 [g24]
def p206 := cutPrefix s4 [g24]
def p207 := cutPrefix s9 [g10, g11]
def p208 := cutPrefix s3 [g10, g11]
def p209 := cutPrefix s14 [g10, g11]
def p210 := cutPrefix s4 [g24, g11]
def p211 := cutPrefix s3 [g10, g56]
def p212 := cutPrefix s14 [g10, g56]
def p213 := cutPrefix s9 [g10, g56]
def p214 := cutPrefix s4 [g24, g56]
def p215 := cutPrefix s2 [g10, g56]
def p216 := cutPrefix s5 [g24]
def p217 := cutPrefix s6 [g24]
def p218 := cutPrefix s3 [g10, g13]
def p219 := cutPrefix s14 [g10, g13]
def p220 := cutPrefix s4 [g24, g13]
def p221 := cutPrefix s6 [g10, g11]
def g70 : Choice := (0,0xffaaffaaffaaffaa,0xffff0000ffff0000)
def p222 := cutPrefix s6 [g10, g70]
def p223 := cutPrefix s5 [g10, g70]
def g71 : Choice := (1,0xf0a0f0a0f0a0f0a0,0xffff0000ffff0000)
def p224 := cutPrefix s6 [g10, g70, g71]
def p225 := cutPrefix s9 [g10, g70]
def p226 := cutPrefix s3 [g10, g70]
def p227 := cutPrefix s4 [g63]
def p228 := cutPrefix s9 [g10, g63]
def p229 := cutPrefix s3 [g10, g63]
def p230 := cutPrefix s7 [g10, g70]
def w55 := combineObserved 0 w11 w4
def p231 := cutPrefix s6 [g10, g13, g71]
def g72 : Choice := (1,0xffaa0000ffaa,0xf0f00000f0f00000)
def p232 := cutPrefix s6 [g10, g69, g72]
def g73 : Choice := (0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000)
def p233 := cutPrefix s4 [g73, g69]
def g74 : Choice := (2,0xcccccccccccccccc,0xf0f00000f0f00000)
def p234 := cutPrefix s6 [g10, g69, g74]
def p235 := cutPrefix s6 [g10, g69]
def p236 := cutPrefix s3 [g10, g73, g69]
def g75 : Choice := (1,0xf0f00000f0f00000,0xff00ff00ff00ff00)
def p237 := cutPrefix s6 [g10, g69, g75]
def p238 := cutPrefix s7 [g10, g69]
def w56 := combineObserved 0 w2 w4
def g76 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xf0f00000f0f00000)
def p239 := cutPrefix s6 [g10, g69, g76]
def g77 : Choice := (1,0xf0f00000f0f00000,0xffaaffaaffaaffaa)
def p240 := cutPrefix s6 [g10, g69, g77]
def g78 : Choice := (1,0xf0f00000f0f0,0xffaaffaaffaaffaa)
def p241 := cutPrefix s6 [g10, g70, g78]
def g79 : Choice := (2,0xffff0000ffff0000,0xff00ff00ff00ff00)
def g80 : Choice := (3,0xff000000ff0000,0xffffaaaaffffaaaa)
def p242 := cutPrefix s4 [g79, g80]
def p243 := cutPrefix s3 [g48, g79, g80]
def p244 := cutPrefix s8 [g48]
def p245 := cutPrefix s13 [g14]
def p246 := cutPrefix s9 [g10]
def p247 := cutPrefix s3 [g10]
def p248 := cutPrefix s3 [g10, g14]
def p249 := cutPrefix s3 [g14]
def p250 := cutPrefix s7 [g10]
def p251 := cutPrefix s11 [g16, g14]
def p252 := cutPrefix s13 [g14, g13]
def p253 := cutPrefix s4 [g16, g13]
theorem s20 : Slice true R T 0x55555555 7 :=
  slice_correct (ms := fixRows 33 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B27.low
def p254 := cutPrefix s20 [g42]
def p255 := cutPrefix s3 [g10, g42]
def p256 := cutPrefix s3 [g42]
def p257 := cutPrefix s2 [g10, g16, g42]
def p258 := cutPrefix s10 [g10]
def g81 : Choice := (0,0xffffaaaaffffaaaa,0xff00ff00ff00ff00)
def p259 := cutPrefix s4 [g81, g16]
def p260 := cutPrefix s11 [g81, g16]
def p261 := cutPrefix s2 [g48, g81, g16]
def p262 := cutPrefix s9 [g48, g81]
def p263 := cutPrefix s7 [g48, g81]
def p264 := cutPrefix s6 [g48, g81, g16]
def g82 : Choice := (0,0xffffaaaaffffaaaa,0xffffffffff00ff00)
def p265 := cutPrefix s3 [g48, g82]
def w57 := combineObserved 0 w23 w3
def p266 := cutPrefix s4 [g13, g9]
def p267 := cutPrefix s6 [g10, g13, g9]
def p268 := cutPrefix s13 [g13, g9]
theorem s21 : Slice true R T 0xcccc0000cccc 5 :=
  slice_correct (ms := fixRows 16 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B21.low
def p269 := cutPrefix s21 []
def p270 := cutPrefix s18 []
def p271 := cutPrefix s2 [g48]
def g83 : Choice := (2,0xffffaaaaffffaaaa,0xff00ff00ff00ff00)
def p272 := cutPrefix s2 [g48, g83]
def w58 := combineObserved 2 w23 w3
def w59 := combineObserved 3 w58 w1
def p273 := cutPrefix s9 [g48]
def p274 := cutPrefix s2 [g48, g16]
def p275 := cutPrefix s3 [g48]
def p276 := cutPrefix s7 [g48]
def g84 : Choice := (3,0x5555000055550000,0xffffffffff00ff00)
def p277 := cutPrefix s4 [g16, g84]
def g85 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000)
def p278 := cutPrefix s2 [g85, g16, g84]
def p279 := cutPrefix s7 [g85]
def p280 := cutPrefix s6 [g85, g16, g84]
def p281 := cutPrefix s3 [g85, g84]
def p282 := cutPrefix s13 [g85, g84]
def p283 := cutPrefix s9 [g85]
def w60 := combineObserved 3 w0 w4
def w61 := combineObserved 3 w60 w30
def p284 := cutPrefix s5 [g0, g17]
def p285 := cutPrefix s6 [g0, g17, g18]
def p286 := cutPrefix s4 [g0]
def p287 := cutPrefix s6 [g0, g17]
def p288 := cutPrefix s6 [g0, g17, g19]
def p289 := cutPrefix s6 [g0, g17, g20]
def p290 := cutPrefix s6 [g0, g1, g18]
def g86 : Choice := (1,0xc0c0c0c0c0c0c0c0,0xff000000ff000000)
def p291 := cutPrefix s6 [g0, g1, g86]
def p292 := cutPrefix s6 [g0, g1, g52]
def p293 := cutPrefix s6 [g0, g1, g53]
def p294 := cutPrefix s3 [g23, g0, g1]
def g87 : Choice := (1,0xff000000ff00,0xaaaaaaaaaaaaaaaa)
def p295 := cutPrefix s5 [g11, g87]
def p296 := cutPrefix s6 [g11, g87, g18]
def g88 : Choice := (1,0xaaaaffaaaaaaffaa,0xc0c0c0c0c0c0c0c0)
def p297 := cutPrefix s6 [g11, g87, g88]
def g89 : Choice := (2,0xaaaaffaaaaaaffaa,0xc0c0c0c0c0c0c0c0)
def p298 := cutPrefix s6 [g11, g87, g89]
def p299 := cutPrefix s6 [g11, g87, g46]
def w62 := combineObserved 1 w13 w0
def p300 := cutPrefix s11 [g23]
def p301 := cutPrefix s3 [g23, g11, g41]
def p302 := cutPrefix s6 [g11, g41, g18]
def p303 := cutPrefix s9 [g66, g65]
def p304 := cutPrefix s3 [g66, g65]
def w63 := combineObserved 0 w21 w2
def g90 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xcccc0000cccc0000)
def p305 := cutPrefix s5 [g67, g90]
def g91 : Choice := (1,0x1010505010105050,0xaaaaaaaaaaaaaaaa)
def p306 := cutPrefix s6 [g67, g90, g91]
def p307 := cutPrefix s6 [g67, g90]
def w64 := combineObserved 3 w25 w2
def p308 := cutPrefix s2 [g65]
def w65 := combineObserved 1 w21 w4
def p309 := cutPrefix s5 [g66, g65]
def g92 : Choice := (1,0xf0f00000f0f0,0xaaaaaaaaaaaaaaaa)
def p310 := cutPrefix s6 [g66, g65, g92]
def g93 : Choice := (1,0xf0f00000f0f0,0xeeaaeeaaeeaaeeaa)
def p311 := cutPrefix s6 [g66, g65, g93]
def g94 : Choice := (3,0xf0f00000f0f0,0xeeaaeeaaeeaaeeaa)
def p312 := cutPrefix s6 [g66, g65, g94]
def p313 := cutPrefix s4 [g66, g9]
def p314 := cutPrefix s2 [g65, g9]
def p315 := cutPrefix s13 [g9]
def p316 := cutPrefix s6 [g66, g65, g9]
def g95 : Choice := (3,0xcccc0000cccc0000,0xffffffffff00ff00)
def p317 := cutPrefix s4 [g67, g16, g95]
def p318 := cutPrefix s2 [g16, g95]
def p319 := cutPrefix s7 [g67]
def p320 := cutPrefix s6 [g67, g16, g95]
def p321 := cutPrefix s3 [g67, g95]
def p322 := cutPrefix s13 [g67, g95]
def p323 := cutPrefix s9 [g67]
def w66 := combineObserved 3 w24 w30
def g96 : Choice := (2,0xcccccccccccccccc,0xff00ff00ff00ff00)
def g97 : Choice := (1,0xcc00cc00cc00cc,0xffff0000ffff0000)
def p324 := cutPrefix s4 [g96, g97, g9]
def p325 := cutPrefix s2 [g97, g9]
def p326 := cutPrefix s6 [g96, g97, g9]
def p327 := cutPrefix s7 [g96, g97]
def p328 := cutPrefix s15 [g9]
def p329 := cutPrefix s13 [g97, g9]
def p330 := cutPrefix s9 [g96, g97]
def p331 := cutPrefix s3 [g96, g97]
def w67 := combineObserved 2 w1 w3
def w68 := combineObserved 1 w67 w4
def g98 : Choice := (2,0xcccc0000cccc,0xffffffff00000000)
def g99 : Choice := (3,0xcccc,0xcccccccccccccccc)
def p332 := cutPrefix s4 [g40, g98, g99]
def p333 := cutPrefix s3 [g40, g99]
def p334 := cutPrefix s7 []
def p335 := cutPrefix s7 [g40]
def p336 := cutPrefix s6 [g40, g98, g99]
def p337 := cutPrefix s2 [g98]
def p338 := cutPrefix s11 [g98, g99]
def g100 : Choice := (0,0xcccc0000cccc,0xffffffffff00ff00)
def p339 := cutPrefix s4 [g40, g16, g100]
def p340 := cutPrefix s2 [g16, g100]
def p341 := cutPrefix s6 [g40, g16, g100]
def p342 := cutPrefix s3 [g40, g100]
def p343 := cutPrefix s13 [g40, g100]
def g101 : Choice := (1,0xcccc0000cc00,0xffff0000ffff0000)
def p344 := cutPrefix s2 [g16, g100, g101]
def p345 := cutPrefix s11 [g16, g100]
def w69 := combineObserved 0 w17 w30
def p346 := cutPrefix s9 [g0, g17]
def p347 := cutPrefix s4 [g24, g0]
def p348 := cutPrefix s3 [g0, g17]
def p349 := cutPrefix s2 [g0, g17]
def p350 := cutPrefix s6 [g24, g0, g17]
def p351 := cutPrefix s9 [g0, g1]
def p352 := cutPrefix s6 [g24, g0, g1]
def p353 := cutPrefix s14 [g0, g1]
def p354 := cutPrefix s9 [g11, g87]
def p355 := cutPrefix s3 [g11, g87]
def p356 := cutPrefix s14 [g11, g87]
def p357 := cutPrefix s2 [g11, g87]
def p358 := cutPrefix s9 [g11, g41]
def p359 := cutPrefix s4 [g24, g11, g41]
def p360 := cutPrefix s6 [g24, g11, g41]
def p361 := cutPrefix s6 [g0, g17, g25]
def p362 := cutPrefix s10 [g17]
def p363 := cutPrefix s4 [g0, g1, g31]
def p364 := cutPrefix s2 [g0, g1, g31]
def p365 := cutPrefix s6 [g0, g1, g31]
def p366 := cutPrefix s13 [g31]
def g102 : Choice := (0,0xcccccccccccccccc,0xffffff00ffffff00)
def p367 := cutPrefix s4 [g1, g102]
def g103 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xcccccc00cccccc00)
def p368 := cutPrefix s2 [g1, g103]
def p369 := cutPrefix s6 [g1, g102, g103]
def p370 := cutPrefix s3 [g1, g102, g103]
def p371 := cutPrefix s2 [g1, g103, g16]
def p372 := cutPrefix s2 [g1, g103, g9]
def w70 := combineObserved 0 w1 w7
def w71 := combineObserved 1 w0 w70
def p373 := cutPrefix s4 [g1, g16, g42]
def p374 := cutPrefix s2 [g1, g16, g42]
def p375 := cutPrefix s7 [g1]
def p376 := cutPrefix s6 [g1, g16, g42]
def p377 := cutPrefix s3 [g1, g42]
theorem s22 : Slice true R T 0xffff 5 :=
  slice_correct (ms := fixRows 48 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
def p378 := cutPrefix s22 []
def g104 : Choice := (3,0xff00ff00ff00ff00,0xffffffffffff0000)
def p379 := cutPrefix s4 [g11, g9, g104]
def p380 := cutPrefix s2 [g11, g9, g104]
def p381 := cutPrefix s6 [g11, g9, g104]
def p382 := cutPrefix s11 [g104]
def p383 := cutPrefix s7 [g11]
def p384 := cutPrefix s3 [g11, g104]
def w72 := combineObserved 3 w3 w16
def p385 := cutPrefix s2 [g16, g33]
def p386 := cutPrefix s6 [g16, g14, g33]
def p387 := cutPrefix s9 [g33]
def p388 := cutPrefix s3 [g14, g33]
def p389 := cutPrefix s2 [g16, g33, g15]
def p390 := cutPrefix s7 [g33]
def p391 := cutPrefix s20 [g14]
def p392 := cutPrefix s2 [g9, g34]
def p393 := cutPrefix s6 [g9, g8, g34]
def p394 := cutPrefix s7 [g34]
def p395 := cutPrefix s13 [g9, g8]
def p396 := cutPrefix s11 [g8, g34]
def p397 := cutPrefix s14 [g1]
def p398 := cutPrefix s4 [g16, g14, g15]
def p399 := cutPrefix s9 [g15]
def p400 := cutPrefix s2 [g16, g15]
def p401 := cutPrefix s7 [g15]
def p402 := cutPrefix s6 [g16, g14, g15]
def p403 := cutPrefix s3 [g14, g15]
def g105 : Choice := (3,0xff00ff00ff0000,0xcccccccccccccccc)
def p404 := cutPrefix s4 [g9, g104, g105]
def p405 := cutPrefix s2 [g9, g104]
def p406 := cutPrefix s6 [g9, g104, g105]
def p407 := cutPrefix s7 [g105]
def p408 := cutPrefix s13 [g9, g105]
def p409 := cutPrefix s11 [g104, g105]
def p410 := cutPrefix s9 [g105]
def p411 := cutPrefix s14 []
def p412 := cutPrefix s14 [g104]
def p413 := cutPrefix s0 [g105]
def w73 := combineObserved 3 w72 w1
def p414 := cutPrefix s4 [g35]
def p415 := cutPrefix s2 [g35]
def g106 : Choice := (1,0xcccccccccccccccc,0xff00ff00ff00ff00)
def p416 := cutPrefix s4 [g106]
def p417 := cutPrefix s6 [g3, g35]
def p418 := cutPrefix s4 [g38]
def p419 := cutPrefix s2 [g38]
def p420 := cutPrefix s6 [g3, g38]
def p421 := cutPrefix s4 [g40]
theorem s23 : Slice true R T 0x30303030 4 :=
  slice_correct (ms := fixRows 34 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B48.low
def p422 := cutPrefix s23 []
def p423 := cutPrefix s6 [g3, g40]
def g107 : Choice := (0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00)
def p424 := cutPrefix s2 [g107]
def p425 := cutPrefix s4 [g107]
def p426 := cutPrefix s5 [g3]
def g108 : Choice := (1,0x4444444444444444,0xf000f000f000f000)
def p427 := cutPrefix s6 [g3, g108]
def g109 : Choice := (2,0x4444444444444444,0xf000f000f000f000)
def p428 := cutPrefix s6 [g3, g109]
def p429 := cutPrefix s6 [g3]
def p430 := cutPrefix s11 [g107]
def p431 := cutPrefix s3 [g107]
def p432 := cutPrefix s3 [g3, g107]
def g110 : Choice := (2,0xcccccccccccccccc,0xf000f000f000f000)
def p433 := cutPrefix s6 [g3, g110]
def g111 : Choice := (1,0xf000f000f000f000,0xffff0000ffff0000)
def p434 := cutPrefix s6 [g3, g111]
def p435 := cutPrefix s7 [g3]
def w74 := combineObserved 0 w2 w3
def g112 : Choice := (1,0xf0f00000f0f0,0x4444444444444444)
def p436 := cutPrefix s6 [g3, g112]
def g113 : Choice := (3,0xf0f00000f0f0,0x4444444444444444)
def p437 := cutPrefix s6 [g3, g113]
def g114 : Choice := (2,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000)
def p438 := cutPrefix s4 [g114]
def p439 := cutPrefix s2 [g114]
def g115 : Choice := (1,0xf0f00000f0f0,0xff00ff00ff00ff00)
def p440 := cutPrefix s6 [g3, g115]
def p441 := cutPrefix s3 [g3, g114]
def p442 := cutPrefix s13 [g114]
def p443 := cutPrefix s3 [g114]
def p444 := cutPrefix s2 [g0]
def p445 := cutPrefix s5 [g0]
def p446 := cutPrefix s6 [g0]
def p447 := cutPrefix s3 [g0]
def p448 := cutPrefix s3 [g3, g0]
def p449 := cutPrefix s2 [g1]
def p450 := cutPrefix s4 [g1]
def p451 := cutPrefix s5 [g1]
def p452 := cutPrefix s6 [g1]
def p453 := cutPrefix s3 [g1]
def p454 := cutPrefix s3 [g3, g1]
def p455 := cutPrefix s2 [g11]
def p456 := cutPrefix s3 [g3, g11]
def p457 := cutPrefix s5 [g11]
def p458 := cutPrefix s6 [g11]
def p459 := cutPrefix s3 [g11]
def p460 := cutPrefix s6 [g3, g16]
def p461 := cutPrefix s6 [g66]
def p462 := cutPrefix s5 [g66]
def g116 : Choice := (1,0x5050505050505050,0xcc00cc00cc00cc00)
def p463 := cutPrefix s6 [g66, g116]
def p464 := cutPrefix s2 [g6]
def p465 := cutPrefix s11 [g66]
def g117 : Choice := (1,0x5050505050505050,0xffff0000ffff0000)
def p466 := cutPrefix s6 [g66, g117]
def p467 := cutPrefix s3 [g66]
def p468 := cutPrefix s3 [g6, g66]
def p469 := cutPrefix s3 [g6]
def p470 := cutPrefix s9 [g6]
def p471 := cutPrefix s7 [g66]
def p472 := cutPrefix s5 [g40]
def g118 : Choice := (1,0xcccc0000cccc,0x5050505050505050)
def p473 := cutPrefix s6 [g40, g118]
def g119 : Choice := (2,0xcccc0000cccc,0x5050505050505050)
def p474 := cutPrefix s6 [g40, g119]
def p475 := cutPrefix s6 [g40]
def p476 := cutPrefix s3 [g6, g40]
def p477 := cutPrefix s13 [g40]
def g120 : Choice := (1,0x5050505050505050,0xff00ff00ff00ff00)
def p478 := cutPrefix s6 [g40, g120]
def p479 := cutPrefix s6 [g40, g117]
def p480 := cutPrefix s3 [g40]
def p481 := cutPrefix s6 [g0, g7]
def g121 : Choice := (1,0x5050505050505050,0xff000000ff000000)
def p482 := cutPrefix s6 [g0, g121]
def p483 := cutPrefix s3 [g6, g0]
def p484 := cutPrefix s7 [g0]
def p485 := cutPrefix s6 [g1, g7]
def p486 := cutPrefix s6 [g1, g120]
def p487 := cutPrefix s6 [g1, g117]
def p488 := cutPrefix s6 [g1, g43]
def p489 := cutPrefix s6 [g1, g44]
def p490 := cutPrefix s3 [g6, g1]
def g122 : Choice := (1,0xff000000ff00,0x5050505050505050)
def p491 := cutPrefix s6 [g11, g122]
def p492 := cutPrefix s3 [g6, g11]
def p493 := cutPrefix s6 [g11, g7]
def p494 := cutPrefix s6 [g11, g117]
def p495 := cutPrefix s5 [g10]
def p496 := cutPrefix s6 [g10, g18]
def p497 := cutPrefix s6 [g10, g46]
def p498 := cutPrefix s6 [g10, g47]
def p499 := cutPrefix s6 [g10, g55]
def p500 := cutPrefix s6 [g10, g57]
def p501 := cutPrefix s3 [g10, g23]
def p502 := cutPrefix s3 [g23]
def p503 := cutPrefix s4 [g45]
def p504 := cutPrefix s6 [g48]
def p505 := cutPrefix s5 [g48]
def p506 := cutPrefix s3 [g48, g66]
def p507 := cutPrefix s3 [g10, g40]
def p508 := cutPrefix s6 [g10, g24]
def p509 := cutPrefix s14 [g10]
def p510 := cutPrefix s13 [g63]
def p511 := cutPrefix s6 [g10, g64]
def p512 := cutPrefix s6 [g10, g71]
def g123 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xf000f000f000f000)
def p513 := cutPrefix s6 [g48, g123]
def p514 := cutPrefix s6 [g48, g110]
def p515 := cutPrefix s3 [g48, g107]
def p516 := cutPrefix s6 [g48, g111]
def g124 : Choice := (1,0xf000f000f000f000,0xffffaaaaffffaaaa)
def p517 := cutPrefix s6 [g48, g124]
def g125 : Choice := (3,0xf000f000f000f000,0xffffaaaaffffaaaa)
def p518 := cutPrefix s6 [g48, g125]
def g126 : Choice := (3,0xf0f00000f0f0,0xcccccccccccccccc)
def p519 := cutPrefix s6 [g10, g126]
def p520 := cutPrefix s6 [g10, g115]
def p521 := cutPrefix s6 [g10, g78]
def g127 : Choice := (3,0xf0f00000f0f0,0xffaaffaaffaaffaa)
def p522 := cutPrefix s6 [g10, g127]
def p523 := cutPrefix s3 [g10, g114]
def p524 := cutPrefix s2 [g48, g49]
def p525 := cutPrefix s6 [g48, g49]
def g128 : Choice := (1,0xaaaaaaaaaaaaaaaa,0xffffffffff00ff00)
def p526 := cutPrefix s3 [g128]
def p527 := cutPrefix s6 [g10, g16]
def p528 := cutPrefix s4 [g81]
def p529 := cutPrefix s11 [g81]
def p530 := cutPrefix s2 [g48, g81]
def p531 := cutPrefix s3 [g48, g81]
def p532 := cutPrefix s6 [g48, g81]
def p533 := cutPrefix s6 [g10, g56]
def p534 := cutPrefix s6 [g10, g13]
def p535 := cutPrefix s6 [g10, g9]
def g129 : Choice := (3,0x5555000055550000,0xcccccccccccccccc)
def p536 := cutPrefix s4 [g129]
def p537 := cutPrefix s2 [g85]
def p538 := cutPrefix s6 [g85, g129]
def p539 := cutPrefix s3 [g85, g129]
def w75 := combineObserved 3 w60 w1
def g130 : Choice := (1,0x5555000055550000,0xff00ff00ff00ff00)
def p540 := cutPrefix s4 [g130]
def p541 := cutPrefix s3 [g85, g130]
def p542 := cutPrefix s2 [g85, g130]
def p543 := cutPrefix s6 [g85, g130]
def p544 := cutPrefix s13 [g85]
def w76 := combineObserved 1 w60 w3
def g131 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00)
def p545 := cutPrefix s5 [g131]
def g132 : Choice := (1,0x5500550055005500,0xc0c0c0c0c0c0c0c0)
def p546 := cutPrefix s6 [g131, g132]
def p547 := cutPrefix s2 [g131]
def p548 := cutPrefix s6 [g131]
def p549 := cutPrefix s9 [g23]
def p550 := cutPrefix s3 [g131, g23]
def p551 := cutPrefix s6 [g131, g46]
def p552 := cutPrefix s11 [g131]
def p553 := cutPrefix s6 [g131, g57]
def p554 := cutPrefix s3 [g131]
def p555 := cutPrefix s7 [g131]
def w77 := combineObserved 3 w0 w3
def p556 := cutPrefix s9 [g131]
def p557 := cutPrefix s6 [g131, g24]
def p558 := cutPrefix s14 [g131]
def g133 : Choice := (1,0xf0f00000f0f0,0x5500550055005500)
def p559 := cutPrefix s6 [g131, g133]
def p560 := cutPrefix s6 [g131, g126]
def p561 := cutPrefix s3 [g131, g114]
def p562 := cutPrefix s9 [g114]
def p563 := cutPrefix s10 [g131]
def p564 := cutPrefix s2 [g131, g1]
def p565 := cutPrefix s6 [g131, g1]
def g134 : Choice := (1,0x5500550055005500,0xffff0000ffff0000)
def p566 := cutPrefix s4 [g134]
def p567 := cutPrefix s3 [g131, g1]
def p568 := cutPrefix s2 [g131, g9]
def p569 := cutPrefix s6 [g131, g9]
def p570 := cutPrefix s6 [g0, g18]
def p571 := cutPrefix s6 [g0, g86]
def p572 := cutPrefix s3 [g23, g0]
def p573 := cutPrefix s6 [g1, g18]
def p574 := cutPrefix s6 [g1, g46]
def p575 := cutPrefix s6 [g1, g57]
def p576 := cutPrefix s6 [g1, g52]
def p577 := cutPrefix s6 [g1, g53]
def p578 := cutPrefix s3 [g23, g1]
def p579 := cutPrefix s6 [g11, g54]
def p580 := cutPrefix s3 [g23, g11]
def p581 := cutPrefix s6 [g11, g18]
def p582 := cutPrefix s6 [g11, g46]
def p583 := cutPrefix s6 [g11, g57]
def g135 : Choice := (1,0xcccc0000cccc0000,0xff00ff00ff00ff00)
def p584 := cutPrefix s4 [g67, g135]
def p585 := cutPrefix s2 [g135]
def p586 := cutPrefix s6 [g67, g135]
def p587 := cutPrefix s13 [g67]
def p588 := cutPrefix s3 [g67, g135]
def w78 := combineObserved 1 w24 w3
def p589 := cutPrefix s6 [g66, g92]
def g136 : Choice := (1,0xf0f00000f0f0,0xcc00cc00cc00cc00)
def p590 := cutPrefix s6 [g66, g136]
def p591 := cutPrefix s3 [g66, g114]
def p592 := cutPrefix s6 [g66, g9]
def p593 := cutPrefix s9 [g66]
def g137 : Choice := (1,0xcccc0000cccc,0xaaaaaaaaaaaaaaaa)
def p594 := cutPrefix s2 [g137]
def p595 := cutPrefix s3 [g40, g137]
def p596 := cutPrefix s6 [g40, g137]
def p597 := cutPrefix s11 [g137]
def w79 := combineObserved 1 w17 w0
def g138 : Choice := (1,0xcccc0000cccc,0xff00ff00ff00ff00)
def p598 := cutPrefix s4 [g40, g138]
def p599 := cutPrefix s2 [g138]
def p600 := cutPrefix s6 [g40, g138]
def p601 := cutPrefix s11 [g138]
def p602 := cutPrefix s3 [g40, g138]
def p603 := cutPrefix s2 [g41]
def w80 := combineObserved 1 w17 w3
def g139 : Choice := (2,0xcccc0000cccc,0xff00ff00ff00ff00)
def p604 := cutPrefix s4 [g40, g139]
def p605 := cutPrefix s2 [g139]
def p606 := cutPrefix s6 [g40, g139]
def p607 := cutPrefix s3 [g40, g139]
def p608 := cutPrefix s11 [g139]
def w81 := combineObserved 2 w17 w3
def p609 := cutPrefix s4 [g40, g98]
def p610 := cutPrefix s9 [g40]
def p611 := cutPrefix s6 [g40, g98]
def p612 := cutPrefix s11 [g98]
def g140 : Choice := (1,0xcccc0000cccc,0xf000f000f000f0)
def p613 := cutPrefix s6 [g40, g140]
def g141 : Choice := (2,0xcccc0000cccc,0xf000f000f000f0)
def p614 := cutPrefix s6 [g40, g141]
def g142 : Choice := (2,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00)
def p615 := cutPrefix s4 [g142]
def p616 := cutPrefix s11 [g142]
def p617 := cutPrefix s2 [g142]
def p618 := cutPrefix s3 [g142]
def p619 := cutPrefix s3 [g40, g142]
def p620 := cutPrefix s9 [g142]
def g143 : Choice := (1,0xf000f000f000f0,0xaaaaaaaaaaaaaaaa)
def p621 := cutPrefix s6 [g40, g143]
def g144 : Choice := (1,0xf000f000f000f0,0xffff0000ffff0000)
def p622 := cutPrefix s6 [g40, g144]
def w82 := combineObserved 2 w2 w3
def p623 := cutPrefix s21 [g16]
def p624 := cutPrefix s6 [g40, g16]
def p625 := cutPrefix s4 [g40, g9]
def p626 := cutPrefix s6 [g40, g9]
def p627 := cutPrefix s9 [g0]
def p628 := cutPrefix s6 [g24, g0]
def p629 := cutPrefix s4 [g24, g1]
def p630 := cutPrefix s9 [g1]
def p631 := cutPrefix s6 [g24, g1]
def p632 := cutPrefix s9 [g11]
def p633 := cutPrefix s6 [g24, g11]
def p634 := cutPrefix s14 [g11]
def g145 : Choice := (2,0xcccccccccccccccc,0xff000000ff000000)
def p635 := cutPrefix s4 [g0, g145]
def p636 := cutPrefix s6 [g0, g145]
def p637 := cutPrefix s3 [g0, g145]
def w83 := combineObserved 2 w1 w6
def g146 : Choice := (3,0xaaaaaaaaaaaaaaaa,0xffffff00ffffff00)
def p638 := cutPrefix s2 [g1, g146]
def p639 := cutPrefix s6 [g1, g146]
def p640 := cutPrefix s11 [g146]
def p641 := cutPrefix s13 [g146]
def p642 := cutPrefix s3 [g1, g146]
def w84 := combineObserved 3 w0 w7
def p643 := cutPrefix s6 [g1, g102]
def p644 := cutPrefix s13 [g102]
def p645 := cutPrefix s11 [g102]
def p646 := cutPrefix s3 [g1, g102]
def p647 := cutPrefix s4 [g1, g16]
def p648 := cutPrefix s2 [g1, g16]
def p649 := cutPrefix s6 [g1, g16]
def g147 : Choice := (1,0xffff0000ffff0000,0xffffffffff00ff00)
def p650 := cutPrefix s3 [g147]
def p651 := cutPrefix s4 [g1, g31]
def p652 := cutPrefix s2 [g1, g31]
def p653 := cutPrefix s6 [g1, g31]
def p654 := cutPrefix s11 [g31]
def p655 := cutPrefix s6 [g11, g87]
def p656 := cutPrefix s11 [g87]
def g148 : Choice := (3,0xff000000ff0000,0xcccccccccccccccc)
def p657 := cutPrefix s4 [g79, g148]
def p658 := cutPrefix s2 [g79]
def p659 := cutPrefix s6 [g79, g148]
def p660 := cutPrefix s13 [g148]
def p661 := cutPrefix s3 [g79, g148]
def w85 := combineObserved 3 w27 w1
def g149 : Choice := (1,0xff000000ff00,0xffff0000ffff0000)
def p662 := cutPrefix s4 [g11, g149]
def p663 := cutPrefix s3 [g11, g149]
def p664 := cutPrefix s2 [g11, g149]
def p665 := cutPrefix s6 [g11, g149]
def p666 := cutPrefix s4 [g11, g9]
def p667 := cutPrefix s2 [g11, g9]
def p668 := cutPrefix s6 [g11, g9]
theorem s24 : Slice true R T 0xcc00cc 4 :=
  slice_correct (ms := fixRows 40 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B18.low
def p669 := cutPrefix s24 []
def p670 := cutPrefix s6 [g7]
def p671 := cutPrefix s6 [g120]
def p672 := cutPrefix s6 [g117]
def p673 := cutPrefix s6 [g18]
def p674 := cutPrefix s6 [g46]
def p675 := cutPrefix s6 [g57]
def p676 := cutPrefix s6 [g123]
def p677 := cutPrefix s6 [g110]
def p678 := cutPrefix s6 [g111]
def p679 := cutPrefix s6 [g92]
def p680 := cutPrefix s6 [g126]
def p681 := cutPrefix s6 [g115]
def data0 : Array Nat := #[fourWords 0x5c5cf28014100248 0xd6006d66585aa001 0xf099b40f04a84621 0x4b92f0305080c101, fourWords 0x8101820218284060 0x808b0c1420304045 0x56c0088700e400f0 0x9646c357338cdf66, fourWords 0xa10182026c30508 0xc10124182840608 0xa810c14203049008 0x60a1018203383051, fourWords 0x10c1420304047061 0x142030404305081 0xc182021828406080 0xb20c142039608080, fourWords 0x978428a82728ae38 0x8c21972e61782a09 0xc230868482cd190a 0x5c8e000f85080c10, fourWords 0x860c8024288c0017 0x90dc345c8a910978 0x4289c230862a1025 0x881e5c9e34bd2d4a, fourWords 0xc218325c88c00178 0xe2170428a8e55354 0xcd30a29785c8a827 0x1202308642bda270, fourWords 0x230a8d2b245e28a6 0x9990428320c9722a 0x8c218025e2100b0 0x22273a4ce10aeb89, fourWords 0xe172428a8a282227 0x35cd6886233654ed 0x394d89c2183200a8 0xa5c90a00178cfb40, fourWords 0x978078000889cdd8 0xa8dc372de0860c97 0x24288c5e36ad989c 0x8c0a8db5414fd3c5, fourWords 0x5a5e28a2a0a60d0b 0x20c8860c9724288c 0x5e02227382df1262 0xa3840c9724288c21, fourWords 0x8584401eacdb462f 0x99b6491be2362fc6 0x779d7b83b1a3dac1 0xad58b5a8eb526d68, fourWords 0xb18a81e98e0129e4 0x4c63c80bd4623864 0xb0b8711a72e580c9 0x41816034639d05a2, fourWords 0x8de4282ed32b9dd0 0x2231abdd0ec2b 0xd14cbb8b0982d01b 0x80015981126b80b0, fourWords 0x1090b720b8c09b69 0xa628f8bd3a8ac3c9 0x7db89a5a8f3942b4 0x503003912408bb20, fourWords 0x20529339b34ac4 0xda4b041b38b5d0cb 0x2b62d6080918a7e1 0xba5429a00021d23, fourWords 0x19c8 0x1ba16818 0x200004dc05433878 0x1b29ca37c80018d0, fourWords 0x22c2fe000 0x528000000000 0x5906b8a28002d 0x82223eb1f413b000, fourWords 0x2289000c14203040 0x5a000c1598406080 0x962bc8239211c1db 0xad09e0002c800000, fourWords 0x101420304045060a 0x1038304045060a10 0x18202299060a101c 0xb04045000c142030, fourWords 0x304045860a101820 0x22c9060a101822a0 0x45803e1420304045 0x60a101820228706, fourWords 0x800c142030434086 0xa3020304900860a 0x10182022c7061014 0x20304045860a1038, fourWords 0x2033c080800a3020 0x30404d860a302030 0x4049063014203045 0x40860a3020304340, fourWords 0x80800c1460304047 0xc20c040608086 0xa30203040590630 0x1420396080860a30, fourWords 0x3020304048000c14 0x20304048000cd828 0x40608086301423a0 0x6080803e14604060, fourWords 0x338d860a10182480 0x67000c1668406080 0x800c142030406600 0x221460406080860a, fourWords 0xa10383049008022 0x1420304067000c20 0x28304067060a1018 0x203399000a101820, fourWords 0x22a059000c167840 0x6080800c142032c0 0x80860a1018248047 0x610142030490086, fourWords 0x800c142030406900 0xc1688406080800c 0x1420305400802214 0x20304540860a1018, fourWords 0x3830404d80221420 0x304049003e142030 0x4049060a10182034 0xc9000a1018202489, fourWords 0x80800c142030406a 0xc152840608080 0xa101820238d8010 0x142030404d800a10, fourWords 0x2028406080803e20 0x28406080800c1420 0x3051c0800c142030 0x406a800018407060]
def data1 : Array Nat := #[fourWords 0x4047000018182027 0x7000c2028406080 0x800c142030558080 0xc1420304fc0805a, fourWords 0x708c218c65c81ecc 0x212cb32a27800014 0x2030405a80001420 0x3048008022142030, fourWords 0xb3c0b3382f33807b 0x3a5e0a823086848c 0xe08b360b334cc8b0 0xcb90a0b022009782, fourWords 0xce00b4ad2344d0b3 0xa5c88c428e02a346 0xd034ccf8c63707ec 0xe89c2f972428ce84, fourWords 0xe338bed9362d6356 0xd4b3a5c90a380c62 0x708c08886d535cd8 0x346d6b52d434e388, fourWords 0x31a120882cdc37ad 0xcb5438b6cdab68d1 0xa125c89c428e00b0 0xce2a3668c36e31b5, fourWords 0xb0a8df37e498c638 0x8dc330b800b78ddb 0x74d53462f8a82707 0xe078005c90a380ce, fourWords 0xac1f82cd48c6e18 0xe20d0b2d50e2370c 0xe2f87ee1382e0346 0x8497227022428e00, fourWords 0x9ae4b8a3e0dce539 0x5c90ae638c23086 0xe20a85c396e38ee2 0xd8a8298a40c81e38, fourWords 0x43bbaceab9acc8f8 0xebba8e8ba05c90a3 0xb89c1fb98a308c21 0xba4ce39ee9b8ee73, fourWords 0x232dc21b76f0b74d 0xcbb6ecbb0e6b3ae3 0xb6cd997227398da0 0x8c218f82a36a8c3b, fourWords 0x608c21b802a38249 0xbc63bbbceebb8e6b 0x3a1fbc0efb8ede37 0x5c8a8273983e0ee, fourWords 0x93647972428a8230 0x8640bd858920f3bc 0xaf23c4e6b3a3e07e 0xe3b84df2ec5c89ce, fourWords 0x6242822ce9782708 0xc21954079724302c 0x58bdc55bd6f302cf 0x6bd4f4bd0929e878, fourWords 0xce210a2721c5c822 0x850a8f8970451544 0x282c00bce7893643 0x1023717207956f71, fourWords 0xe939e7e172429022 0xa1e22702200a1037 0x2c07be4ce162f83 0x90cd218003dee538, fourWords 0x7bce6f1b840802fa 0x1a66918e42832788 0x58079e8f99e05899 0xea33278136f3bae, fourWords 0xb3ecea1e8509c232 0x1c5c8a8fd3ded011 0x4fbbecfa9e023086 0x589604d9e8789720, fourWords 0x64d733a7e1e25c96 0x22a08c7a09c08886 0xf3c0440b5afcbf0f 0x8348863fafe3f6d2, fourWords 0xe4d9ae598a849994 0x1fb72770a85c9142 0x74090182244186ff 0xbfcd893637403003, fourWords 0x8c0f05115028025 0xe0b6298a40d0007a 0x1e207c0c2a1e0530 0xb2508dc5c89c7e01, fourWords 0x510a230860b3724d 0x81f061a20892e66c 0x10f821807c1704bd 0xe850a82721c00972, fourWords 0x9020893637172079 0xa8508a85e10a2308 0x60b1464d81e5cc1a 0x5a022509a85e1324, fourWords 0x96250320881c7889 0xc3701e991e84dc1c 0x579e0241f85192e2 0xa09d06bce7896858, fourWords 0x30b42a0009d09c28 0xceb328410a0c8020 0xa8230865e17308 0x82c2742107c24000, fourWords 0x5c90a21802f688d0 0xcc362a43b0d12047 0xb725092e0c822428 0x8c2182c009790b97, fourWords 0x435ad8c4ac91a463 0xc446990a00c420cc 0x490d446161911144 0x10f4390c24b10c3e, fourWords 0x1164562a373174 0x5514c4f1343ece89 0xc08c4510c350cb5c 0x5c88c21b642a4371, fourWords 0x1e2709408c450f89 0x607002004420cc61 0x17c4699091169264 0x409c07c3e5c80315, fourWords 0xc00a4a47886ddc72 0xdc375194630e36c8 0xc1204289c21bdada 0x8c928a8dac66d99, fourWords 0x273da4288c21b80e 0x8a91db7c47c690e 0x4711bc6d1ab78dc9 0x2042bdab70a82708, fourWords 0xb1782708c21822f7 0x5c96e2a2585c2 0x531f47b1e4750e2e 0xc0b002e124a49920]
def data2 : Array Nat := #[fourWords 0x8a92335ce236309b 0x70ca9421f8325c88 0xc2181e5e10b21483 0x1f800274812190a0, fourWords 0x9ce4096243940cc8 0xe984909901d22c89 0x14b9ce409c08b94d 0x697042b8cd908c21, fourWords 0x1274a30833242832 0xb01f078a8230872 0x61780097325a1124 0xb392509c25022003, fourWords 0x7ba92aca60b4a92 0xb4a52032a2a09c0c 0xca05c88c2182c5e1 0xa1f81eea49f26a1, fourWords 0xe002c928a373af2d 0xa8c8402d2d4b32c2 0x9120210190325c88 0xc2187f2bb705e022, fourWords 0x83532cc931cbeea0 0x32f4bb2e3aeceb3 0x8428a82708c07cc2 0xa3086e7cc4e94c05, fourWords 0x2ca32113489d2cba 0xf3401c2c8a62901e 0xbae2a0320b0233 0x30b6a33a9338b52c, fourWords 0x136bb6c91a469990 0x42b6c0c98f35aa41 0x6367352900080099 0xdc25894240225e0, fourWords 0x6383338198df0593 0x7ca8c905a079a669 0x19042822de3080c8 0x2b718e164dd3637, fourWords 0x9ce9039425e10a23 0x860b1728caa8270 0xa88c2a738b246902 0x200aec6999042b84, fourWords 0x800dccf208800310 0xc00f0a83241eceb2 0xa190325c90a23086 0x5e02d3989d390a8d, fourWords 0xb3e0013dcf40b2c 0xcdc4fb099424b89c 0xc90a230860b1780 0xcee5ccf008ced3a, fourWords 0xe0d178078b6b7022 0x379404ff3f4da2 0xa4a8f733a2a09c0c 0xc805c88c218225e1, fourWords 0xae0a849ab45e07e0 0x7802a2b78b750a00 0x2ca08cdb42507410 0x3200d022c8a62907, fourWords 0x41724288c2181e5e 0x5174509d4402d44d 0x188c50e5e10a2308 0x60b1425c8dc08d0c, fourWords 0x90a230861f8025e3 0x78dc0234837347d1 0xa270a9474a527481 0x7bdcd9b3a0c8028, fourWords 0x90070025e0dce109 0xd49cdf49522990d8 0x340d4270a836d032 0x71424b91007c805c, fourWords 0xc0c9f4088ea2da8a 0x3a0de390325e1e60 0xb1de00a8a0e0300d 0x378b28940caec258, fourWords 0x4508b04f4b64d93b 0x4b7724a0f6485754 0x6b2d45aef4483143 0x2f4a378370025e07, fourWords 0x64b3662fb161a6f6 0x7b85e9b35d1ef5b 0xf2f5ac76590f6575 0x785577453e77521b, fourWords 0x5cef74a3572ff371 0x832701b16ec726d5 0xef6c32f6b07169b3 0x6872c6782c66938, fourWords 0xf338777585d33845 0x6f832b4819b3801e 0xf7ef377d2777b5b2 0x79f3078b2f778767, fourWords 0x7498f759753495c2 0x79537193e2e92cb1 0x917748fe6e8ecf38 0xd5328beb88a0ae88, fourWords 0xb45280581d976fc3 0x6aa4f8d0efa346aa 0x27f2a1166a09f89e 0xbf79cf309bb2f9a8, fourWords 0xcacc24f26ed91 0xe12ca2af0b8320b2 0x2d91960e3b559950 0x99232c38f01b935f, fourWords 0x904ac4000000000 0x6a80000000000009 0xe843600000061723 0x87aee4cbe4ea85c8, fourWords 0x6a5e613400022334 0xcfea000804946d08 0x8f20ee8800000000 0x6961645371ae00, fourWords 0x9643608612 0xa80000d0daa9a21f 0x2df0ae90264b8278 0xa588ca001174fa06, fourWords 0x8e848ac2ed0f8ef6 0x769074b94000d 0x3846a64600002eba 0xb296736099128000, fourWords 0x726f65986328224f 0x73d52e6000a281a4 0xf61276c6e7f22c03 0xeab54074a763b60a, fourWords 0x11400f85080c08a 0x2400f85080c10168 0x88566101820218 0x2b3080c10165360d, fourWords 0x303040459c1c0030 0x80e0c10116002840 0x60808a6a00303040 0x451c1c003080e0c1]
def data3 : Array Nat := #[fourWords 0x92012019b05080c1 0x24021828c0609201 0x1c18418080c12402 0x1828c080c6a40200, fourWords 0x1828c06086811c18 0x284067810d020088 0x5080c10d0200f850 0x80c10d0218284060, fourWords 0x80c1016e00305080 0xc1016e003180a101 0x96044428c080c10d 0x218284060868120, fourWords 0x360028c060808e36 0x418080c1013618 0x6040608c81200030 0x40608c81201828c0, fourWords 0x8080cf02021828c0 0x6781011c14604060 0x8090360028406080 0x903601b05080c101, fourWords 0x820218638080c101 0x641860406e410120 0x30406e41012018 0x284067810120182b, fourWords 0xf980ae8182020028 0xc080c1016a00f850 0x80c101200028c080 0xc120020031808741, fourWords 0xc13e0200c05080c1 0x20020088c080c101 0x2018c05080c13c02 0x11080c1012000, fourWords 0x303049009c1c18 0x284060923f020030 0x80e0c12402182a50 0x80c1240200005080, fourWords 0x6581016418284065 0x81012e1a105080cb 0x202182840668101 0x8218284065a00202, fourWords 0x8c00005080ca0124 0x118a101820200 0x5080c101860088 0x5080cb0202182840, fourWords 0x30404e0e36002840 0x609f8136000080e0 0xc10136002a5080c1 0x13600005080c101, fourWords 0x8202182a5080c101 0x52182a5080d40202 0x182a5080c1014e18 0x2a5080c126020000, fourWords 0x305080e402020002 0xd101c18202000061 0xc10112000000c0 0xc101120000610941, fourWords 0xc120020000560101 0x82020028406b8120 0x20000506080c91c 0x8080c1016a00, fourWords 0x220781c2789c2609 0x625032268922408e 0x2308a22086000050 0x80c14a0201085080, fourWords 0x60f0be2e07e2f0ba 0x2d8ac2d0342c82c2 0x80222c0ac2a8a629 0x322b8a82882c0b0, fourWords 0x787e390de368d83 0x58a8270d0350d233 0x8c6330be320c4308 0xa81f822000c0328c, fourWords 0xb8d43e8f23c0ec1f 0x8f6320c02a0c43b8 0xc23d03c2f8ea3a0e 0x6388e0370b61f022, fourWords 0x11e4711a46116451 0x124410e4310a4190 0x440900420fe3f0da 0x358d02a09c360f83, fourWords 0x3e4f136230285208 0x64e9384d9344c930 0x4b92c4288c0b0864 0xa92849924488a848, fourWords 0x625032540905795a 0xb15855152538345 0x59502d8a62902c53 0x14a2c94651142501, fourWords 0x9684d90a2702c0 0x8962599645815654 0x10a4210223086589 0x5c5481e071562709, fourWords 0xa09c5c9682a0005e 0x136230865d9745c9 0xa5e9705b89c0016 0xc5a8a84515e0b01c, fourWords 0x9906385862988619 0x8e160226418c6093 0x62701e609800897e 0x5f10a001844d9742, fourWords 0xa66910a0c8285a02 0x2641ac099a0079a6 0x691a26719a428326 0x7822661960799464, fourWords 0xc6e9b86d9b46c9b0 0x2708c07902219ae6 0x51926b1906382608 0x81e5f858079aa6a1, fourWords 0x60936271ce731c67 0x98252028721c423 0x1ca4d9c06c1a84d8 0x8c0a026408866f9b, fourWords 0xf1ea799e40e0360d 0x1e789de0c14c771 0xd84507e270227697 0x2759d4721d2741cc, fourWords 0x1e7c8ea391f07b1 0xce2a028001a8518a 0x6290340b0227b8b2 0x99ec7a1e0370ac1, fourWords 0xa822067f204809f 0xe0091408a007e9f8 0x7c158088027d9f47 0x89e03a0e6378b61f, fourWords 0xc789360a02407826 0x82a1484a105c9144 0x28a80b2165e02207 0xa0e6a0288302409a]
def data4 : Array Nat := #[fourWords 0x1f22a898b688a208 0x7a187a8a2870380d 0x81e009de1f8340b0 0x2286830839a82720, fourWords 0xe0f6008c80f0a831 0x240308c047a368d2 0x328c22e4288c0b08 0x68b0325e02c8a224, fourWords 0x8c2196e938da358 0xd42a09c3624c9291 0xe3424891a4490926 0x2a08c21a3e8f23a8, fourWords 0x5e9725a5c16e2708 0xc088865c0a827022 0x2582707e088009 0x5a542308694a505c, fourWords 0x25e2701f26c9c8b6 0x9ba689aa665682c0 0x70009489c258940c 0x8229426498890982, fourWords 0xa6294a5a8a37210a 0x4a90a3288a3a860b 0xdca0178a127e9f2 0x7a9da829e2748803, fourWords 0xb0c0aa9aca99a669 0x10a0caa8642a2638 0x58a929e9a8de0887 0xca8178a6a9ca302c, fourWords 0x2ba342b6a91acae2 0xb4699a4428326602 0x2ac990162b016822 0x8f6322ae1604ea, fourWords 0x3c142c08c88c21aa 0x6a8a30230868caa8 0x428640b2304282ca 0xa0fe3698eaf858af, fourWords 0x8ab2cab1ac4008a8 0x1f80c01022020000 0x38020000c0100803 0x8a81fac20003e150, fourWords 0xb82deb6ad83aad6b 0x52d0088005e17223 0x860b2cc42ad2b3a 0x60087e320f608ac, fourWords 0x92f67a8380d834bc 0x82cbc030372ecbba 0xe2baae8b9a64b922 0x2d87e0787c08adc, fourWords 0x360c02ec53107ab 0x120d02cc3b081f07 0xe0b304c1b0207b00 0x212febf2fabe2f47, fourWords 0xe01ae6f81237acb2 0x8c8afe07802c9b24 0xc831ec702cc6b16c 0x630cbe07c00b0a0e, fourWords 0xcea56b74bd63a229 0x9d0254e74a7735f6 0x3973b5c995ce3b2a 0x71756b879adc2158, fourWords 0x50f1c28789123c34 0xa5e03c8efcec776f 0x43b8f91dbdceed62 0x176a753b21b9d6dd, fourWords 0x5e0fa6f17c8d43e1 0xe8df07ccf7c6c7b6 0xb4bd88b5ea3c6f4e 0x267a357bccfade4c, fourWords 0xc74d05c2b8273441 0x11ba065d3027ac80 0xc584012adfedd2fe 0xbaa7ef95bf45c9f7, fourWords 0x1fadd0ebeb86f16c 0x337ba178d50afea8 0x51b64251c2100d30 0x752583772c1a2920, fourWords 0xa2e853168ec8acf7 0x4521ae2755312f66 0x893f4447792231cd 0x1116488632441da2, fourWords 0xf39d400b5d637db1 0x7196f1658760c0ea 0x9f0128e130069301 0xd1a7708c9b5c616b, fourWords 0x756c118d00096cb6 0x2ac91726b75e14b8 0x6e97cd000354e04b 0x3574d50ae0400000, fourWords 0x840608681201828f 0x608681001818202 0x2c4800c0c1011424 0x15400740000011, fourWords 0x8060a3c19e0404c0 0x43a0c10136186040 0x6681100c602032c0 0x8b8518101941a048, fourWords 0x92010a1018228051 0xa20a101824005098 0x80c120023020304 0x5009000101822804, fourWords 0xc1014e184250609 0x30100001820224d8 0x1094182026c0060 0x6092011218425060, fourWords 0xb0182022400606a 0xc101120030304a80 0x890c212830405486 0x10941a804043084a, fourWords 0x402c07018050000 0x200c010102840608 0xa01621420304800a 0xf000168304044800, fourWords 0x805c160541203c0d 0x50130440f048100 0x3c0e034010340c02 0x4080280700806014, fourWords 0x9827094230880a0 0x407010060900500 0x8210801f0781d064 0xe0701b0640f0681, fourWords 0x103307c280981e07 0xc320a81e0a82f0b4 0x1028070c4300b80 0x20b02b0a8290b428, fourWords 0xc2e00407028000e8 0x390b8380dc360280 0x7010020d40501807 0x180500800004340]
def data5 : Array Nat := #[fourWords 0x5209c5209c5249c5 0xc19c5209c52a9bee 0x89b9e108411003f0 0xf801028000f43c0e, fourWords 0xe29eaa29e9699e3c 0x89decb9d7e59d4c2 0x9d3859d0639ce849 0xcc059c8e19c8409c, fourWords 0x0 0x1a0622a 0x4e99ff489fa499f 0x4a89efa29ee649eb]
def wordAt (i : Nat) : Nat := (if i < 96 then (if i < 32 then data0[i % 32]?.getD 0 else (if i < 64 then data1[i % 32]?.getD 0 else data2[i % 32]?.getD 0)) else (if i < 128 then data3[i % 32]?.getD 0 else (if i < 160 then data4[i % 32]?.getD 0 else data5[i % 32]?.getD 0)))
def countAt : Nat → Nat
  | 6 => 28
  | 7 => 79
  | 8 => 69
  | 9 => 14
  | 10 => 1
  | _ => 0
def rowAt : Nat → Nat → Nat
  | 6, i => packedEntry wordAt (38466+i*49) 49
  | 7, i => packedEntry wordAt (24081+i*56) 56
  | 8, i => packedEntry wordAt (4735+i*56) 56
  | 9, i => packedEntry wordAt (383+i*49) 49
  | 10, i => packedEntry wordAt (0+i*42) 42
  | _, _ => 0
def indexAt : Nat → Nat → Nat
  | 6, tag => let j := (tag / 12 + packedEntry wordAt (37954 + (tag % 12)*6) 6) % 44; packedEntry wordAt (38026 + j*10) 10
  | 7, tag => let j := (tag / 32 + packedEntry wordAt (22429 + (tag % 32)*7) 7) % 119; packedEntry wordAt (22653 + j*12) 12
  | 8, tag => let j := (tag / 32 + packedEntry wordAt (3047 + (tag % 32)*7) 7) % 122; packedEntry wordAt (3271 + j*12) 12
  | 9, tag => let j := (tag / 8 + packedEntry wordAt (91 + (tag % 8)*5) 5) % 28; packedEntry wordAt (131 + j*9) 9
  | _, _ => 0
def candidatesAt : Nat → Nat → Nat → List Nat
  | 6,i,_ => let r := packedEntry wordAt (41068+i*20) 20; readField wordAt (r % 65536) (r / 65536) 10
  | 7,i,_ => let r := packedEntry wordAt (36295+i*21) 21; readField wordAt (r % 65536) (r / 65536) 10
  | 8,i,_ => let r := packedEntry wordAt (21049+i*20) 20; readField wordAt (r % 32768) (r / 32768) 10
  | 9,i,_ => let r := packedEntry wordAt (2809+i*17) 17; readField wordAt (r % 4096) (r / 4096) 10
  | 10,i,_ => let r := packedEntry wordAt (82+i*9) 9; readField wordAt (r % 64) (r / 64) 10
  | _,_,_ => []
def book : Archive R T (asRow P) (asRow N) := ⟨#[w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64, w65, w66, w67, w68, w69, w70, w71, w72, w73, w74, w75, w76, w77, w78, w79, w80, w81, w82, w83, w84, w85], #[(usePool p0), (usePool p1), (usePool p2), (usePool p3), (usePool p4), (usePool p5), (usePool p6), (usePool p7), (joinPools p5 p8), (joinPools p5 p9), (usePool p10), (usePool p11), (joinPools p5 p12), (joinPools p1 p13), (usePool p14), (usePool p15), (usePool p16), (usePool p17), (usePool p18), (usePool p19), (usePool p20), (usePool p21), (usePool p22), (usePool p23), (usePool p24), (usePool p25), (usePool p26), (usePool p27), (usePool p28), (joinPools p29 p30), (usePool p31), (usePool p32), (joinPools p29 p33), (joinPools p29 p34), (joinPools p5 p35), (joinPools p5 p36), (usePool p37), (joinPools p5 p38), (usePool p39), (usePool p40), (usePool p41), (usePool p42), (usePool p43), (usePool p44), (usePool p45), (usePool p46), (usePool p47), (usePool p48), (usePool p49), (usePool p50), (usePool p51), (joinPools p29 p52), (usePool p53), (usePool p54), (joinPools p5 p55), (joinPools p5 p56), (usePool p57), (usePool p58), (usePool p59), (usePool p60), (usePool p61), (usePool p62), (usePool p63), (usePool p64), (usePool p65), (joinPools p66 p67), (usePool p68), (usePool p69), (joinPools p70 p71), (joinPools p70 p72), (usePool p73), (usePool p74), (usePool p75), (usePool p76), (usePool p77), (usePool p78), (usePool p79), (usePool p80), (usePool p81), (usePool p82), (usePool p83), (usePool p84), (usePool p85), (usePool p86), (usePool p87), (joinPools p22 p88), (usePool p89), (usePool p90), (usePool p91), (usePool p92), (usePool p93), (usePool p94), (usePool p95), (usePool p96), (usePool p97), (usePool p98), (usePool p99), (usePool p100), (usePool p101), (usePool p102), (usePool p103), (usePool p104), (usePool p105), (usePool p106), (usePool p107), (usePool p108), (usePool p109), (usePool p110), (usePool p111), (usePool p112), (usePool p113), (usePool p114), (usePool p115), (usePool p116), (usePool p117), (usePool p118), (usePool p119), (usePool p120), (joinPools p100 p121), (usePool p122), (joinPools p100 p123), (joinPools p100 p124), (usePool p125), (usePool p126), (usePool p127), (usePool p128), (joinPools p110 p129), (usePool p130), (joinPools p131 p132), (usePool p133), (joinPools p131 p134), (joinPools p131 p135), (usePool p131), (usePool p136), (usePool p137), (joinPools p138 p139), (usePool p140), (joinPools p138 p141), (usePool p142), (joinPools p138 p143), (joinPools p138 p144), (joinPools p138 p145), (joinPools p138 p146), (usePool p147), (usePool p148), (joinPools p149 p150), (joinPools p149 p151), (usePool p152), (joinPools p149 p153), (joinPools p149 p154), (joinPools p155 p156), (usePool p157), (joinPools p155 p158), (usePool p159), (joinPools p155 p160), (usePool p161), (joinPools p155 p162), (joinPools p155 p163), (joinPools p164 p165), (joinPools p164 p166), (joinPools p164 p167), (usePool p168), (joinPools p164 p169), (usePool p170), (usePool p164), (usePool p171), (usePool p172), (joinPools p22 p173), (usePool p174), (usePool p175), (usePool p176), (usePool p177), (joinPools p178 p15), (usePool p179), (joinPools p22 p180), (usePool p181), (usePool p182), (usePool p183), (joinPools p131 p184), (usePool p185), (usePool p186), (usePool p187), (usePool p188), (usePool p189), (usePool p190), (usePool p191), (usePool p192), (usePool p193), (usePool p194), (usePool p195), (usePool p196), (usePool p197), (usePool p198), (usePool p199), (usePool p200), (usePool p201), (usePool p202), (usePool p203), (usePool p204), (usePool p205), (usePool p206), (usePool p207), (usePool p208), (usePool p209), (usePool p210), (usePool p211), (usePool p212), (usePool p213), (usePool p214), (usePool p215), (usePool p216), (usePool p217), (usePool p218), (usePool p219), (usePool p220), (usePool p221), (usePool p222), (joinPools p223 p224), (usePool p225), (usePool p226), (usePool p227), (usePool p228), (usePool p229), (usePool p230), (joinPools p164 p231), (joinPools p198 p232), (usePool p233), (joinPools p198 p234), (usePool p235), (usePool p236), (joinPools p198 p237), (usePool p238), (joinPools p198 p239), (joinPools p198 p240), (joinPools p223 p241), (usePool p223), (usePool p242), (usePool p243), (usePool p244), (usePool p245), (usePool p246), (usePool p247), (usePool p248), (usePool p249), (usePool p250), (usePool p251), (joinPools p252 p15), (usePool p253), (usePool p254), (usePool p255), (usePool p256), (usePool p257), (usePool p258), (usePool p259), (usePool p260), (usePool p261), (usePool p262), (usePool p263), (usePool p264), (joinPools p0 p17), (usePool p265), (usePool p266), (usePool p267), (usePool p268), (usePool p269), (usePool p270), (usePool p271), (usePool p272), (usePool p273), (usePool p274), (usePool p275), (usePool p276), (usePool p277), (usePool p278), (usePool p279), (usePool p280), (usePool p281), (usePool p282), (usePool p283), (joinPools p284 p285), (usePool p286), (usePool p287), (joinPools p284 p288), (joinPools p284 p289), (joinPools p100 p290), (joinPools p100 p291), (joinPools p100 p292), (joinPools p100 p293), (usePool p294), (joinPools p295 p296), (joinPools p295 p297), (joinPools p295 p298), (joinPools p295 p299), (usePool p300), (usePool p301), (joinPools p110 p302), (usePool p303), (usePool p304), (joinPools p305 p306), (usePool p307), (usePool p308), (joinPools p309 p310), (joinPools p309 p311), (joinPools p309 p312), (usePool p313), (usePool p314), (usePool p315), (usePool p316), (usePool p317), (usePool p318), (usePool p319), (usePool p320), (usePool p321), (usePool p322), (usePool p323), (usePool p324), (usePool p325), (usePool p326), (usePool p327), (usePool p328), (usePool p329), (usePool p330), (usePool p331), (usePool p332), (usePool p333), (usePool p334), (usePool p335), (usePool p336), (usePool p337), (usePool p338), (usePool p339), (usePool p340), (usePool p341), (usePool p342), (usePool p343), (joinPools p22 p344), (usePool p345), (usePool p346), (usePool p347), (usePool p348), (usePool p349), (usePool p350), (usePool p351), (usePool p352), (usePool p353), (usePool p354), (usePool p355), (usePool p356), (usePool p357), (usePool p358), (usePool p359), (usePool p360), (joinPools p284 p361), (usePool p362), (usePool p363), (usePool p364), (usePool p365), (usePool p366), (usePool p367), (usePool p368), (usePool p369), (usePool p370), (joinPools p22 p371), (joinPools p22 p372), (usePool p373), (usePool p374), (usePool p375), (usePool p376), (usePool p377), (usePool p378), (usePool p379), (usePool p380), (usePool p381), (usePool p382), (usePool p383), (usePool p384), (usePool p385), (usePool p386), (usePool p387), (usePool p388), (joinPools p22 p389), (usePool p390), (usePool p391), (usePool p392), (usePool p393), (usePool p394), (usePool p395), (usePool p396), (usePool p397), (usePool p398), (usePool p399), (usePool p400), (usePool p401), (usePool p402), (usePool p403), (usePool p404), (usePool p405), (usePool p406), (usePool p407), (usePool p408), (usePool p409), (usePool p410), (usePool p411), (usePool p412), (usePool p413), (usePool p414), (usePool p415), (usePool p416), (usePool p417), (usePool p418), (usePool p419), (usePool p420), (usePool p421), (usePool p422), (usePool p423), (usePool p424), (usePool p425), (joinPools p426 p427), (joinPools p426 p428), (usePool p429), (usePool p430), (usePool p431), (usePool p432), (joinPools p426 p433), (joinPools p426 p434), (usePool p435), (usePool p426), (joinPools p426 p436), (joinPools p426 p437), (usePool p438), (usePool p439), (joinPools p426 p440), (usePool p441), (usePool p442), (usePool p443), (usePool p444), (usePool p445), (usePool p446), (usePool p447), (usePool p448), (usePool p449), (usePool p450), (usePool p451), (usePool p452), (usePool p453), (usePool p454), (usePool p455), (usePool p456), (usePool p457), (usePool p458), (usePool p459), (usePool p460), (usePool p461), (joinPools p462 p463), (usePool p462), (usePool p464), (usePool p465), (joinPools p462 p466), (usePool p467), (usePool p468), (usePool p469), (usePool p470), (usePool p471), (usePool p472), (joinPools p472 p473), (joinPools p472 p474), (usePool p475), (usePool p476), (usePool p477), (joinPools p472 p478), (joinPools p472 p479), (usePool p480), (joinPools p445 p481), (joinPools p445 p482), (usePool p483), (usePool p484), (joinPools p451 p485), (joinPools p451 p486), (joinPools p451 p487), (joinPools p451 p488), (joinPools p451 p489), (usePool p490), (joinPools p457 p491), (usePool p492), (joinPools p457 p493), (joinPools p457 p494), (joinPools p495 p496), (usePool p495), (joinPools p495 p497), (joinPools p495 p498), (joinPools p495 p499), (joinPools p495 p500), (usePool p501), (usePool p502), (usePool p503), (usePool p504), (usePool p505), (usePool p506), (usePool p507), (usePool p508), (usePool p509), (usePool p510), (joinPools p495 p511), (joinPools p495 p512), (joinPools p505 p513), (joinPools p505 p514), (usePool p515), (joinPools p505 p516), (joinPools p505 p517), (joinPools p505 p518), (joinPools p495 p519), (joinPools p495 p520), (joinPools p495 p521), (joinPools p495 p522), (usePool p523), (usePool p524), (usePool p525), (usePool p526), (usePool p527), (usePool p528), (usePool p529), (usePool p530), (usePool p531), (usePool p532), (usePool p533), (usePool p534), (usePool p535), (usePool p536), (usePool p537), (usePool p538), (usePool p539), (usePool p540), (usePool p541), (usePool p542), (usePool p543), (usePool p544), (joinPools p545 p546), (usePool p545), (usePool p547), (usePool p548), (usePool p549), (usePool p550), (joinPools p545 p551), (usePool p552), (joinPools p545 p553), (usePool p554), (usePool p555), (usePool p556), (usePool p557), (usePool p558), (joinPools p545 p559), (joinPools p545 p560), (usePool p561), (usePool p562), (usePool p563), (usePool p564), (usePool p565), (usePool p566), (usePool p567), (usePool p568), (usePool p569), (joinPools p445 p570), (joinPools p445 p571), (usePool p572), (joinPools p451 p573), (joinPools p451 p574), (joinPools p451 p575), (joinPools p451 p576), (joinPools p451 p577), (usePool p578), (joinPools p457 p579), (usePool p580), (joinPools p457 p581), (joinPools p457 p582), (joinPools p457 p583), (usePool p584), (usePool p585), (usePool p586), (usePool p587), (usePool p588), (joinPools p462 p589), (joinPools p462 p590), (usePool p591), (usePool p592), (usePool p593), (usePool p594), (usePool p595), (usePool p596), (usePool p597), (usePool p598), (usePool p599), (usePool p600), (usePool p601), (usePool p602), (usePool p603), (usePool p604), (usePool p605), (usePool p606), (usePool p607), (usePool p608), (usePool p609), (usePool p610), (usePool p611), (usePool p612), (joinPools p472 p613), (joinPools p472 p614), (usePool p615), (usePool p616), (usePool p617), (usePool p618), (usePool p619), (usePool p620), (joinPools p472 p621), (joinPools p472 p622), (usePool p623), (usePool p624), (usePool p625), (usePool p626), (usePool p627), (usePool p628), (usePool p629), (usePool p630), (usePool p631), (usePool p632), (usePool p633), (usePool p634), (usePool p635), (usePool p636), (usePool p637), (usePool p638), (usePool p639), (usePool p640), (usePool p641), (usePool p642), (usePool p643), (usePool p644), (usePool p645), (usePool p646), (usePool p647), (usePool p648), (usePool p649), (usePool p650), (usePool p651), (usePool p652), (usePool p653), (usePool p654), (usePool p655), (usePool p656), (usePool p657), (usePool p658), (usePool p659), (usePool p660), (usePool p661), (usePool p662), (usePool p663), (usePool p664), (usePool p665), (usePool p666), (usePool p667), (usePool p668), (usePool p669), (joinPools p69 p670), (joinPools p69 p671), (joinPools p69 p672), (joinPools p69 p673), (joinPools p69 p674), (joinPools p69 p675), (joinPools p69 p676), (joinPools p69 p677), (joinPools p69 p678), (joinPools p69 p679), (joinPools p69 p680), (joinPools p69 p681)], #[⟨a0,a0ok⟩, ⟨a1,a1ok⟩], 7, countAt, rowAt, indexAt, candidatesAt⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h6_0 : Span (book.check 6) 0 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h6_8 : Span (book.check 6) 8 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h6_16 : Span (book.check 6) 16 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h6_24 : Span (book.check 6) 24 4 := scan_ok (by decide +kernel)
theorem done6 : Span (book.check 6) 0 28 := (adjacent (adjacent h6_0 h6_8) (adjacent h6_16 h6_24))
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
theorem h7_56 : Span (book.check 7) 56 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_64 : Span (book.check 7) 64 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h7_72 : Span (book.check 7) 72 7 := scan_ok (by decide +kernel)
theorem done7 : Span (book.check 7) 0 79 := (adjacent (adjacent (adjacent (adjacent h7_0 h7_8) (adjacent h7_16 h7_24)) (adjacent (adjacent h7_32 h7_40) (adjacent h7_48 h7_56))) (adjacent h7_64 h7_72))
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
theorem h8_56 : Span (book.check 8) 56 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h8_64 : Span (book.check 8) 64 5 := scan_ok (by decide +kernel)
theorem done8 : Span (book.check 8) 0 69 := (adjacent (adjacent (adjacent (adjacent h8_0 h8_8) (adjacent h8_16 h8_24)) (adjacent (adjacent h8_32 h8_40) (adjacent h8_48 h8_56))) h8_64)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h9_0 : Span (book.check 9) 0 8 := scan_ok (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem h9_8 : Span (book.check 9) 8 6 := scan_ok (by decide +kernel)
theorem done9 : Span (book.check 9) 0 14 := (adjacent h9_0 h9_8)
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
  · exact (Nat.not_lt_zero _ hi).elim
  · exact done6 i (Nat.zero_le _) hi
  · exact done7 i (Nat.zero_le _) hi
  · exact done8 i (Nat.zero_le _) hi
  · exact done9 i (Nat.zero_le _) hi
  · exact done10 i (Nat.zero_le _) hi
theorem low : Lower true R T 11 := by
  let c : Closed T 10 := ⟨book.vals 10 0,book.sound properPN 10 allRows 0 (by decide)⟩
  exact fromClosed c (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 1, 9), (0xffff0000ffff0000, 1, 17), (0xffffffff00000000, 3, 35)] (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B57

def fullRoots : List Sig := inputs
def fullWord : Sig := 0xfeeaeac8feeaea80
theorem fullBound : Lower true fullRoots fullWord 11 := by
  intro p bank h hit
  have hlow := B57.low p bank h hit
  omega
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4276808320)
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
  unfold PEqualNP.Outside.L_meta_40874.Model.Repr at out
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

def mono : List Gate := [⟨.or, [4, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [0, 14]⟩, ⟨.and, [8, 15]⟩, ⟨.or, [13, 16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 17⟩ (List.ofFn x) = posted x := by decide +kernel

theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40874

open PEqualNP.Outside.L_meta_40874 in
theorem PEqualNP.Outside.L_meta_40874 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve fullBound

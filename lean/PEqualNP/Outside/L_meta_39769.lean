import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39769
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
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
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

private lemma b_read (i) (w : List Sig) (j : Nat) :
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
  simp only [b_read]
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

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else if (m >>> 9).testBit j then one else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 1 &&& x 3 &&& x 5) ||| (x 0 &&& x 2 &&& x 3 &&& x 5) ||| (x 1 &&& x 2 &&& x 3 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := (hints >>> (6*i)) &&& 63
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior

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

abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else if (m >>> 9).testBit j then BitVec.allOnes 1024 else 0
 (x 0 &&& x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 1 &&& x 3 &&& x 5) ||| (x 0 &&& x 2 &&& x 3 &&& x 5) ||| (x 1 &&& x 2 &&& x 3 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else if (m >>> 9).testBit j.val then BitVec.allOnes 1024 else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · by_cases pin : (m >>> 9).testBit j.val = true
    · simp only [vertex,if_neg hh,if_pos pin,bit_one,BitVec.getLsbD_allOnes,decide_eq_true i.isLt]
    · simp [vertex,hh,pin,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else if (m >>> 9).testBit j then BitVec.allOnes 1024 else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2

def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,_,_,l,base) := s
  let ms := fixRows ((m &&& 63) ^^^ ((m &&& 63) &&& (q ||| o))) o
  earlier.contains (q,base) && (l == base) && properB (graphGoal q) &&
    checkMap ms (vars m) (graphGoal m) (vars q) (graphGoal q) &&
    (movedWord ms (subcube z o) == one)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  rcases s with ⟨z,o,q,sp,hi,l,base⟩
  simp only [certifiesSlice,Bool.and_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨earlier,rfl⟩,pr⟩,mapped⟩,all⟩ := ok
  exact slice_correct mapped all (proper_of _ pr) (prior _ earlier)

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot
def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP20502 : Nat → Bits
  | 1 => ~~~(0x1114 : Bits)
  | 2 => 0xdf7c
  | 4 => ~~~(0x4068 : Bits)
  | _ => 0

def samplesQ20502 : Nat → Bits
  | 1 => ~~~(0xedde : Bits)
  | 2 => 0x2818
  | 4 => 0x4406
  | _ => 0

def compactPerms20502 : Array (List Nat) := ([[], [66], [33], [33, 66], [65, 66], [65]] : List (List Nat)).toArray

def compactDomains20502 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords20502 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount20502 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath20502 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive20502 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords20502 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs20502 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords20502 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords20502 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket20502 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP20503 : Nat → Bits
  | 0 => 0x5fec97bd7b8e86
  | 1 => ~~~(0x100915c84b4ad4 : Bits)
  | 2 => 0x7bfb0d7add5b70
  | 4 => ~~~(0x8228f30119f22 : Bits)
  | _ => 0

def samplesQ20503 : Nat → Bits
  | 0 => 0x20814820600c04
  | 1 => ~~~(0x6effeebeebfefc : Bits)
  | 2 => 0x440a092080260
  | 4 => 0xa02060c800098
  | _ => 0

def compactPerms20503 : Array (List Nat) := ([[], [66], [33], [33, 66], [65, 66], [65], [16], [16, 66], [16, 33], [16, 33, 66], [16, 65, 66], [16, 65], [32, 33], [32, 33, 66], [32], [32, 66], [32, 65], [32, 65, 66], [64, 65, 66], [64, 65], [64, 66], [64], [64, 33, 66], [64, 33]] : List (List Nat)).toArray

def compactDomains20503 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 2 0, 4), (subcube 4 0, 4), (subcube 16 0, 4)] : List (Sig × Nat)).toArray

def compactWords20503 : Nat → Nat
  | 0 => 0x7f81fe060de0536aaf2d6789dfe00229fe032acf971b013e23908b946904802804803b8c8356e22cff0060d198fb6b8e78ca8a8f55ff80ff01fe016e0f5bb0049009aa5d7f805b5cf63bfc053b5bc3c16f96d3ff80ff01b45ffc0142fff01fe023e04fc79f89105a2ca3225ff0001000464872293fd7de80590490480308f0c9dbb504ffe0ff05fd7fc0197ff01070fd0060e4f
  | _ => 0

def compactCount20503 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 3
  | 3 => 2
  | _ => 0

def compactPath20503 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords20503 (18 + 12*i) 12
  | 4 => let v := readCompactBits compactWords20503 (193 + 12*i) 12
    (readCompactBits compactWords20503 (181 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 3 => let v := readCompactBits compactWords20503 (953 + 13*i) 13
    (readCompactBits compactWords20503 (905 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive20503 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords20503 (0 + 4*i) 4
  | 5 => readCompactBits compactWords20503 (30 + 5*i) 5
  | 4 => readCompactBits compactWords20503 (229 + 6*i) 6
  | 3 => readCompactBits compactWords20503 (979 + 7*i) 7
  | _ => 0

def compactPoolIDs20503 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords20503 (12 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords20503 (4 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits compactWords20503 (43 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords20503 (35 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords20503 (253 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords20503 (247 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 3 => let v := readCompactBits compactWords20503 (997 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords20503 (993 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket20503 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords20503 (49 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords20503 (51 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords20503 (265 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 40)
    let v := readCompactBits compactWords20503 (305 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits compactWords20503 (1005 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 12)
    let v := readCompactBits compactWords20503 (1011 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP4135 : Nat → Bits
  | 0 => ~~~(0x10184040068602 : Bits)
  | 1 => ~~~(0x4012600284824 : Bits)
  | 2 => ~~~(0x20200980103118 : Bits)
  | 5 => 0x77f96fff3eff3e
  | _ => 0

def samplesQ4135 : Nat → Bits
  | 0 => ~~~(0x6dc73be64ff746 : Bits)
  | 1 => 0x49507340525d2
  | 2 => ~~~(0x5edfac78b771ba : Bits)
  | 5 => 0x84d90aa02532e
  | _ => 0

def compactPerms4135 : Array (List Nat) := ([[], [82], [33], [33, 82], [81, 82], [81], [16], [16, 82], [16, 33], [16, 33, 82], [16, 81, 82], [16, 81], [32, 33], [32, 33, 82], [32], [32, 82], [32, 81], [32, 81, 82], [80, 81, 82], [80, 81], [80, 82], [80], [80, 33, 82], [80, 33]] : List (List Nat)).toArray

def compactDomains4135 : Array (Sig × Nat) := ([(subcube 0 1, 4), (subcube 0 2, 4), (subcube 0 4, 4), (subcube 0 32, 4)] : List (Sig × Nat)).toArray

def compactWords4135 : Nat → Nat
  | 0 => 0x7f8189762adfe07f808d6374dfe07928ce7795f5cbff801404f88e022c51841000801000a0b23d7536fbfc01eaeff005e96d95cea47389bb18256a0c1ba81e85e21c7f80ff01fe00dd39f2fff01fe02b47791ff05836aafca2426806b445b1a3ff808f68f07bfc0573b05400696249149febef002882082001ff0715d05aef5c27ff83fc0a278f9ff83fc05070fc0060e4f
  | _ => 0

def compactCount4135 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 3
  | 3 => 2
  | _ => 0

def compactPath4135 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords4135 (18 + 12*i) 12
  | 4 => let v := readCompactBits compactWords4135 (208 + 12*i) 12
    (readCompactBits compactWords4135 (196 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 3 => let v := readCompactBits compactWords4135 (923 + 13*i) 13
    (readCompactBits compactWords4135 (875 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive4135 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords4135 (0 + 4*i) 4
  | 5 => readCompactBits compactWords4135 (30 + 5*i) 5
  | 4 => readCompactBits compactWords4135 (244 + 6*i) 6
  | 3 => readCompactBits compactWords4135 (949 + 7*i) 7
  | _ => 0

def compactPoolIDs4135 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords4135 (12 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords4135 (4 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits compactWords4135 (43 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords4135 (35 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords4135 (268 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords4135 (262 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 3 => let v := readCompactBits compactWords4135 (967 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords4135 (963 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket4135 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords4135 (49 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 11)
    let v := readCompactBits compactWords4135 (53 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords4135 (280 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 37)
    let v := readCompactBits compactWords4135 (320 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits compactWords4135 (975 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 13)
    let v := readCompactBits compactWords4135 (981 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP4119 : Nat → Bits
  | 0 => 0xbaff4c6febd90f62
  | 1 => ~~~(0x230c0a70425d523a : Bits)
  | 2 => 0xf1fdba1fd6e457d8
  | 4 => ~~~(0x1001000180800540 : Bits)
  | _ => 0

def samplesQ4119 : Nat → Bits
  | 0 => 0x4528730703099e42
  | 1 => ~~~(0xdcb1dfa5f757127e : Bits)
  | 2 => 0xe1650ac904173d0
  | 4 => 0x108000006400002c
  | _ => 0

def compactPerms4119 : Array (List Nat) := ([[], [33], [16], [16, 33], [32, 33], [32]] : List (List Nat)).toArray

def compactDomains4119 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords4119 : Nat → Nat
  | 0 => 0x1521f6a578dff009e42d1e7cb1b7968eff000a7ad59a68ff00e9933967845d33fc0ff0130ff027fc0ff03fc0ff023a21f5ec05bd4031b522b5c81653a5ac375fe3db63fc0e94be55b3181d35c44b60e5734a6217c50220c0628c00058a1200016db6db5d7e5903040b102a40f105a410803002806006002c28ff81fe044af507ff801a234529e834ce18ebe2b6e54217412aa3f7edc78a4d0aa27fe00e84c46531dfe07f80824064618cfd1bfe048023940c00001fffffffff00e00d00c00e005004004f
  | _ => 0

def compactCount4119 (k : Nat) : Nat := match k with
  | 5 => 1
  | 4 => 7
  | 3 => 7
  | _ => 0

def compactPath4119 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | 4 => readCompactBits compactWords4119 (6 + 12*i) 12
  | 3 => let v := readCompactBits compactWords4119 (661 + 14*i) 14
    (readCompactBits compactWords4119 (613 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive4119 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords4119 (0 + 4*i) 4
  | 4 => readCompactBits compactWords4119 (90 + 5*i) 5
  | 3 => readCompactBits compactWords4119 (759 + 6*i) 6
  | _ => 0

def compactPoolIDs4119 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords4119 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords4119 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 4 => let v := readCompactBits compactWords4119 (125 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords4119 (125 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 3 => let v := readCompactBits compactWords4119 (801 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords4119 (801 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket4119 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let d := readCompactBits compactWords4119 (139 + 5*(i % 8)) 5
    let off := ((i/8 + d) % 31)
    let v := readCompactBits compactWords4119 (179 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 3 => let d := readCompactBits compactWords4119 (815 + 5*(i % 13)) 5
    let off := ((i/13 + d) % 49)
    let v := readCompactBits compactWords4119 (880 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP4662 : Nat → Bits
  | 1 => 0xbf6c37daa13a
  | 2 => 0xdfaac9fd21cc
  | 4 => ~~~(0x2a20d6217c : Bits)
  | 5 => 0xeef32ef64274
  | _ => 0

def samplesQ4662 : Nat → Bits
  | 1 => 0x441284880922
  | 2 => 0x28052130108c
  | 5 => 0x12085a400650
  | _ => 0

def compactPerms4662 : Array (List Nat) := ([[], [82], [33], [33, 82], [81, 82], [81]] : List (List Nat)).toArray

def compactDomains4662 : Array (Sig × Nat) := ([(subcube 16 0, 4)] : List (Sig × Nat)).toArray

def compactWords4662 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount4662 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath4662 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive4662 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords4662 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs4662 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords4662 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords4662 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket4662 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP4150 : Nat → Bits
  | 1 => ~~~(0x220148608229621c : Bits)
  | 2 => 0x76ffe96f9fe96e7c
  | 4 => ~~~(0x100081000c800c20 : Bits)
  | 5 => 0x78f1df0feeb00fb0
  | _ => 0

def samplesQ4150 : Nat → Bits
  | 1 => ~~~(0x5ddaf3b9b7bda71e : Bits)
  | 2 => 0x9802e8312807c58
  | 4 => 0x10488008013c0306
  | 5 => 0x71da23da40e27b0
  | _ => 0

def compactPerms4150 : Array (List Nat) := ([[], [33]] : List (List Nat)).toArray

def compactDomains4150 : Array (Sig × Nat) := ([(subcube 0 32, 4)] : List (Sig × Nat)).toArray

def compactWords4150 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount4150 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath4150 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive4150 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords4150 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs4150 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords4150 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords4150 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket4150 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP4151 : Nat → Bits
  | 0 => 0x5ecfeffd3c3aded83fff7df2e6fde97b1aa14717dfe78ee6bc3e62861ebda2
  | 1 => ~~~(0x85804c00a7048df20024112c1e564519c1127c4424044a3a4b36aec52257a : Bits)
  | 2 => 0x7c3ffecefff0b9871ffecf7ddbe2def5cc13a0dcffdbcdb96f91086dc6e6d8
  | 4 => ~~~(0x40408080088bc80001800603a90ca6d0a8080008d8288f80a1c00058cbe80 : Bits)
  | 5 => 0x6f53fdfbcacd6cc01fdbf3fe3995664dbfdc800feffe70fb82fc0005f93f40
  | _ => 0

def samplesQ4151 : Nat → Bits
  | 0 => 0x21305081c544202399100980fd010b81154230071e0380c03020630e163882
  | 1 => ~~~(0x77a6ff1f55dfbf69cbbbdfb56db4bb7ef4c7fb6d56eadfebf6f7aeacf22dfe : Bits)
  | 2 => 0x3c032710009027847088410216823205a9e0910539a09210600027d82c4d0
  | 4 => 0x406080400808c0000a3020100900016000000080060060240c1808060012c
  | 5 => 0x10ac8a146c12110deac050274eb26c3644e4026de4ec50088015b0a0f92f40
  | _ => 0

def compactPerms4151 : Array (List Nat) := ([[], [33], [16], [16, 33], [32, 33], [32]] : List (List Nat)).toArray

def compactDomains4151 : Array (Sig × Nat) := ([(subcube 0 32, 7), (subcube 16 0, 7), (subcube 32 0, 6), (subcube 0 1, 5), (subcube 0 2, 5), (subcube 0 4, 5), (subcube 1 0, 5), (subcube 2 0, 5), (subcube 4 0, 5)] : List (Sig × Nat)).toArray

def compactWords4151 : Nat → Nat
  | 0 => 0x72dff1fe1297f8d38c1be187f1004007fc1b6e5217f821212d1356e217fc1daaff02191d91bafff07f82e572ec4faa52a80030ad2e9462b13605486030b2f468dffffc00a00800c3f
  | _ => 0

def compactCount4151 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 3
  | 6 => 1
  | _ => 0

def compactPath4151 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords4151 (11 + 12*i) 12
  | 6 => let v := readCompactBits compactWords4151 (466 + 12*i) 12
    (readCompactBits compactWords4151 (454 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive4151 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords4151 (0 + 5*i) 5
  | 7 => readCompactBits compactWords4151 (47 + 6*i) 6
  | 6 => readCompactBits compactWords4151 (478 + 7*i) 7
  | _ => 0

def compactPoolIDs4151 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords4151 (7 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords4151 (5 + 1*(v &&& 3)) (1*n)
    compactIDsFromBits bits 1 n
  | 7 => let v := readCompactBits compactWords4151 (185 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords4151 (65 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords4151 (505 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords4151 (485 + 5*(v &&& 7)) (5*n)
    compactIDsFromBits bits 5 n
  | _ => []

def compactBucket4151 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords4151 (212 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 18)
    let v := readCompactBits compactWords4151 (220 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords4151 (511 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords4151 (513 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP16414 : Nat → Bits
  | 1 => ~~~(0x2062100948a4 : Bits)
  | 2 => 0xbfe6dfff4bae
  | 3 => ~~~(0x0 : Bits)
  | 4 => ~~~(0x1084c036010a : Bits)
  | _ => 0

def samplesQ16414 : Nat → Bits
  | 1 => ~~~(0xdd5cea8f8de4 : Bits)
  | 2 => 0x480b639a5326
  | 3 => 0x1242c840ddc
  | 4 => ~~~(0xeb73a5ae2d1e : Bits)
  | _ => 0

def compactPerms16414 : Array (List Nat) := ([[], [66], [33], [33, 66], [65, 66], [65]] : List (List Nat)).toArray

def compactDomains16414 : Array (Sig × Nat) := ([(subcube 0 8, 4)] : List (Sig × Nat)).toArray

def compactWords16414 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount16414 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath16414 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive16414 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords16414 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs16414 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords16414 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords16414 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket16414 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP16415 : Nat → Bits
  | 0 => 0xfb2ff6d5ffe0cfb53ff6fefb7dbee9872223cfdf9f7df73653876bf46bb4
  | 1 => ~~~(0x42a00010c882cbdc400488824024f1e63405ec111011403a6325cc2152bc : Bits)
  | 2 => 0xf4effb7fcf823bcaffff9b9fdfe5f2e254cc37f7fbf75bd9a425ceff12da
  | 3 => ~~~(0x100002440600000000021001100000000000000402401300000000d40000 : Bits)
  | 4 => ~~~(0x2160700101203fa3800002180d8fea8342ea1402892400d594876a022bd2 : Bits)
  | _ => 0

def samplesQ16415 : Nat → Bits
  | 0 => 0x4d24aaa081b3245d25502e565471484852c19d893059516174167b44b14
  | 1 => ~~~(0xbd57ffceb53c3c13769a0de31fffbd5c47f55539333fd229eb07fc33d3bc : Bits)
  | 2 => 0xb1114c210ef50b530a9a02a71c1210f1a7443853aa6425c85284e7e109a
  | 3 => 0x1004064c4300000025100c000a0841204710943b413a200140069003e7e8
  | 4 => ~~~(0xde9f27eaeef7a11c71795cd3fe81c9f79fbd989fdba6259dc697ba066fda : Bits)
  | _ => 0

def compactPerms16415 : Array (List Nat) := ([[], [66], [33], [33, 66], [65, 66], [65], [16], [16, 66], [16, 33], [16, 33, 66], [16, 65, 66], [16, 65], [32, 33], [32, 33, 66], [32], [32, 66], [32, 65], [32, 65, 66], [64, 65, 66], [64, 65], [64, 66], [64], [64, 33, 66], [64, 33]] : List (List Nat)).toArray

def compactDomains16415 : Array (Sig × Nat) := ([(subcube 0 8, 7), (subcube 0 1, 6), (subcube 0 2, 6), (subcube 0 4, 6), (subcube 0 16, 6), (subcube 1 0, 5), (subcube 2 0, 5), (subcube 4 0, 5), (subcube 16 0, 5)] : List (Sig × Nat)).toArray

def compactWords16415 : Nat → Nat
  | 0 => 0x19d778aff83fc1fe0a0984fa62822000ff83fc0dd331bff8056bfe02818820e66104e5fe088003fe032aff83fc1fe0be6ff80fee153457e71eb0d84073c9152fc00688d11f
  | _ => 0

def compactCount16415 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 1
  | 6 => 1
  | 5 => 1
  | _ => 0

def compactPath16415 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords16415 (26 + 12*i) 12
  | 6 => let v := readCompactBits compactWords16415 (253 + 12*i) 12
    (readCompactBits compactWords16415 (241 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords16415 (447 + 12*i) 12
    (readCompactBits compactWords16415 (423 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive16415 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords16415 (0 + 5*i) 5
  | 7 => readCompactBits compactWords16415 (38 + 6*i) 6
  | 6 => readCompactBits compactWords16415 (265 + 7*i) 7
  | 5 => readCompactBits compactWords16415 (459 + 8*i) 8
  | _ => 0

def compactPoolIDs16415 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords16415 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords16415 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords16415 (88 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords16415 (44 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords16415 (322 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords16415 (272 + 5*(v &&& 15)) (5*n)
    compactIDsFromBits bits 5 n
  | 5 => let v := readCompactBits compactWords16415 (467 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords16415 (467 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket16415 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords16415 (96 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 11)
    let v := readCompactBits compactWords16415 (98 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords16415 (330 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 7)
    let v := readCompactBits compactWords16415 (332 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords16415 (469 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords16415 (471 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP542 : Nat → Bits
  | 1 => 0xebe7be3f77a0dec
  | 2 => 0xdbf9db3ffac0ef8
  | 3 => ~~~(0x4001820042808c0 : Bits)
  | 4 => ~~~(0x82018013000428 : Bits)
  | _ => 0

def samplesQ542 : Nat → Bits
  | 1 => 0x14a8e16b018996c
  | 2 => 0x26026e9cd0066d8
  | 3 => ~~~(0xbfb779dbdf95ace : Bits)
  | 4 => 0x92209120e05a86
  | _ => 0

def compactPerms542 : Array (List Nat) := ([[], [67], [33], [33, 67]] : List (List Nat)).toArray

def compactDomains542 : Array (Sig × Nat) := ([(subcube 0 2, 4)] : List (Sig × Nat)).toArray

def compactWords542 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount542 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath542 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive542 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords542 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs542 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords542 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords542 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket542 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP31 : Nat → Bits
  | 0 => 0x7d3fdb57ff0669ffb7bbf7dfb9c8503bfdf9f7df7453815fde4a
  | 1 => ~~~(0x218000432216fe0024230610012e5a7e01110114077ba581056e : Bits)
  | 2 => 0x7abfedff3e1097fffcef3ef7ef660a45ff7fbf75b32824ef7f24
  | 3 => ~~~(0x800091018000000108000c600400000004024013000000a5000 : Bits)
  | 4 => ~~~(0x1001c0040400000000083001a800000000289240000000440a00 : Bits)
  | _ => 0

def samplesQ31 : Nat → Bits
  | 0 => 0x2c92aa820d98e92a84bc8d8b6706342dd8930595863c1dddc42
  | 1 => ~~~(0x5e5fff3ad4e145b4d076c485fbfdc3e84b9333fd263e878545ee : Bits)
  | 2 => 0x5445308437b69854d40571e3a48ccc97853aa6423a0a9e77624
  | 3 => 0x81019310c01232880710343544a0390abb413a209b107248fdc
  | 4 => ~~~(0x6ffc9fabbbbd7f8bcaf3a7ffdc4f6ff2b9fdba625bb317649e54 : Bits)
  | _ => 0

def compactPerms31 : Array (List Nat) := ([[], [67], [33], [33, 67], [16], [16, 67], [16, 33], [16, 33, 67], [32, 33], [32, 33, 67], [32], [32, 67]] : List (List Nat)).toArray

def compactDomains31 : Array (Sig × Nat) := ([(subcube 0 8, 6), (subcube 0 16, 6), (subcube 0 1, 5), (subcube 0 2, 5), (subcube 0 4, 5), (subcube 0 3, 4), (subcube 0 5, 4), (subcube 0 6, 4)] : List (Sig × Nat)).toArray

def compactWords31 : Nat → Nat
  | 0 => 0x743e0b5c6996455a2332ff0001b5a0917fe0030427f80340f5fe004f95280e9c21fa2eb0c676335f10bfec2748575d56c257ffe001038aca900e9f0ea2ff007f803fc01fe0055358434bfc018eaf822cff8016d43173bff002e906c1ccd034cf23a844d32254f6fe712084bccd3b92fbff00041a7140a98801f64800400e3900ac2ba000008182100084008202c800447a4018086408104706c0e410384008190c0000409ca4246686904a033d4764e9db6b45638bf9662ac5189bd192253fe718cb16527a458720c315c1f02e83600808028862120c10888018082901a050082918a000a4c51244180049082020052149060824c50a604196001e441202051950100c48019851882501848ce0b330b38290480806208c0612101014e629983020a8090a5080c7c332628bfffbffffdfeffff7ffdfefffbffeffffffafdbb7feffffffafdff8b28145028a049408282c5210642048601080210043148629085210a431426284850c0648007228e45144a260c8c28c03200430006028c0510401803801401064003001ff01606cfd7ff800a67fe03fc035c7392e2e67382ff80ff0064ac293932a6d2bfe02f1daf1ff875aedef84ff80ff01b6c8150f911ff01fe03fc07f804c6cecb9145ae1d1647ce9a7c1a642cef03b308b9540219008a1b2810a1cb2848824329488431908324c391afffffffff832401801c00a00800c5f
  | 1 => 0x129184a8c04460a131420c818c4086205316c0c96004b46258312a0c9500388321e300f18ad0646c6234310b18a48c0246280190004808c400620230580c8c0046462303119184c8c05801ae30d6186f0647861e50032452001c51c00c51400c50801c50032402001a51400a50032200800852001851a00851800851000850801850032032400832200832001832000821800812001802001801c00801800ff803fc01cae79aa9a6cfcc46a4963ff00099b6acf924e26930a70b2ee4f14efd9b9e44ac8d6480938d58ba4de3575cc287f290888ffc01aea65c150b8b7fc01b47bff007f80051a7fe000d10e4a1b1a6c95679391a71152a3a047fc9413a222851c9e85df97040e2123fcc956e1d8751fbe1c54cf2c5471ae5ccebfe00806fb01e7a52ed48f4f8c7f800f63200deee408a1bedd60b4aae85aaa0258d59208c245b84877e0bbbc63d483ddb6dd438cc0b5341bbc0da196162551280bc2fb89b4cb3157f941335c4c0473d099963b9d915e429692994d7da457fe00ff002ca37fc017c20ff00799468537fe001e5d871f71e3dfe00ff005c2fbfc0046f3375a32ad88e15fe00151cb7a9ee941d6bd0061d0473a10f434b804e089de89239680ff005f31cb1c71a78c0915f2a529ef9e2e6b52ff803fc01fe00904cd319c7cfcc4a3f555fd49aa1705e17ff004ad5e95b5929e515e2108a605f0089374fff80115d5e
  | 2 => 0x284c481b3329c3f3cde0c3b43703d4974e7160d8980697c907282f2e65f4dda8b12c802e51b09a5165acd11c496ccd6050a01000207002a06120912040028000b0031141c2400340501006a0c5103030e0024020b5225002307a5013d2b212a00353314200103030d0413030208110029020c0a0007311d010d0d620b0010020f0600020b24100003000d270a1203005f0001000005060803120c03001a1700000501070107000502030101000703020c01060004070a00062c08170503321c00030006000d0f000102010a00030502370100000104000905002e0d020c3204831d4531142304c04f93c2ecba0e9380e1b58c52f2b82e2b42d2b0ab0acaa0a8a90a4a84982609826294a4090a308c234842128020080204799b4641906498061950549405014050934449023c8e0388d0348c8200821d8480001040f0c02030c051850000400810100420000420000031c064108008c0c16026131984c11030830cc0c304110014c4c005814218c158b7de9f9fbdbdb7bdbddef6f6e79fbee7e6e7ee9fb7bdbed79fdd9ddd9fded7de9f9f9fbebd9ff6bebeded7de9f9fdbdadbbe9fd79f9f9fbe9ff6fcbebefcd7de9f9f9fdede9f9ffcbcc461cf282718338c08660c0305318698c14a60a5280d18064c018320d316498a206410325c192e00978c17461ba305d180e8c37460ba305d182e4c174603a30280c94004a462503
  | 3 => 0xf1b5cb6e4c40ff0001a31f22efd86eff00178fa3177c2884ec24e571abd65822e2acadc95471067e7143f7c5ed8a3f55dee83a8b5be7edaac653089b7957400fb2e8aeab6615b56ec853480fbe87777da8178685efc1e60874a68c522b666075c781c391f7da091581654dfa569d064c973923d7eb46c7b220d1313717ffc00ad97b0423b396a55d38672bfc004126645ee8888e9a45a0ccd926d37020d8bad06fb027e54338f627ff00368098d336d14f876393d9ea65eac4edf534e6a4b3e9fdd8526c174f60fd77b4527691c567539a2aae18b0ff00121e1e6a2bcd5f32111cc4dff0008159ff003fc00ff003d23fe89a9b523ff000c9afff00304a03623c8757ab02b45e7222b131f9acbde8579685aeb647a52725876f37adc6decc6e7465bb9c3ffc00034d3410d8141495e3dcd47fc00109eb948e575d71c3fff003fc0041779368b9f4edfa920d57874f5ff0016558ed11fc2849e6ed88d2557fc45853945c8966af327fc00903be163bac94bfc00ff002e48a1a58fa5e0ff0028d9a4a82ffc007c6f3fc009c1dffc00ff002ea7dff002608068d1cb8f821a0488f9ee9ed671ec0794d707881328e2f302c41a1fa13876d73ff00098bfff0037df3987540500bda5f1efb7b7323a3d637b304b41a4c8769a1d7d4ef2d407893b014f1f09283a02f440ad2076082cdb7331a28e337e91162f45ba518bc21a2b5dc991c
  | 4 => 0x3274ce094b4a98bc6ff0395ba9760855b4d49962047dcd0f6a797624f642a443f4c9e7de4877c0886d3d7f2e441079b97eeb7b68a6a13f880b8cd0499f085fe79aed8f31ff0019d68f472e5a39d8664517fb6227fc0053ceffc00670cda9a0842df0dddff002487dba86e8dd1cba00aa4eea742d22dd9caea1c8ff00325bd4f0bffc00ff0023ebfff003fc00a80fbfc00ff0015411ff001030b169ca630dc7b3801d7e9633fc00ff0011c36ff0019dc96dd8da8a4ff003c1cfa97c4dca20e76a9d53dd59f3673509dfaca6856cedec87666ffc001c2092c869ad9f4dc683255734f9527aec6b4e8dffc00ff0002a69286d48471424748aa700cff7954b2c94254d38a3e6e6c431aa2950bf752271ff105d45929a20d9c722276f315b9c4daff49d032c2ac90e676f051ff000ee41284c24d296d8ce8d7202b0a1aee676b6c4b6a6517c74b5765ea69bff003fc0027190e666c573a8f5b291cd19959e63d0f11ff0011eefe63a4dc8c78b63fc00430b95ae7107d3a6af8cba84e63b9d4ce17c04a79702227b53fc004614d62670a66339913890c8d646354b12e3f31425974ff0032e6f6f7aa5b35be3d055d63649d21abbc275fc6965aeacd5a4d6713eb30a0f3448d942d46e0144b7f812bff00362e69f6c6353fff001e729bed0d8a9fcbd35f5656f5f85ecf5435f7e1d2071e7c460c55ffc00ff0014c37c56ff203df6010c
  | 5 => 0xa82089861861861869041041044c30c30d20a0314209b025616375c8f5d30f99cce738dc6e956ab5598f46fc93ce346e3d0fae6d2793c94712c38579ccc0e1703246309b18504c110320c19000c808e400721a385f1caa8e220321139820c898e24c701e390b1ca806444722039230628019230429000e30029000e30019100531409000d30429000d30019000d28028019031028d00431028c00430d00400430c28800419128a00419100400409000c00401228e00401228400c01028c00400e28a007d26ba92fa72f32e8d46664975b6f9151361d9d514a22f155c96557d0b205634edc2f3927fc00de60ffc00ff002a8c8ff0026d3d20c8e22215841a580b03504b52ed476484e3ff003fc009444608cfff00070454528778dd24bc9f9195d5f7fc00ff003fc00ff00325e901247611333c4d9293ff0022296ff0002887c74d6fcb8e67a3fc00e4712c0b3f6a8e420026587fc00f4a1bfc00367dea96aff00309a7ff0012d2dff000ad04ff003fc00ff001f171e2706b09fff003fc00ff0029170ff0030405c146ce265ff003fc00ff0037815ff003fc00ff0001abeff0016042ff0007657ff003fc00f89a2156c17a14cdb7c393e80d5cf58172c3dc94d8c65137bffc009585d312fff0010e25ff001f1011f7f4db05f34843a29480c88cca54dadb1f20429415f88529c5c7405c88986ff368eaf2f837ef89a120351c30
  | 6 => 0x7f87f86656ccd82ff87f87f87f80ddb121fc7f806480c89cc048006003e2a5e55448c6f516a64dfff007f803fc01e859083aff80050296493ff0000c3ffc00bed0f52aba2bc0e26b90aa323ec196ad07a12dff005bb4fb58e5817ba02ff8015a430ae3e338b145cb88b10532e94f030bd9911616b41eff8011ddb14644f6b65b0ffc00aabd1c6342c4a3d4ffe0040877f800124ee05d67343896275815adba98f8c136d59760bbf048fab2a5e469e1d7d1dc6c45f5d6cc8d3716ec2f01d6d3f065664fc216144502d1e36a7f80079120cb4063488b97a8b924fbcf4c91147c15dfe00ef5d68072c947fe000255ff8016de6268fff00218bfb97e829d9c86ff803fc00f731e9848ac41ed2ffe001f5845b6541034ec4e667f83576e1826e7ea83cf495a04202a9012dbb2f9093ea2c1f435510ea2dc3fe00d59bbb22e5c13fe006f99c12b4fcb41c41ff007f802d163acefff005e02c38fbaa29ff007f803fc0122102f85af1d0c9bbfe00080aa234bac2370b2bd5cd7b37fc00e85fff0079c15b487bb010e6ba19affc0022206e2f2cc10ad0fec70ce2b030fdedefccaa883bcf4afe58b1f0024119db33fc0035086d74c2950097089350356661d94966dd2fc050ee26d612bf257d55bb4b38010c0d400800f04d1474c33dd01912308410930201214370504600000f0821804010d61830c12043430002
  | _ => 0

def compactCount31 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 6
  | 6 => 31
  | 5 => 73
  | 4 => 26
  | 3 => 1
  | _ => 0

def compactPath31 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords31 (11 + 12*i) 12
  | 6 => let v := readCompactBits compactWords31 (1024 + 15*i) 15
    (readCompactBits compactWords31 (952 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords31 (7523 + 17*i) 17
    (readCompactBits compactWords31 (6923 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 4 => let v := readCompactBits compactWords31 (23698 + 17*i) 17
    (readCompactBits compactWords31 (23014 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 3 => let v := readCompactBits compactWords31 (28421 + 12*i) 12
    (readCompactBits compactWords31 (28373 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0

def compactLive31 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords31 (0 + 5*i) 5
  | 7 => readCompactBits compactWords31 (83 + 6*i) 6
  | 6 => readCompactBits compactWords31 (1489 + 7*i) 7
  | 5 => readCompactBits compactWords31 (8764 + 8*i) 8
  | 4 => readCompactBits compactWords31 (24140 + 9*i) 9
  | 3 => readCompactBits compactWords31 (28433 + 10*i) 10
  | _ => 0

def compactPoolIDs31 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords31 (7 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords31 (5 + 1*(v &&& 3)) (1*n)
    compactIDsFromBits bits 1 n
  | 7 => let v := readCompactBits compactWords31 (295 + 10*i) 10
    let n := v >>> 6
    let bits := readCompactBits compactWords31 (119 + 4*(v &&& 63)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords31 (2436 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords31 (1706 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 5 => let v := readCompactBits compactWords31 (9786 + 10*i) 10
    let n := v >>> 7
    let bits := readCompactBits compactWords31 (9348 + 6*(v &&& 127)) (6*n)
    compactIDsFromBits bits 6 n
  | 4 => let v := readCompactBits compactWords31 (24424 + 6*i) 6
    let n := v >>> 4
    let bits := readCompactBits compactWords31 (24374 + 5*(v &&& 15)) (5*n)
    compactIDsFromBits bits 5 n
  | 3 => let v := readCompactBits compactWords31 (28443 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords31 (28443 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket31 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords31 (355 + 3*(i % 9)) 3
    let off := ((i/9 + d) % 38)
    let v := readCompactBits compactWords31 (382 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords31 (2777 + 6*(i % 62)) 6
    let off := ((i/62 + d) % 222)
    let v := readCompactBits compactWords31 (3149 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords31 (10516 + 8*(i % 174)) 8
    let off := ((i/174 + d) % 617)
    let v := readCompactBits compactWords31 (11908 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 4 => let d := readCompactBits compactWords31 (24580 + 6*(i % 57)) 6
    let off := ((i/57 + d) % 203)
    let v := readCompactBits compactWords31 (24922 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 3 => let d := readCompactBits compactWords31 (28445 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 13)
    let v := readCompactBits compactWords31 (28447 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP1596 : Nat → Bits
  | 2 => 0x76febc3f7da5cbd2
  | 3 => ~~~(0x1000882221250382 : Bits)
  | 4 => ~~~(0x220426905412e878 : Bits)
  | 5 => 0x78f5e28ef7522f28
  | _ => 0

def samplesQ1596 : Nat → Bits
  | 2 => 0x942418524114990
  | 3 => ~~~(0x6f7ff7ff6f7fffb6 : Bits)
  | 4 => 0x222412180b221606
  | 5 => 0x716546e40735f20
  | _ => 0

def compactPerms1596 : Array (List Nat) := ([[], [66]] : List (List Nat)).toArray

def compactDomains1596 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords1596 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount1596 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath1596 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive1596 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords1596 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs1596 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords1596 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords1596 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket1596 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP574 : Nat → Bits
  | 1 => 0xf5abf6cfdff714f88ffcfbdbf7eec7b8e3d48a0effcfbef39f1d2d803dc36dc
  | 2 => 0xdfc3fff9e77c671e0fff3ffef8f0f83f03e7f00f3ef3fffbe3e1ce0037ed760
  | 3 => ~~~(0x40800001c06000100000010080e08030020400003082302202010c002581400 : Bits)
  | 4 => ~~~(0x54800c0061e548c00003890401c440cc1e3c80008010cd1f9d8810010682f8 : Bits)
  | 5 => 0xec5be9f7fecad8850ffbfdb5cfdd0444dc2b4c0ff9bf7dc478da91603f388b8
  | _ => 0

def samplesQ574 : Nat → Bits
  | 1 => 0xa549990b000e607ec916228549bd05aa82120caa5c92ab0964a2908bc826d4
  | 2 => 0x203e000a3ac598a2b2e54d12111c0503269cc5160a62f1eaa148c425336d540
  | 3 => ~~~(0xbf7fddef3f1ffffffadd7f7fdfffe36ff7aafbfff3e372faff6ffd74ffb54c6 : Bits)
  | 4 => 0x54908c2030e342c02180a67c1214104c480729df222020026275524cf95006
  | 5 => 0x13a453484914b576d9495a225b6688cd426892bf51955460ee4a45627f308a8
  | _ => 0

def compactPerms574 : Array (List Nat) := ([[], [33]] : List (List Nat)).toArray

def compactDomains574 : Array (Sig × Nat) := ([(subcube 0 32, 6), (subcube 0 2, 5), (subcube 0 4, 5), (subcube 0 8, 5), (subcube 16 0, 5), (subcube 32 0, 5), (subcube 16 8, 4), (subcube 32 2, 4)] : List (Sig × Nat)).toArray

def compactWords574 : Nat → Nat
  | 0 => 0x3e225d30c288006f0e2f2b3d0ba813fc0617fc19b666bfc3fc3fc2da7fc27de146eee2e0c32aa26563c14a2842d12fdffd7effebf7e8a16284c03328c4a300088a2028b00c008007fc3fc2e4ffc18d1a4a207fc1856c655dc23dad9a108803b2831ba8410b260421309aa1b80c15f7fffff0c8089806004003868d11f
  | _ => 0

def compactCount574 (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 5
  | 5 => 8
  | 4 => 1
  | _ => 0

def compactPath574 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits compactWords574 (29 + 12*i) 12
  | 5 => let v := readCompactBits compactWords574 (458 + 14*i) 14
    (readCompactBits compactWords574 (422 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits compactWords574 (962 + 12*i) 12
    (readCompactBits compactWords574 (938 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive574 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords574 (0 + 5*i) 5
  | 6 => readCompactBits compactWords574 (89 + 6*i) 6
  | 5 => readCompactBits compactWords574 (570 + 7*i) 7
  | 4 => readCompactBits compactWords574 (974 + 8*i) 8
  | _ => 0

def compactPoolIDs574 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords574 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords574 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits compactWords574 (239 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords574 (119 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits compactWords574 (662 + 6*i) 6
    let n := v >>> 4
    let bits := readCompactBits compactWords574 (626 + 3*(v &&& 15)) (3*n)
    compactIDsFromBits bits 3 n
  | 4 => let v := readCompactBits compactWords574 (982 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords574 (982 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket574 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits compactWords574 (284 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 11)
    let v := readCompactBits compactWords574 (290 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords574 (710 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 18)
    let v := readCompactBits compactWords574 (722 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 4 => let d := readCompactBits compactWords574 (984 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords574 (985 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP47 : Nat → Bits
  | 0 => ~~~(0x1010802c000063658020001200103604b0 : Bits)
  | 1 => ~~~(0x402660000661000184a00004226484940 : Bits)
  | 2 => ~~~(0x200009d000098c8006018004318180300a : Bits)
  | 3 => ~~~(0x0 : Bits)
  | 5 => 0x77f2effdffefffe59e6bfff673b7ff7dfa
  | _ => 0

def samplesQ47 : Nat → Bits
  | 0 => 0x1031841c32f81ee381e01d710f8f89f346
  | 1 => ~~~(0x7afdd8f457dca5a4d3bd2c225aed5a5b50 : Bits)
  | 2 => ~~~(0x5dff6c2ff268637a5fc9036d7b9530740e : Bits)
  | 3 => ~~~(0x7fabdfbf3cdc7e17b752999587ba8f8182 : Bits)
  | 5 => 0x88710875410a62abac6abb456b2935d9a
  | _ => 0

def compactPerms47 : Array (List Nat) := ([[], [82], [33], [33, 82], [81, 82], [81], [16], [16, 82], [16, 33], [16, 33, 82], [16, 81, 82], [16, 81], [32, 33], [32, 33, 82], [32], [32, 82], [32, 81], [32, 81, 82], [80, 81, 82], [80, 81], [80, 82], [80], [80, 33, 82], [80, 33]] : List (List Nat)).toArray

def compactDomains47 : Array (Sig × Nat) := ([(subcube 0 8, 7)] : List (Sig × Nat)).toArray

def compactWords47 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount47 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath47 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive47 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords47 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs47 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords47 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords47 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket47 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP62 : Nat → Bits
  | 1 => ~~~(0xa024c201e4002818120704e330010618227331082aa : Bits)
  | 2 => 0x5efffe671e5fff9fcffbf0ce337ff3e39fff3317deaa
  | 3 => ~~~(0x0 : Bits)
  | 4 => ~~~(0x40030460000001e0882008000000200199800015800 : Bits)
  | 5 => 0x6cfa7dfe801ffaffb9a67f80007f9e7dfbb80005fbc0
  | _ => 0

def samplesQ62 : Nat → Bits
  | 1 => ~~~(0x75d99bcfe5936f471ead238bd5a956d1a6ad3d188bba : Bits)
  | 2 => 0x218002bae0e2e5abb088c550bc65a2a70e3f8346dc8a
  | 3 => 0x88440a2152340ba111086446a4350e5a3943b9b76
  | 4 => ~~~(0x7bbdcf3cef6de7f5b8d1ba2f7c62830af7bf80bbd846 : Bits)
  | 5 => 0x1314d20937e949a6531ab3f251bbb42cba895525ebc0
  | _ => 0

def compactPerms62 : Array (List Nat) := ([[], [33]] : List (List Nat)).toArray

def compactDomains62 : Array (Sig × Nat) := ([(subcube 0 8, 5)] : List (Sig × Nat)).toArray

def compactWords62 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount62 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath62 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive62 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords62 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs62 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords62 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords62 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket62 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP63 : Nat → Bits
  | 0 => 0x5fababfffdd9beff91f3bb9e7afbcfa1a033fffe3f79fffeff7fb7f9fdee6fbdf6aef38e25a68e34f0fdc3f5ff807d0e0d07fffff79ffe5f7f3eff7ff5dd39d9d07e29e6fc79fd7de8f4ffea7b203d7e78102621e3fff5fefeffa7fb14fe611fead7a7b7f9e79d8643c02bfbef6d23da4a
  | 1 => ~~~(0x8988c00800088310ce085941028d9e5f8b4000010203810283006010040e81e2244db0ba12c0503e0198009c7037f6fcdb80000020c040810103021805b711f8013808c70f020f884e070f020781138125e37b3fb80412000610201305407140780e23c58ad11f6f3d8b01229cc0a316e : Bits)
  | 2 => 0x7e5f87ff9f6ffff97fe0bf83fc1df85e5887fffbfdfff87ff9f9ff3f3ffff3fe1fd3ff33e2fc113fe3079cffc0830261c0bffffc7ffcfffff3fff1f79ffff07f8787c27d0ff61ffa7fe30ff09ff84ff88a4e1192187fdf2fdfe7ff7ff12cff0c7f83f9fc3e7cec70b0189f7e37bcf8f324
  | 3 => ~~~(0x201000e004802001000300040110000000000000118000e00000038380002001002000000800030000000c000800000000000004180c000020c000410000040000400600800100060000c0010000800080000000004000c1a048060002040004002010020408c0000000a600420208000 : Bits)
  | 4 => ~~~(0x42680011c0000c0e1100b03ba08c60200000002000100008141b000042a51bd86b0f0b20622900413045c3530000000000000003000325301020100041d081857822a03040e0d46089703ea8b204566800000000003140200022118050aa00f2ad198b3162060000000010bb318c14a00 : Bits)
  | 5 => 0x6fb4c3fffefecbf7ec1c45759328d7e60003ffffd3bf3f9faff7fefffe78d81fa274d8fb9f2bf5c31f187c09370000000007fffffbeff7fb9fdf3fadfe5b4f1e7f93be8b708e20c6849f70ffa07fd12790000000007f7fff3b7ffbfd2f5386f707f8da3b56a9700000000ff3b9dacf2c00
  | _ => 0

def samplesQ63 : Nat → Bits
  | 0 => 0x2054542012564501ee0c8463851a303c3ecca11dc1660071017e4839c22e7c4216bd0c422759600b0c05df0a00f381f00e3b1737899f025c8331017815dd39a628062b980c7fe28068f7f0151b2072810c60383a03e815cee2f8a67b15d161106ad441b7c0670e0683e03bdbc74d22d842
  | 1 => ~~~(0x776772fb3ffa776eba5f6a23ffd7031a8f09ed6ed79a91e5f4ee3c6a6dbe13f17fbabddd5dc8f06abbe2efa955fd14bab42d2355c6da54f9d76669b9b3779dd699950c3dd35bc0eec5ad5ab33f11f5dce87bf29f6d89676649698e29b2d48d956799e6ee9aedb5d2fec8f812abcc6e31ee : Bits)
  | 2 => 0x1a07810e498010a821544ec89e347a1a3db6046858662815a0a96c1f8082684e09e34084d36a3c91548650cc92fa48e1cc0aaf4d615c49ba2c3539300a5c33dd2a3bc38100894bb01639d2032c2f4e20a90b1c640db9e225cc5cf654134cb285c81c8d9382ce478809a3f3c23bcf0b224
  | 3 => 0x201004700c8521014201200415100880000c4a549088823b41002d81c90103151024008804010227820206002140886401c45c4044a35204102a880e10a850a78089415a13e41dda20026402508634ca816401ca0036a12853b1419908c949721292462178812b8d541e007ba89cf57dc
  | 4 => ~~~(0x7bd97dfee8ff7d3d0efaf4f961f7a1fdfdebe2bf69c6dd7f7e3d26fffe313f287d5fe08bd17bc9dbfeb1fad8cedfd98feef85df727bff76b03c385c6e1fecf3a7d4bbf5de87f79bbfa63efca3dbd7767091f69dfa3431e12a6bf377d11eef15f7b7990fb172a7a78c345e30fb399c3de54 : Bits)
  | 5 => 0x104b3c8221031c483363b3aa2c772a0ceff50a284c4b59b69a48394a4ac5662ea5c42514669cea51243e8f1750951f32f7cd7959baa55075b4551614a6c4d282998c4f2a7992714c0ba501f3f1b9986bb78252a02dfd67752b2f3bac675342650b9cdb196204349314490ff2b9d24f2c00
  | _ => 0

def compactPerms63 : Array (List Nat) := ([[], [33], [16], [16, 33], [32, 33], [32]] : List (List Nat)).toArray

def compactDomains63 : Array (Sig × Nat) := ([(subcube 0 8, 9), (subcube 0 32, 9), (subcube 32 0, 9), (subcube 0 1, 8), (subcube 0 2, 8), (subcube 0 4, 8), (subcube 16 0, 8), (subcube 1 0, 6), (subcube 2 0, 6), (subcube 4 0, 6), (subcube 0 48, 6), (subcube 0 3, 5)] : List (Sig × Nat)).toArray

def compactWords63 : Nat → Nat
  | 0 => 0x1fe0ff07f83fc1fe09391bc3fc121345718228ecc85ff02aaa7af934005ff83fc1fe034af7c460064b6d797600028949320cd90814f18c0ad8e897214e2d28428c04cd9425448e8c8e4a301505315222e0f7fff7f7f8c16222308185808003e69fe1fe0f4b16ffe0105fe1fe0a76ab3fe04b74002922c80cca71805929ab89d8327fff808003c2d4c63f
  | _ => 0

def compactCount63 (k : Nat) : Nat := match k with
  | 10 => 1
  | 9 => 2
  | 8 => 4
  | _ => 0

def compactPath63 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | 9 => readCompactBits compactWords63 (33 + 12*i) 12
  | 8 => let v := readCompactBits compactWords63 (369 + 13*i) 13
    (readCompactBits compactWords63 (345 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive63 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits compactWords63 (0 + 6*i) 6
  | 9 => readCompactBits compactWords63 (57 + 7*i) 7
  | 8 => readCompactBits compactWords63 (421 + 8*i) 8
  | _ => 0

def compactPoolIDs63 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits compactWords63 (27 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords63 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 9 => let v := readCompactBits compactWords63 (181 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords63 (71 + 5*(v &&& 31)) (5*n)
    compactIDsFromBits bits 5 n
  | 8 => let v := readCompactBits compactWords63 (747 + 10*i) 10
    let n := v >>> 6
    let bits := readCompactBits compactWords63 (453 + 6*(v &&& 63)) (6*n)
    compactIDsFromBits bits 6 n
  | _ => []

def compactBucket63 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let d := readCompactBits compactWords63 (199 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 12)
    let v := readCompactBits compactWords63 (201 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 8 => let d := readCompactBits compactWords63 (787 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 23)
    let v := readCompactBits compactWords63 (802 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []
theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid20502 : CompactGrid := (20502, 3, samplesP20502, samplesQ20502)
def tab20502 : CompactTable := (compactCount20502, compactPath20502, compactLive20502, compactPoolIDs20502, compactBucket20502)
def check20502 (k : Nat) := compactNode grid20502 tab20502 compactDomains20502 compactPerms20502 k
def sliceSpecs20502 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains20502 : ∀ d ∈ compactDomains20502, Slice true (vars 20502) (graphGoal 20502) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs20502)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs20502 : properPairs (graphGoal 20502) (asRow samplesP20502) (asRow samplesQ20502) :=
  compactPairs (g := grid20502) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos20502 : ∀ p ∈ compactPerms20502, autoOK (graphGoal 20502) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c20502k3p0 : chartBlock (check20502 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev20502k3 : chartBlock (check20502 3) 0 1 = true :=
  c20502k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded20502 : Impossible true (graphGoal 20502) 3 (vars 20502).toFinset := by
  apply compactRoot (g := grid20502) (t := tab20502) (dom := compactDomains20502) (perms := compactPerms20502) pairs20502 domains20502 autos20502
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev20502k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound20502 : Lower true (vars 20502) (graphGoal 20502) 4 :=
  plain_low (hints := 33562880) (by decide +kernel) excluded20502

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound20501 : Lower true (vars 20501) (graphGoal 20501) 4 :=
  carry_of (old := 20501) (rep := 20502) (swaps := [16]) (by decide +kernel) bound20502

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound20499 : Lower true (vars 20499) (graphGoal 20499) 4 :=
  carry_of (old := 20499) (rep := 20502) (swaps := [16, 33]) (by decide +kernel) bound20502

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound20487 : Lower true (vars 20487) (graphGoal 20487) 4 :=
  carry_of (old := 20487) (rep := 20502) (swaps := [16, 33, 66]) (by decide +kernel) bound20502

def grid20503 : CompactGrid := (20503, 6, samplesP20503, samplesQ20503)
def tab20503 : CompactTable := (compactCount20503, compactPath20503, compactLive20503, compactPoolIDs20503, compactBucket20503)
def check20503 (k : Nat) := compactNode grid20503 tab20503 compactDomains20503 compactPerms20503 k
def sliceSpecs20503 : List SliceSpec := [(1, 0, 20502, 0, 0, 4, 4), (2, 0, 20501, 0, 0, 4, 4), (4, 0, 20499, 0, 0, 4, 4), (16, 0, 20487, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains20503 : ∀ d ∈ compactDomains20503, Slice true (vars 20503) (graphGoal 20503) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(20502, 4), (20501, 4), (20499, 4), (20487, 4)]) (specs := sliceSpecs20503)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound20502
    · exact bound20501
    · exact bound20499
    · exact bound20487
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs20503 : properPairs (graphGoal 20503) (asRow samplesP20503) (asRow samplesQ20503) :=
  compactPairs (g := grid20503) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos20503 : ∀ p ∈ compactPerms20503, autoOK (graphGoal 20503) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c20503k3p0 : chartBlock (check20503 3) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev20503k3 : chartBlock (check20503 3) 0 2 = true :=
  c20503k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c20503k4p0 : chartBlock (check20503 4) 0 3 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev20503k4 : chartBlock (check20503 4) 0 3 = true :=
  c20503k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c20503k5p0 : chartBlock (check20503 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev20503k5 : chartBlock (check20503 5) 0 1 = true :=
  c20503k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c20503k6p0 : chartBlock (check20503 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev20503k6 : chartBlock (check20503 6) 0 1 = true :=
  c20503k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded20503 : Impossible true (graphGoal 20503) 6 (vars 20503).toFinset := by
  apply compactRoot (g := grid20503) (t := tab20503) (dom := compactDomains20503) (perms := compactPerms20503) pairs20503 domains20503 autos20503
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev20503k3
    · exact lev20503k4
    · exact lev20503k5
    · exact lev20503k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound20503 : Lower true (vars 20503) (graphGoal 20503) 7 :=
  plain_low (hints := 16781378) (by decide +kernel) excluded20503

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4646 : Lower true (vars 4646) (graphGoal 4646) 4 :=
  carry_of (old := 4646) (rep := 20502) (swaps := [84]) (by decide +kernel) bound20502

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound5157 : Lower true (vars 5157) (graphGoal 5157) 4 :=
  carry_of (old := 5157) (rep := 20502) (swaps := [16, 84]) (by decide +kernel) bound20502

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound6179 : Lower true (vars 6179) (graphGoal 6179) 4 :=
  carry_of (old := 6179) (rep := 20502) (swaps := [16, 33, 84]) (by decide +kernel) bound20502

def grid4135 : CompactGrid := (4135, 6, samplesP4135, samplesQ4135)
def tab4135 : CompactTable := (compactCount4135, compactPath4135, compactLive4135, compactPoolIDs4135, compactBucket4135)
def check4135 (k : Nat) := compactNode grid4135 tab4135 compactDomains4135 compactPerms4135 k
def sliceSpecs4135 : List SliceSpec := [(0, 1, 4646, 0, 0, 4, 4), (0, 2, 5157, 0, 0, 4, 4), (0, 4, 6179, 0, 0, 4, 4), (0, 32, 20487, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains4135 : ∀ d ∈ compactDomains4135, Slice true (vars 4135) (graphGoal 4135) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(4646, 4), (5157, 4), (6179, 4), (20487, 4)]) (specs := sliceSpecs4135)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound4646
    · exact bound5157
    · exact bound6179
    · exact bound20487
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs4135 : properPairs (graphGoal 4135) (asRow samplesP4135) (asRow samplesQ4135) :=
  compactPairs (g := grid4135) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos4135 : ∀ p ∈ compactPerms4135, autoOK (graphGoal 4135) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4135k3p0 : chartBlock (check4135 3) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4135k3 : chartBlock (check4135 3) 0 2 = true :=
  c4135k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4135k4p0 : chartBlock (check4135 4) 0 3 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4135k4 : chartBlock (check4135 4) 0 3 = true :=
  c4135k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4135k5p0 : chartBlock (check4135 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4135k5 : chartBlock (check4135 5) 0 1 = true :=
  c4135k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4135k6p0 : chartBlock (check4135 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4135k6 : chartBlock (check4135 6) 0 1 = true :=
  c4135k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded4135 : Impossible true (graphGoal 4135) 6 (vars 4135).toFinset := by
  apply compactRoot (g := grid4135) (t := tab4135) (dom := compactDomains4135) (perms := compactPerms4135) pairs4135 domains4135 autos4135
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev4135k3
    · exact lev4135k4
    · exact lev4135k5
    · exact lev4135k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4135 : Lower true (vars 4135) (graphGoal 4135) 7 :=
  plain_low (hints := 3221238086) (by decide +kernel) excluded4135

def grid4119 : CompactGrid := (4119, 5, samplesP4119, samplesQ4119)
def tab4119 : CompactTable := (compactCount4119, compactPath4119, compactLive4119, compactPoolIDs4119, compactBucket4119)
def check4119 (k : Nat) := compactNode grid4119 tab4119 compactDomains4119 compactPerms4119 k
def sliceSpecs4119 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains4119 : ∀ d ∈ compactDomains4119, Slice true (vars 4119) (graphGoal 4119) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs4119)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs4119 : properPairs (graphGoal 4119) (asRow samplesP4119) (asRow samplesQ4119) :=
  compactPairs (g := grid4119) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos4119 : ∀ p ∈ compactPerms4119, autoOK (graphGoal 4119) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4119k3p0 : chartBlock (check4119 3) 0 7 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4119k3 : chartBlock (check4119 3) 0 7 = true :=
  c4119k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4119k4p0 : chartBlock (check4119 4) 0 7 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4119k4 : chartBlock (check4119 4) 0 7 = true :=
  c4119k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4119k5p0 : chartBlock (check4119 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4119k5 : chartBlock (check4119 5) 0 1 = true :=
  c4119k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded4119 : Impossible true (graphGoal 4119) 5 (vars 4119).toFinset := by
  apply compactRoot (g := grid4119) (t := tab4119) (dom := compactDomains4119) (perms := compactPerms4119) pairs4119 domains4119 autos4119
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev4119k3
    · exact lev4119k4
    · exact lev4119k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4119 : Lower true (vars 4119) (graphGoal 4119) 6 :=
  plain_low (hints := 16789830) (by decide +kernel) excluded4119

def grid4662 : CompactGrid := (4662, 4, samplesP4662, samplesQ4662)
def tab4662 : CompactTable := (compactCount4662, compactPath4662, compactLive4662, compactPoolIDs4662, compactBucket4662)
def check4662 (k : Nat) := compactNode grid4662 tab4662 compactDomains4662 compactPerms4662 k
def sliceSpecs4662 : List SliceSpec := [(16, 0, 4646, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains4662 : ∀ d ∈ compactDomains4662, Slice true (vars 4662) (graphGoal 4662) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(4646, 4)]) (specs := sliceSpecs4662)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound4646
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs4662 : properPairs (graphGoal 4662) (asRow samplesP4662) (asRow samplesQ4662) :=
  compactPairs (g := grid4662) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos4662 : ∀ p ∈ compactPerms4662, autoOK (graphGoal 4662) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4662k4p0 : chartBlock (check4662 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4662k4 : chartBlock (check4662 4) 0 1 = true :=
  c4662k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded4662 : Impossible true (graphGoal 4662) 4 (vars 4662).toFinset := by
  apply compactRoot (g := grid4662) (t := tab4662) (dom := compactDomains4662) (perms := compactPerms4662) pairs4662 domains4662 autos4662
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev4662k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4662 : Lower true (vars 4662) (graphGoal 4662) 5 :=
  plain_low (hints := 2147492096) (by decide +kernel) excluded4662

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound5173 : Lower true (vars 5173) (graphGoal 5173) 5 :=
  carry_of (old := 5173) (rep := 4662) (swaps := [16]) (by decide +kernel) bound4662

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound6195 : Lower true (vars 6195) (graphGoal 6195) 5 :=
  carry_of (old := 6195) (rep := 4662) (swaps := [16, 33]) (by decide +kernel) bound4662

def grid4150 : CompactGrid := (4150, 4, samplesP4150, samplesQ4150)
def tab4150 : CompactTable := (compactCount4150, compactPath4150, compactLive4150, compactPoolIDs4150, compactBucket4150)
def check4150 (k : Nat) := compactNode grid4150 tab4150 compactDomains4150 compactPerms4150 k
def sliceSpecs4150 : List SliceSpec := [(0, 32, 20502, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains4150 : ∀ d ∈ compactDomains4150, Slice true (vars 4150) (graphGoal 4150) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(20502, 4)]) (specs := sliceSpecs4150)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound20502
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs4150 : properPairs (graphGoal 4150) (asRow samplesP4150) (asRow samplesQ4150) :=
  compactPairs (g := grid4150) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos4150 : ∀ p ∈ compactPerms4150, autoOK (graphGoal 4150) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4150k4p0 : chartBlock (check4150 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4150k4 : chartBlock (check4150 4) 0 1 = true :=
  c4150k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded4150 : Impossible true (graphGoal 4150) 4 (vars 4150).toFinset := by
  apply compactRoot (g := grid4150) (t := tab4150) (dom := compactDomains4150) (perms := compactPerms4150) pairs4150 domains4150 autos4150
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev4150k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4150 : Lower true (vars 4150) (graphGoal 4150) 5 :=
  plain_low (hints := 6476071936) (by decide +kernel) excluded4150

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4149 : Lower true (vars 4149) (graphGoal 4149) 5 :=
  carry_of (old := 4149) (rep := 4150) (swaps := [16]) (by decide +kernel) bound4150

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4147 : Lower true (vars 4147) (graphGoal 4147) 5 :=
  carry_of (old := 4147) (rep := 4150) (swaps := [16, 33]) (by decide +kernel) bound4150

def grid4151 : CompactGrid := (4151, 8, samplesP4151, samplesQ4151)
def tab4151 : CompactTable := (compactCount4151, compactPath4151, compactLive4151, compactPoolIDs4151, compactBucket4151)
def check4151 (k : Nat) := compactNode grid4151 tab4151 compactDomains4151 compactPerms4151 k
def sliceSpecs4151 : List SliceSpec := [(0, 32, 20503, 0, 0, 7, 7), (16, 0, 4135, 0, 0, 7, 7), (32, 0, 4119, 0, 0, 6, 6), (0, 1, 4662, 0, 0, 5, 5), (0, 2, 5173, 0, 0, 5, 5), (0, 4, 6195, 0, 0, 5, 5), (1, 0, 4150, 0, 0, 5, 5), (2, 0, 4149, 0, 0, 5, 5), (4, 0, 4147, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains4151 : ∀ d ∈ compactDomains4151, Slice true (vars 4151) (graphGoal 4151) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(20503, 7), (4135, 7), (4119, 6), (4662, 5), (5173, 5), (6195, 5), (4150, 5), (4149, 5), (4147, 5)]) (specs := sliceSpecs4151)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound20503
    · exact bound4135
    · exact bound4119
    · exact bound4662
    · exact bound5173
    · exact bound6195
    · exact bound4150
    · exact bound4149
    · exact bound4147
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs4151 : properPairs (graphGoal 4151) (asRow samplesP4151) (asRow samplesQ4151) :=
  compactPairs (g := grid4151) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos4151 : ∀ p ∈ compactPerms4151, autoOK (graphGoal 4151) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4151k6p0 : chartBlock (check4151 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4151k6 : chartBlock (check4151 6) 0 1 = true :=
  c4151k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4151k7p0 : chartBlock (check4151 7) 0 3 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4151k7 : chartBlock (check4151 7) 0 3 = true :=
  c4151k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c4151k8p0 : chartBlock (check4151 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev4151k8 : chartBlock (check4151 8) 0 1 = true :=
  c4151k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded4151 : Impossible true (graphGoal 4151) 8 (vars 4151).toFinset := by
  apply compactRoot (g := grid4151) (t := tab4151) (dom := compactDomains4151) (perms := compactPerms4151) pairs4151 domains4151 autos4151
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev4151k6
    · exact lev4151k7
    · exact lev4151k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4151 : Lower true (vars 4151) (graphGoal 4151) 9 :=
  plain_low (hints := 3238015302) (by decide +kernel) excluded4151

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16926 : Lower true (vars 16926) (graphGoal 16926) 6 :=
  carry_of (old := 16926) (rep := 4119) (swaps := [16, 32, 67, 64]) (by decide +kernel) bound4119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound17437 : Lower true (vars 17437) (graphGoal 17437) 6 :=
  carry_of (old := 17437) (rep := 4119) (swaps := [33, 67, 65]) (by decide +kernel) bound4119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound18459 : Lower true (vars 18459) (graphGoal 18459) 6 :=
  carry_of (old := 18459) (rep := 4119) (swaps := [67, 66]) (by decide +kernel) bound4119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound24591 : Lower true (vars 24591) (graphGoal 24591) 6 :=
  carry_of (old := 24591) (rep := 4119) (swaps := [67]) (by decide +kernel) bound4119

def grid16414 : CompactGrid := (16414, 4, samplesP16414, samplesQ16414)
def tab16414 : CompactTable := (compactCount16414, compactPath16414, compactLive16414, compactPoolIDs16414, compactBucket16414)
def check16414 (k : Nat) := compactNode grid16414 tab16414 compactDomains16414 compactPerms16414 k
def sliceSpecs16414 : List SliceSpec := [(0, 8, 20502, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains16414 : ∀ d ∈ compactDomains16414, Slice true (vars 16414) (graphGoal 16414) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(20502, 4)]) (specs := sliceSpecs16414)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound20502
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs16414 : properPairs (graphGoal 16414) (asRow samplesP16414) (asRow samplesQ16414) :=
  compactPairs (g := grid16414) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos16414 : ∀ p ∈ compactPerms16414, autoOK (graphGoal 16414) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16414k4p0 : chartBlock (check16414 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev16414k4 : chartBlock (check16414 4) 0 1 = true :=
  c16414k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded16414 : Impossible true (graphGoal 16414) 4 (vars 16414).toFinset := by
  apply compactRoot (g := grid16414) (t := tab16414) (dom := compactDomains16414) (perms := compactPerms16414) pairs16414 domains16414 autos16414
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev16414k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16414 : Lower true (vars 16414) (graphGoal 16414) 5 :=
  plain_low (hints := 169386752) (by decide +kernel) excluded16414

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16413 : Lower true (vars 16413) (graphGoal 16413) 5 :=
  carry_of (old := 16413) (rep := 16414) (swaps := [16]) (by decide +kernel) bound16414

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16411 : Lower true (vars 16411) (graphGoal 16411) 5 :=
  carry_of (old := 16411) (rep := 16414) (swaps := [16, 33]) (by decide +kernel) bound16414

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16399 : Lower true (vars 16399) (graphGoal 16399) 5 :=
  carry_of (old := 16399) (rep := 16414) (swaps := [16, 33, 66]) (by decide +kernel) bound16414

def grid16415 : CompactGrid := (16415, 8, samplesP16415, samplesQ16415)
def tab16415 : CompactTable := (compactCount16415, compactPath16415, compactLive16415, compactPoolIDs16415, compactBucket16415)
def check16415 (k : Nat) := compactNode grid16415 tab16415 compactDomains16415 compactPerms16415 k
def sliceSpecs16415 : List SliceSpec := [(0, 8, 20503, 0, 0, 7, 7), (0, 1, 16926, 0, 0, 6, 6), (0, 2, 17437, 0, 0, 6, 6), (0, 4, 18459, 0, 0, 6, 6), (0, 16, 24591, 0, 0, 6, 6), (1, 0, 16414, 0, 0, 5, 5), (2, 0, 16413, 0, 0, 5, 5), (4, 0, 16411, 0, 0, 5, 5), (16, 0, 16399, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains16415 : ∀ d ∈ compactDomains16415, Slice true (vars 16415) (graphGoal 16415) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(20503, 7), (16926, 6), (17437, 6), (18459, 6), (24591, 6), (16414, 5), (16413, 5), (16411, 5), (16399, 5)]) (specs := sliceSpecs16415)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound20503
    · exact bound16926
    · exact bound17437
    · exact bound18459
    · exact bound24591
    · exact bound16414
    · exact bound16413
    · exact bound16411
    · exact bound16399
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs16415 : properPairs (graphGoal 16415) (asRow samplesP16415) (asRow samplesQ16415) :=
  compactPairs (g := grid16415) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos16415 : ∀ p ∈ compactPerms16415, autoOK (graphGoal 16415) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16415k5p0 : chartBlock (check16415 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev16415k5 : chartBlock (check16415 5) 0 1 = true :=
  c16415k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16415k6p0 : chartBlock (check16415 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev16415k6 : chartBlock (check16415 6) 0 1 = true :=
  c16415k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16415k7p0 : chartBlock (check16415 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev16415k7 : chartBlock (check16415 7) 0 1 = true :=
  c16415k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16415k8p0 : chartBlock (check16415 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev16415k8 : chartBlock (check16415 8) 0 1 = true :=
  c16415k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded16415 : Impossible true (graphGoal 16415) 8 (vars 16415).toFinset := by
  apply compactRoot (g := grid16415) (t := tab16415) (dom := compactDomains16415) (perms := compactPerms16415) pairs16415 domains16415 autos16415
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev16415k5
    · exact lev16415k6
    · exact lev16415k7
    · exact lev16415k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16415 : Lower true (vars 16415) (graphGoal 16415) 9 :=
  plain_low (hints := 118264394) (by decide +kernel) excluded16415

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound8207 : Lower true (vars 8207) (graphGoal 8207) 6 :=
  carry_of (old := 8207) (rep := 4119) (swaps := [67]) (by decide +kernel) bound4119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound1564 : Lower true (vars 1564) (graphGoal 1564) 4 :=
  carry_of (old := 1564) (rep := 20502) (swaps := [33, 49]) (by decide +kernel) bound20502

def grid542 : CompactGrid := (542, 4, samplesP542, samplesQ542)
def tab542 : CompactTable := (compactCount542, compactPath542, compactLive542, compactPoolIDs542, compactBucket542)
def check542 (k : Nat) := compactNode grid542 tab542 compactDomains542 compactPerms542 k
def sliceSpecs542 : List SliceSpec := [(0, 2, 1564, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains542 : ∀ d ∈ compactDomains542, Slice true (vars 542) (graphGoal 542) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(1564, 4)]) (specs := sliceSpecs542)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound1564
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs542 : properPairs (graphGoal 542) (asRow samplesP542) (asRow samplesQ542) :=
  compactPairs (g := grid542) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos542 : ∀ p ∈ compactPerms542, autoOK (graphGoal 542) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c542k4p0 : chartBlock (check542 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev542k4 : chartBlock (check542 4) 0 1 = true :=
  c542k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded542 : Impossible true (graphGoal 542) 4 (vars 542).toFinset := by
  apply compactRoot (g := grid542) (t := tab542) (dom := compactDomains542) (perms := compactPerms542) pairs542 domains542 autos542
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev542k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound542 : Lower true (vars 542) (graphGoal 542) 5 :=
  plain_low (hints := 102277888) (by decide +kernel) excluded542

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound1053 : Lower true (vars 1053) (graphGoal 1053) 5 :=
  carry_of (old := 1053) (rep := 542) (swaps := [16]) (by decide +kernel) bound542

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound2075 : Lower true (vars 2075) (graphGoal 2075) 5 :=
  carry_of (old := 2075) (rep := 542) (swaps := [16, 33]) (by decide +kernel) bound542

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound2586 : Lower true (vars 2586) (graphGoal 2586) 4 :=
  carry_of (old := 2586) (rep := 20502) (swaps := [50]) (by decide +kernel) bound20502

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound3097 : Lower true (vars 3097) (graphGoal 3097) 4 :=
  carry_of (old := 3097) (rep := 20502) (swaps := [16, 50]) (by decide +kernel) bound20502

def grid31 : CompactGrid := (31, 8, samplesP31, samplesQ31)
def tab31 : CompactTable := (compactCount31, compactPath31, compactLive31, compactPoolIDs31, compactBucket31)
def check31 (k : Nat) := compactNode grid31 tab31 compactDomains31 compactPerms31 k
def sliceSpecs31 : List SliceSpec := [(0, 8, 4119, 0, 0, 6, 6), (0, 16, 8207, 0, 0, 6, 6), (0, 1, 542, 0, 0, 5, 5), (0, 2, 1053, 0, 0, 5, 5), (0, 4, 2075, 0, 0, 5, 5), (0, 3, 1564, 0, 0, 4, 4), (0, 5, 2586, 0, 0, 4, 4), (0, 6, 3097, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains31 : ∀ d ∈ compactDomains31, Slice true (vars 31) (graphGoal 31) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(4119, 6), (8207, 6), (542, 5), (1053, 5), (2075, 5), (1564, 4), (2586, 4), (3097, 4)]) (specs := sliceSpecs31)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound4119
    · exact bound8207
    · exact bound542
    · exact bound1053
    · exact bound2075
    · exact bound1564
    · exact bound2586
    · exact bound3097
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs31 : properPairs (graphGoal 31) (asRow samplesP31) (asRow samplesQ31) :=
  compactPairs (g := grid31) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos31 : ∀ p ∈ compactPerms31, autoOK (graphGoal 31) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k3p0 : chartBlock (check31 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k3 : chartBlock (check31 3) 0 1 = true :=
  c31k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k4p0 : chartBlock (check31 4) 0 26 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k4 : chartBlock (check31 4) 0 26 = true :=
  c31k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k5p0 : chartBlock (check31 5) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k5p1 : chartBlock (check31 5) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k5p2 : chartBlock (check31 5) 64 9 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k5 : chartBlock (check31 5) 0 73 = true :=
  (chartBlock_join (a := 32) (b := 41) c31k5p0 (chartBlock_join (a := 32) (b := 9) c31k5p1 c31k5p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k6p0 : chartBlock (check31 6) 0 31 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k6 : chartBlock (check31 6) 0 31 = true :=
  c31k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k7p0 : chartBlock (check31 7) 0 6 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k7 : chartBlock (check31 7) 0 6 = true :=
  c31k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k8p0 : chartBlock (check31 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k8 : chartBlock (check31 8) 0 1 = true :=
  c31k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded31 : Impossible true (graphGoal 31) 8 (vars 31).toFinset := by
  apply compactRoot (g := grid31) (t := tab31) (dom := compactDomains31) (perms := compactPerms31) pairs31 domains31 autos31
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev31k3
    · exact lev31k4
    · exact lev31k5
    · exact lev31k6
    · exact lev31k7
    · exact lev31k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound31 : Lower true (vars 31) (graphGoal 31) 9 :=
  plain_low (hints := 119321422) (by decide +kernel) excluded31

def sixTarget (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372968 * 2 ^ 32 + 3974160576) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sixGraph : Sig := 0xfffefe80aa80aa80fffefe80aa80aa80fffefe80aa80aa80fffefe80aa80aa80fffefe80aa80aa80fffefe80aa80aa80fffefe80aa80aa80fffefe80aa80aa80
def sixInputs : List Sig := [inputs.getD 5 zero, inputs.getD 0 zero, inputs.getD 3 zero, inputs.getD 1 zero, inputs.getD 2 zero, inputs.getD 4 zero]
def sixSample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)

set_option maxRecDepth 8192 in
private theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
private theorem sixSampled (r : Row) : List.ofFn (sixSample r) = sixInputs.map (bit r) := by
  rw [← sixList, List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sixTable : ∀ r : Row, bit r sixGraph = sixTarget (sixSample r) := by decide +kernel

private theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (i : Nat) (r : Row) :
    bit r ((execute C.gates sixInputs).getD i zero) = (C.wires (List.ofFn (sixSample r))).getD i false := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), sixSampled]
  rfl

private theorem observeComplement (a : Sig) : observe (~~~a) = inv (observe a) := by
  funext r
  simp only [observe, inv, bit, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]

private theorem lowerComplement {base G L} (low : Lower true base G L) :
    Lower true base (~~~G) L := by
  intro p bank run hit
  apply low p bank run
  rw [observeComplement] at hit
  simpa only [inv_inv'] using avail_inv (u := true) rfl hit

def signedFreeWord (base : List Sig) (w : Sig) : Bool := freeWord base w || freeWord base (~~~w)

private theorem signedFreeWord_ok {base w} (ok : signedFreeWord base w = true) :
    Available true (base.map observe) (observe w) := by
  rw [signedFreeWord, Bool.or_eq_true] at ok
  rcases ok with positive | negative
  · exact freeWord_ok positive
  · have h := freeWord_ok (u := true) negative
    rw [observeComplement] at h
    simpa only [inv_inv'] using avail_inv (u := true) rfl h

def flipInput (i : Nat) : Move :=
  let a := inputs.getD i zero
  (~~~a, a, Fin.ofNat 512 (1 <<< i))
def dualMoves : List Move := fixRows 0 32 ++ [flipInput 0, flipInput 1, flipInput 2, flipInput 3, flipInput 4]
def pinWitness : List (Sig × Row × Row) := [(inputs.getD 5 zero, 10, 42)]

private theorem sixProper : proper sixGraph := proper_of _ (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sixLower : Lower true sixInputs sixGraph 10 := by
  have essential : checkEssential sixGraph sixInputs pinWitness = true := by decide +kernel
  have mapped : rename (movedRow dualMoves) sixGraph = ~~~(graphGoal 31) := by
    rw [← moved_eq_rename]
    decide +kernel
  have cover : ∀ a ∈ sixInputs, Available true ((vars 31).map observe)
      (observe (rename (movedRow dualMoves) a)) := by
    have check : sixInputs.all (fun a => signedFreeWord (vars 31) (movedWord dualMoves a)) = true := by
      decide +kernel
    intro a ha
    rw [← moved_eq_rename]
    exact signedFreeWord_ok (List.all_eq_true.mp check a ha)
  have constant : ∀ a ∈ (pinWitness.map Prod.fst).toFinset,
      Constant (observe (rename (movedRow dualMoves) a)) := by
    intro a ha
    have eq : a = inputs.getD 5 zero := by simpa [pinWitness] using ha
    rw [eq, ← moved_eq_rename]
    have v : movedWord dualMoves (inputs.getD 5 zero) = one := by decide +kernel
    rw [v]
    exact ⟨true, funext bit_one⟩
  have result := lower_slice sixProper (essential_plain essential).1 (essential_plain essential).2
    (proper_of _ (by decide +kernel)) (movedRow dualMoves) mapped cover _
    (essential_ok essential) constant 9 (lowerComplement bound31)
  have card : (pinWitness.map Prod.fst).toFinset.card = 1 := by decide +kernel
  rw [card] at result
  exact result

private theorem binaryFloor (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = sixTarget x) :
    10 ≤ C.gates.countP (fun g => !isNot g) := by
  have goalEq : (execute C.gates sixInputs).getD C.output zero = sixGraph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sixSample r)).trans (sixTable r).symm)
  have out := get_rep (u := true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have plain : bit 0 sixGraph = false := by decide +kernel
  rw [nrm_id plain] at out
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates sixInputs legal (by simp) sixProper
    (out.resolve_right (fun h => h sixProper))
  have ns : sixInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (sixInputs.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, B, reach, hit, hq⟩ := contraction (observe_proper sixProper) rr _ Reach.start supplied
  have bound := sixLower q B reach hit
  omega

def monoCircuit : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩
private theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 monoCircuit := by
  intro g hg
  simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
private theorem witnessEval : ∀ x : Fin 6 → Bool, monoCircuit.eval (List.ofFn x) = sixTarget x := by
  decide +kernel

end PEqualNP.Outside.L_meta_39769

open PEqualNP.Outside.L_meta_39769 in
theorem PEqualNP.Outside.L_meta_39769 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3974160576) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3974160576) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨C, legal, size, computes⟩ := hs
  by_cases noNot : ∀ g ∈ C.gates, g.op ≠ .not
  · refine ⟨C, ?_, size, computes⟩
    intro g hg
    obtain ⟨op, arity⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (noNot g hg))), arity⟩
  · push Not at noNot
    obtain ⟨g, hg, hop⟩ := noNot
    have paid : C.gates.countP (fun q => !isNot q) < C.gates.length := by
      by_contra! bad
      have equality := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) g hg
      simp [isNot, hop] at equality
    have low := binaryFloor C legal computes
    refine ⟨monoCircuit, witnessMonotone, ?_, witnessEval⟩
    change C.gates.length ≤ s at size
    change 11 ≤ s
    omega

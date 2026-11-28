import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31243_aux


open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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


abbrev Row := Fin 256
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

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

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
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

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

abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 65536 then
    let r := Fin.ofNat 256 (code % 256)
    let s := Fin.ofNat 256 (code / 256)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 131072 then
    match cuts[code-65536]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-131072]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 262144) &&
      checkMoves T k cuts links rest (data / 262144)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 8).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input


def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)


def fixes (q : Nat) : List Move :=
  ((List.range 8).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 256 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 8).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 256 r,Fin.ofNat 256 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2




def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128080810128200a08028080a08028200810108404210120404212008480a02020600818020404818020600a02008480212008404818020600a08008480a08008404212008480a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

theorem lower225 : Claim 225 5 :=
  fromLift 5 64 5 lower161 (by decide +kernel)

def cuts168 : Cuts (goalAt 168) := []

def state168_0 : List Sig := roots 168
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude168_0 : Impossible true (goalAt 168) 3 state168_0.toFinset :=
  node_ok cuts168 [] 0x28080280828080880828200a08028080a0802820088080a02028082202028200a080a02022200888022020888022200a0200a08028200a020888022200a0800a080a0800a02028200a080a080222008880 (by decide +kernel)

theorem lower168 : Claim 168 4 :=
  fromSearch 808472576 (by decide +kernel) exclude168_0

theorem lower232 : Claim 232 5 :=
  fromLift 5 64 858804224 lower168 (by decide +kernel)

def cuts137 : Cuts (goalAt 137) := []

def state137_0 : List Sig := roots 137
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude137_0 : Impossible true (goalAt 137) 3 state137_0.toFinset :=
  node_ok cuts137 [] 0x220200901220208101222008880220208880222008101024040901204040908024208808206008180204048180206008808024200908024048180206008880024208880024040908024208880206008180 (by decide +kernel)

theorem lower137 : Claim 137 4 :=
  fromSearch 3 (by decide +kernel) exclude137_0

theorem lower201 : Claim 201 5 :=
  fromLift 5 64 3 lower137 (by decide +kernel)

def rule169_0 : {c : Cut // CutGood (goalAt 169) c} :=
  ruleFor 169 lower168 none (by decide +kernel)

def rule169_1 : {c : Cut // CutGood (goalAt 169) c} :=
  ruleFor 169 lower161 none (by decide +kernel)

def rule169_2 : {c : Cut // CutGood (goalAt 169) c} :=
  ruleFor 169 lower137 none (by decide +kernel)

def cuts169 : Cuts (goalAt 169) := [rule169_0,rule169_1,rule169_2]

def state169_0 : List Sig := roots 169
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude169_0 : Impossible true (goalAt 169) 5 state169_0.toFinset :=
  node_ok cuts169 [] 0x40008a0200a020a02040008880828200a08040008a02028200a0804000888080a02028084000488080a080282040004a02022200888040004880822200888040004a0200a080282040004280822200888040004a0800a080a0804000428080a080282040004a08022200888040000810108480212040000a02020600818040000810120600818040000a02008480212040000210120600818040000a08008480a08040000210108480212040000a080206008180400000901206008180400008880024208880400000901024200908400008880206008180 (by decide +kernel)

theorem lower169 : Claim 169 6 :=
  fromSearch 3 (by decide +kernel) exclude169_0

def cuts73 : Cuts (goalAt 73) := []

def state73_0 : List Sig := roots 73
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude73_0 : Impossible true (goalAt 73) 3 state73_0.toFinset :=
  node_ok cuts73 [] 0x120200901120204101121004840120204840121004101024040901104040908024204808105004140104044140105004808024200908024044140105004840024204840024040908024204840105004140 (by decide +kernel)

theorem lower73 : Claim 73 4 :=
  fromSearch 3 (by decide +kernel) exclude73_0

theorem lower105 : Claim 105 5 :=
  fromLift 5 32 3 lower73 (by decide +kernel)

def cuts41 : Cuts (goalAt 41) := []

def state41_0 : List Sig := roots 41
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude41_0 : Impossible true (goalAt 41) 3 state41_0.toFinset :=
  node_ok cuts41 [] 0xa02009010a02021010a08028200a02028200a0802101024040901084040908024202808084802120084042120084802808024200908024042120084802820024202820024040908024202820084802120 (by decide +kernel)

theorem lower41 : Claim 41 4 :=
  fromSearch 3 (by decide +kernel) exclude41_0

def rule233_0 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower225 none (by decide +kernel)

def rule233_1 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower232 none (by decide +kernel)

def rule233_2 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower201 none (by decide +kernel)

def rule233_3 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower169 none (by decide +kernel)

def rule233_4 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower105 none (by decide +kernel)

def rule233_5 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower73 none (by decide +kernel)

def rule233_6 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower137 none (by decide +kernel)

def rule233_7 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower168 none (by decide +kernel)

def rule233_8 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower161 none (by decide +kernel)

def rule233_9 : {c : Cut // CutGood (goalAt 233) c} :=
  ruleFor 233 lower41 none (by decide +kernel)

def cuts233 : Cuts (goalAt 233) := [rule233_0,rule233_1,rule233_2,rule233_3,rule233_4,rule233_5,rule233_6,rule233_7,rule233_8,rule233_9]

def state233_0 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_0 : Impossible true (goalAt 233) 4 state233_0.toFinset :=
  node_ok cuts233 [] 0xa06022020a06012020a06038300e0c002420a08038300e0c002420880828180880828180480808404480802404090838300090838300c8c018580a06022020616012020616018581000630700c1c018580e0c0 (by decide +kernel)

def state233_1 : List Sig := [0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa,input 3,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_1 : Impossible true (goalAt 233) 4 state233_1.toFinset :=
  node_ok cuts233 [] 0x28180880828180280818580a0602040461600242061601858009081858068600242061603070068602818088081a18028081a180686002404c8c028180e0c038301000528200e0c0383010003 (by decide +kernel)

def state233_2 : List Sig := [0xff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa,input 3,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_2 : Impossible true (goalAt 233) 4 state233_2.toFinset :=
  node_ok cuts233 [] 0xa06022020a0600a020616028180810118580090818580616002420c9c032300090832300484032300c8c01a300888032300c8c022300a06038300e0c022020a08038300e0c00a020c1c0307006160383006860 (by decide +kernel)

def state233_3 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_3 : Impossible true (goalAt 233) 5 state233_3.toFinset :=
  node_ok cuts233 [⟨state233_0,exclude233_0⟩,⟨state233_1,exclude233_1⟩,⟨state233_2,exclude233_2⟩] 0x88081a180686028180c8c032300880832300c8c02818068601a180480822200888008404c8c032300480832300c8c008404888022302000232300c8c03830068603830200011a180686038300c8c032300a06012020a06022021000622020a06040014a06022020480812020810118580616028181000728180810140014810128180616018580090118580616032301000732300090180000090132300616032300210140018210112020616018580210118580616012021000712021000240008c1c028181000528180880838300e0c028180e0c038300880840014880808405000328200480838300e0c008404e0c03830048084000c4808 (by decide +kernel)

def state233_4 : List Sig := [0x5555555555005500555555555500550055555555550055005555555555005500,input 0,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_4 : Impossible true (goalAt 233) 4 state233_4.toFinset :=
  node_ok cuts233 [] 0xa06022020a0600a02068602818088081a18028081a180686002404414030700c1c018700818030700c1c020700c1c032700090130700a06038300e0c020404a08038300e0c008404c8c0323006860383006160 (by decide +kernel)

def state233_5 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_5 : Impossible true (goalAt 233) 4 state233_5.toFinset :=
  node_ok cuts233 [] 0xa06022020a0600a020a06038300e0c002404a08038300e0c002404090828180810128180090808420410102420090138300090838300c1c01a180a0602202068600a02068601a181000632300c8c01a180e0c0 (by decide +kernel)

def state233_6 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_6 : Impossible true (goalAt 233) 5 state233_6.toFinset :=
  node_ok cuts233 [⟨state233_1,exclude233_1⟩,⟨state233_4,exclude233_4⟩,⟨state233_5,exclude233_5⟩] 0x810118580616028180c1c030700810130700c1c02818061601858041012060081800a020c1c030700410130700c1c00a020818020701000830700c1c01a18009081a18200020242009081a180c1c030702000130700c1c038300616038302000018580616038300c1c030700a0600a020a06022021000622020a06040014a0602202028080a02088081a18068602818100082818088084001488082818068601a18028084001828081040468601a18028081a180686010405000810405000240008c8c028181000528180810138300e0c028180e0c03830081014001481010a021000328200410138300e0c00a020e0c03830041014000c4101 (by decide +kernel)

def state233_7 : List Sig := [0xffaaffaa000000000000000000000000ffaaffaa,input 0,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_7 : Impossible true (goalAt 233) 4 state233_7.toFinset :=
  node_ok cuts233 [] 0xa06038300e0c022020686032300c8c01a180c8c038300686032300616030700c1c018580c1c038300616030700c1c032300090830700480828180880828180280822300c8c012020c8c020700c1c002420c1c0 (by decide +kernel)

def state233_8 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_8 : Impossible true (goalAt 233) 5 state233_8.toFinset :=
  node_ok cuts233 [⟨state233_1,exclude233_1⟩,⟨state233_0,exclude233_0⟩,⟨state233_5,exclude233_5⟩,⟨state233_7,exclude233_7⟩] 0x28180e0c038300880828200a06022020a06012020880828180880828180090138302000238300480810404480802404c8c002420a06020404a06002420e0c080004e0c00242048081040409080240409084001cc1c022020a06022020a06040008e0c080000e0c0120220003120210006 (by decide +kernel)

def state233_9 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 5,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_9 : Impossible true (goalAt 233) 6 state233_9.toFinset :=
  node_ok cuts233 [⟨state233_3,exclude233_3⟩,⟨state233_6,exclude233_6⟩,⟨state233_8,exclude233_8⟩] 0x4001488081a180686040020a06032300c8c040014880832300c8c040020a0601a180686040009000232300c8c040008e0c01a180e0c04000a00011a180686040008e0c032300c8c040018480822200888040020410132300c8c040018480832300c8c04002041012220088c04001481011858061604001ca06030700c1c040014810130700c1c04001ca06018580616040020090130700c1c04001cc8c002420c8c08000809010242009084001cc8c030700c1c040009000230700c1c040008e0c018580e0c04000a000018580616040008e0c030700c1c04001841012060081804001c480830700c1c040018410130700c1c04001c48082060081c040008a06040014a06040008880838300e0c040008a06038300e0c04000888084000888084000d00034000ca08040018a06012020a06040018880840018880840018a06040014a060400188808120204808 (by decide +kernel)

def state233_10 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_10 : Impossible true (goalAt 233) 4 state233_10.toFinset :=
  node_ok cuts233 [] 0x280838300e0c00a020a06038300e0c002420a02028180a06002420280838300280838300480810404480802404090828180090828180c8c030700e0c00a020c1c012020c1c030701000918580c1c030700a060 (by decide +kernel)

def state233_11 : List Sig := [0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_11 : Impossible true (goalAt 233) 4 state233_11.toFinset :=
  node_ok cuts233 [] 0xa020e0c038300280828180e0c038301000630700e0c008404c1c002420c1c030700090830700c8c002420c1c018580c8c038300280832300480832300c8c002404686028080a060281810003 (by decide +kernel)

def state233_12 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa,input 3,input 0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_12 : Impossible true (goalAt 233) 4 state233_12.toFinset :=
  node_ok cuts233 [] 0x280838300e0c00a020c1c038300210130700090830700c1c002420c1c01a18009083070048403830068603830028201a18068600a180e0c028180e0c00a020a02028180a06012020c1c018580c1c028180c8c0 (by decide +kernel)

def state233_13 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_13 : Impossible true (goalAt 233) 5 state233_13.toFinset :=
  node_ok cuts233 [⟨state233_10,exclude233_10⟩,⟨state233_11,exclude233_11⟩,⟨state233_12,exclude233_12⟩] 0x100050a020280812020e0c038301000538300e0c01202028080a020a0600a020a06040018e0c038300a06038300e0c04001828080a020280832300c8c03830068603830028081a180686038300c8c03230048080a080282010404c8c032300480832300c8c01040428200a18200021a180686028180c8c032302000132300c8c02818068601a180210130700c1c038301000738300210140014210138300c1c030700090130700c1c032301000732300090180000090132300c1c030700410140024410112020c1c030700410130700c1c012021000712021000440010616010405000328080480828180a06010404a0602818048084000c4808 (by decide +kernel)

def state233_14 : List Sig := [0x5555555555555555555555555555555555005500550055005500550055005500,input 0,input 3,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_14 : Impossible true (goalAt 233) 4 state233_14.toFinset :=
  node_ok cuts233 [] 0x280838300e0c00a020c8c038300280832300480832300c8c002404414038300616038300212018580616008580616032300090132300e0c028180e0c008404a02028180a06010404c8c01a180c8c028180c1c0 (by decide +kernel)

def state233_15 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_15 : Impossible true (goalAt 233) 4 state233_15.toFinset :=
  node_ok cuts233 [] 0x280838300e0c00a020a06038300e0c002404a02028180a06002404090838300210138300090812020410102420090128180090828180c1c032300e0c00a020c8c012020c8c03230100091a180c8c032300a060 (by decide +kernel)

def state233_16 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_16 : Impossible true (goalAt 233) 5 state233_16.toFinset :=
  node_ok cuts233 [⟨state233_11,exclude233_11⟩,⟨state233_14,exclude233_14⟩,⟨state233_15,exclude233_15⟩] 0x100050a020280812020e0c038301000538300e0c01202028080a020a06008404a06040018e0c038300a06038300e0c040018210108404210130700c1c038300616038300210118580616038300c1c030700410108480212012020c1c030700410130700c1c012020212008581000830700c1c032300090832302000202420090832300c1c030702000118580616028180c1c030702000030700c1c028180616018580280832300c8c038301000838300280840014280838300c8c032300480840024480810404c8c032300480832300c8c010405000810405000440010686012021000328080410128180a06012020a0602818041014000c4101 (by decide +kernel)

def state233_17 : List Sig := [0xffaaffaaffaaffaa,input 0,input 3,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_17 : Impossible true (goalAt 233) 4 state233_17.toFinset :=
  node_ok cuts233 [] 0xa06038300e0c00a020c8c038300686032300686032300c8c01a180c1c038300616030700616030700c1c018580c1c03230009083070028083830028083830088080a180c8c012020c8c008580c1c002420c1c0 (by decide +kernel)

def state233_18 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_18 : Impossible true (goalAt 233) 5 state233_18.toFinset :=
  node_ok cuts233 [⟨state233_11,exclude233_11⟩,⟨state233_10,exclude233_10⟩,⟨state233_15,exclude233_15⟩,⟨state233_17,exclude233_17⟩] 0x28180e0c03830028080a020e0c038300280828080280838300280838300090128182000228180480810404480802404c8c002420e0c008404e0c002420a06080004a0600242048081040409080240409084001cc1c00a020e0c00a020e0c040010a06080000a060120220003120210009 (by decide +kernel)

def state233_19 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_19 : Impossible true (goalAt 233) 6 state233_19.toFinset :=
  node_ok cuts233 [⟨state233_13,exclude233_13⟩,⟨state233_16,exclude233_16⟩,⟨state233_18,exclude233_18⟩] 0x40010a0600a020a06040011000638300e0c040010a06038300e0c04001100040a02028084001500050a020280840018480838300e0c040015000538300e0c04001848080a020280840018280832300c8c040020e0c01a180e0c04001428081a180686040020e0c032300c8c04001100041a180686040010a06032300c8c040012000132300c8c040010a0601a18068604002448080a080282040020410132300c8c040024480832300c8c04002041010a080286040018210130700c1c04001ce0c018580e0c04001421011858061604001ce0c030700c1c040020090130700c1c04001cc8c002420c8c08000809010242009084001cc8c030700c1c040011000418580616040010a06030700c1c040012000030700c1c040010a0601858061604002441010848021204001c480830700c1c040024410130700c1c04001c48080848021604000d00034000ca020 (by decide +kernel)

def state233_20 : List Sig := [0xffffffff00000000ffffffffffaaffaa,input 5,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_20 : Impossible true (goalAt 233) 3 state233_20.toFinset :=
  node_ok cuts233 [] 0x32300e0c01a180c8c030700c8c002420c1c030700e0c018580c1c01a180c8c01a180c8c018580c1c018580c1c00a020e0c028180e0c0 (by decide +kernel)

def state233_21 : List Sig := [0xffffffff00000000ffffffffffaaffaaffffffff00000000ffffffffffaaffaa,input 5,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_21 : Impossible true (goalAt 233) 4 state233_21.toFinset :=
  node_ok cuts233 [⟨state233_20,exclude233_20⟩] 0x686032300c8c01a180c8c01a180686032300c8c022300686032300616030700c1c018580c1c032300090830700c1c018580616030700c1c020700616030700a06022020a0600a020e0c0281820000281804808 (by decide +kernel)

def state233_22 : List Sig := [0xffffffff00000000ffffffff000000000000000000000000ffaaffaa,input 7,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_22 : Impossible true (goalAt 233) 3 state233_22.toFinset :=
  node_ok cuts233 [] 0x1a180c8c032300686030700c8c002420c1c018580c1c030700616032300686032300e0c030700616030700e0c00a020e0c038300a060 (by decide +kernel)

def state233_23 : List Sig := [0xffffffffffffffffffffffffffffffff0000000000000000ffaaffaaffaaffaa,input 7,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_23 : Impossible true (goalAt 233) 4 state233_23.toFinset :=
  node_ok cuts233 [⟨state233_22,exclude233_22⟩] 0x280838300e0c00a022000038300e0c012020c8c038300686032300686032300c8c01a180686032300c8c01a180c1c038300616030700c1c032300090830700616030700c1c018580616030700c1c018580a060 (by decide +kernel)

def state233_24 : List Sig := [0xffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa,input 0,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_24 : Impossible true (goalAt 233) 5 state233_24.toFinset :=
  node_ok cuts233 [⟨state233_7,exclude233_7⟩,⟨state233_17,exclude233_17⟩,⟨state233_21,exclude233_21⟩,⟨state233_23,exclude233_23⟩] 0x28180280828180880838300e0c028180e0c03830088080a02028082202068601a180a06032300c8c022020c8c032300a0601a18068600a020c8c032300e0c01a180e0c00a02068601a180e0c032300c8c020404616018580a06030700c1c020404c1c030700a06018580616008404c1c030700e0c018580e0c008404616018580e0c030700c1c002404c1c030700c8c002420c8c002404090802420c8c030700c1c022020480812020a06080004a06022022000322020a06012020a0600a02048080a020e0c080000e0c00a02200020a020e0c012020e0c002404410122300c8c012020c8c002404480812020c8c010404c8c002420480820700c1c010404c1c002420410102420c1c012020c1c0 (by decide +kernel)

def state233_25 : List Sig := [0xffffffffffaaffaa0000000000000000ffffffffffaaffaa,input 5,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_25 : Impossible true (goalAt 233) 4 state233_25.toFinset :=
  node_ok cuts233 [] 0x1a180c8c032300686032300e0c01a180c8c018580c1c030700616030700c8c002420c1c030700e0c018580c1c038180e0c038300280828180a06028080e06022300c8c00a080c8c020700c1c008480c1c028300e0c00a020e0c0 (by decide +kernel)

def state233_26 : List Sig := [0xffffffffffaaffaaffffffffffaaffaa,input 5,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_26 : Impossible true (goalAt 233) 4 state233_26.toFinset :=
  node_ok cuts233 [] 0x22200c8c03230088c032300e0c01a180c8c020600c1c03070081c030700c8c002420c1c030700e0c018580c1c028200e0c038300a0c028180a06038180a0201a180c8c01a180c8c018580c1c018580c1c00a020e0c038180e0c0 (by decide +kernel)

def state233_27 : List Sig := [0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa,input 5,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_27 : Impossible true (goalAt 233) 5 state233_27.toFinset :=
  node_ok cuts233 [⟨state233_1,exclude233_1⟩,⟨state233_25,exclude233_25⟩,⟨state233_26,exclude233_26⟩] 0xe06028080a0602818068603818088081a18028201a18068600a18028081a180686012180c8c018580e06020404616008480616018580216018580686002420616002420616018580416030700e06022020e0600a02028081202200000a020e0c0381820002381810004120220001120210003 (by decide +kernel)

def state233_28 : List Sig := [0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 5,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_28 : Impossible true (goalAt 233) 5 state233_28.toFinset :=
  node_ok cuts233 [⟨state233_7,exclude233_7⟩] 0xe06028080a0602818068603818088081a18028201a18068600a180e8c03830068603830061603818081011858021201858061600858061601a180090818580e1c038300616038300e06038300e0c022020a08038300e0c02830088083818088083818048088000048084000cc8c03230009011a180c1c0307000908185802808 (by decide +kernel)

def state233_29 : List Sig := [0xffaaffaaffaaffaa0000000000000000ffaaffaaffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_29 : Impossible true (goalAt 233) 5 state233_29.toFinset :=
  node_ok cuts233 [] 0x28180e0c038300280822020a06022020a0600a020e0c00a020e0c0323000908281808101281800908383002101383000901024210007307008808281808808281802808383002808383004808281808808281802808383002808383000901120204808104040908104040908120210003 (by decide +kernel)

def state233_30 : List Sig := [0xffffffff00000000ffffffff00000000ffaaffaa00000000ffaaffaa,input 7,input 0,input 3,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_30 : Impossible true (goalAt 233) 4 state233_30.toFinset :=
  node_ok cuts233 [] 0x38180a02028180a06022200c8c03230088c01a180c8c032300686020600c1c03070081c030700c8c002420c1c018580c1c030700616028300e0c038300a08032300686032300e0c030700616030700e0c00a020e0c038300e060 (by decide +kernel)

def state233_31 : List Sig := [0xffffffffffffffff0000000000000000ffaaffaaffaaffaa,input 7,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_31 : Impossible true (goalAt 233) 4 state233_31.toFinset :=
  node_ok cuts233 [] 0x38180e0c038300280832300e0c01a180c8c01a180c8c032300686030700e0c018580c1c030700c8c002420c1c018580c1c030700616028300e0c028200e0c022300c8c022200c8c020700c1c020600c1c028180a06022020e060 (by decide +kernel)

def state233_32 : List Sig := [0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_32 : Impossible true (goalAt 233) 5 state233_32.toFinset :=
  node_ok cuts233 [⟨state233_11,exclude233_11⟩,⟨state233_30,exclude233_30⟩,⟨state233_31,exclude233_31⟩] 0x48082202200001202200021202048084000ca08038300e0c028300280838300e0c00a022000138300e0c040008888032300c8c022300c8c038300280832300880832300c8c012300686020600c1c03070081c030700e0c008404c1c030700c8c002420c1c002420c1c03070041c018580e060 (by decide +kernel)

def state233_33 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_33 : Impossible true (goalAt 233) 5 state233_33.toFinset :=
  node_ok cuts233 [⟨state233_17,exclude233_17⟩] 0xe06028080a06028180a08038300e0c028300e06038300e0c00a020888032300c8c022300c8c038300280832300e86032300c8c038180818030700c1c020700c1c038300210130700c1c032300090830700e16030700c1c03818048088000048084000c2808383002808383006860323000901323006160307000908307008808 (by decide +kernel)

def state233_34 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_34 : Impossible true (goalAt 233) 4 state233_34.toFinset :=
  node_ok cuts233 [] 0x38180a02028180a06018580c96022020616008480616018580296030700c1c018580486032300c8c018580416038180880838180090802420480810404090838300e0c0024210000381808101381800901120204101120200901 (by decide +kernel)

def state233_35 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_35 : Impossible true (goalAt 233) 5 state233_35.toFinset :=
  node_ok cuts233 [⟨state233_0,exclude233_0⟩,⟨state233_34,exclude233_34⟩] 0x38180a02028180a06022020e06022020e06012020410112020090132300090108406000102404090802404090840000616038180880818580212018580616008580210118580616010580c1c030700616040000e06022020e06022020210112022000012020e0c0381808808381800908024204808104040908 (by decide +kernel)

def state233_36 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_36 : Impossible true (goalAt 233) 4 state233_36.toFinset :=
  node_ok cuts233 [] 0x12020090810404090810404480812020090128200e0c038300a0c00a020e0c038300090808404e0c038300090120600c1c03070089c030700e0c00a020c1c018580c1c03070048c01a180c1c03070041c038180e060024210000 (by decide +kernel)

def state233_37 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_37 : Impossible true (goalAt 233) 5 state233_37.toFinset :=
  node_ok cuts233 [⟨state233_10,exclude233_10⟩,⟨state233_36,exclude233_36⟩] 0x12020810180000480812020090810404090828200e0c038300a0c00a020e0c03830028080a020e0c03830009081202041011202009010a020e0c00a020e0c032300090120406000102404090802404090840000818030700c1c020700c1c038300280830700810130700c1c010700616030700c1c040000e060 (by decide +kernel)

def state233_38 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_38 : Impossible true (goalAt 233) 5 state233_38.toFinset :=
  node_ok cuts233 [⟨state233_5,exclude233_5⟩,⟨state233_34,exclude233_34⟩] 0x38180a02028180a06002420e06020404e0600242048081040409083070009080842200010242009010242009084000468603818088081a18028201a18068600a18028081a180686012180c8c032300686040004e06022020e0600a02028081202200000a020e0c0381808101381800901120204101120200901 (by decide +kernel)

def state233_39 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_39 : Impossible true (goalAt 233) 5 state233_39.toFinset :=
  node_ok cuts233 [⟨state233_36,exclude233_36⟩,⟨state233_15,exclude233_15⟩] 0x12020880880004480810404480812020090128200e0c038300a0c00a020e0c038300280808404e0c038300090102420480810404090802420e0c008404e0c030700090820422000002420090102420090840004888032300c8c022300c8c038300280832300880832300c8c012300686032300c8c040010e060 (by decide +kernel)

def state233_40 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_40 : Impossible true (goalAt 233) 6 state233_40.toFinset :=
  node_ok cuts233 [⟨state233_8,exclude233_8⟩,⟨state233_18,exclude233_18⟩,⟨state233_24,exclude233_24⟩,⟨state233_27,exclude233_27⟩,⟨state233_28,exclude233_28⟩,⟨state233_29,exclude233_29⟩,⟨state233_32,exclude233_32⟩,⟨state233_33,exclude233_33⟩,⟨state233_35,exclude233_35⟩,⟨state233_37,exclude233_37⟩,⟨state233_38,exclude233_38⟩,⟨state233_39,exclude233_39⟩] 0xe06012020e06028081000728080e06080004a06028080480828180e0600a020e06022020e0c038300e06038300e0c02202028080a021000728200a08012020e0c038302000038300e0c012020a0802830088080240488083818100003818088088002c88083818009013818048080240448081040500001040448084001c480810404090102404280802404280838301000038300280880028280838300090138301000040004c8c020404090802420e06040004e06020406000920404e06002420e06010404090802420480840004480810405000710404480802420090808404090802420e0c040004e0c008406000808404e0c002420e0c002405000002405000102420090840001000040001000040000c1c022021000422020e0608001ce06022022000622020e06040010e0601202100031202200054001e00021202100071202100074000d00030a02100020a020e0c080010e0c00a02200030a020e0c040008e0c0 (by decide +kernel)

def state233_41 : List Sig := [0xff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa,input 3,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_41 : Impossible true (goalAt 233) 5 state233_41.toFinset :=
  node_ok cuts233 [⟨state233_2,exclude233_2⟩] 0xe06028080a06028180e06022020e0600a02028081202200000a020616038180810118580212018580616008580090818580616010580c9c032300090832300484032300c8c038180888032300c8c022300c8c03a300280832300e06022020e06022020410112020410112020e0c03830021010a020c1c0307006160024206860 (by decide +kernel)

def state233_42 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_42 : Impossible true (goalAt 233) 5 state233_42.toFinset :=
  node_ok cuts233 [⟨state233_34,exclude233_34⟩] 0x38180a02028180a06018580e0602040461600848061601858021603070061601a182000018580210118580616010580e06022020e0600a02028081202041010a020e0c03830028084000068603818088081a18028201a18068600a18028081a180686012180c8c0381808101381802101120204101120202101 (by decide +kernel)

def state233_43 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_43 : Impossible true (goalAt 233) 6 state233_43.toFinset :=
  node_ok cuts233 [⟨state233_35,exclude233_35⟩,⟨state233_3,exclude233_3⟩,⟨state233_27,exclude233_27⟩,⟨state233_41,exclude233_41⟩,⟨state233_42,exclude233_42⟩] 0xe06012020e06028081000728080e06040014a0602808048082818088081a180686038180c8c032300880832300c8c03818068601a180480822200888010404c8c032300480832300c8c010404888022301000232300c8c00840468601a18200041a180686008404c8c032302000332300c8c04000068601a18200021a180686040000c8c032300e06008404e06022021000222020e06040014e0602202021012202100020840421011202100021202100024001e000112020210112021000140004e0c020404616018580e06040004e06020405000520404e06018580616010404212008480480818580616010404616018580480808480216002404616018580c8c040004c8c002406000002404c8c018580c8c008405000208405000118580616040005000110581000140008c1c03818100043818088084001488083818100053818088084001088081040500031040448084001c48081040500071040448084000c4808 (by decide +kernel)

def state233_44 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa,input 3,input 0,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_44 : Impossible true (goalAt 233) 5 state233_44.toFinset :=
  node_ok cuts233 [⟨state233_12,exclude233_12⟩] 0x480822022000012020a08038300e0c028300280838300e0c00a020818030700c1c020700c1c038300210130700090830700c1c010700c1c01a18009083070028201a18068600a18048403830068603830068603a18088081a180410112020410112020e0c00a020e0c00a020e06038180810122020c1c018580c1c002420c8c0 (by decide +kernel)

def state233_45 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_45 : Impossible true (goalAt 233) 5 state233_45.toFinset :=
  node_ok cuts233 [⟨state233_36,exclude233_36⟩] 0x12020880810404480810404480812020410128200e0c038300a0c00a020e0c038300280808404e0c038300210120600c1c03070081c030700e0c008404c1c018580c1c032302000030700810130700c1c010700e06038180880840000888032300c8c022300c8c038300280832300880832300c8c0123006860 (by decide +kernel)

def state233_46 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_46 : Impossible true (goalAt 233) 6 state233_46.toFinset :=
  node_ok cuts233 [⟨state233_37,exclude233_37⟩,⟨state233_32,exclude233_32⟩,⟨state233_13,exclude233_13⟩,⟨state233_44,exclude233_44⟩,⟨state233_45,exclude233_45⟩] 0x100041202048082040500042040500074001200022040448081202100071202048084000c41011040500071040441014000c480812021000728200a08012020e0c038301000538300e0c012020a0802830100040a020280820404e0c038301000538300e0c02040428080a02100050a020280840008e0c038301000538300e0c04000828080a020480822200888010404c8c032300480832300c8c010404888022300280832300c8c03830068603830028081a180686038300c8c03230100041a180686020404c8c032302000432300c8c02040468601a18200031a180686040000c8c032302000132300c8c04000068601a181000440004e06010404818020600480830700c1c010404c1c03070048082060081c008404c1c030700e0c040004e0c008405000508404e0c030700c1c002404c1c030700c8c040004c8c002406000002404c8c030700c1c020405000420405000130700c1c0400110004107010004400106160 (by decide +kernel)

def state233_47 : List Sig := [0x5555555555005500555555555500550055555555550055005555555555005500,input 0,input 3,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_47 : Impossible true (goalAt 233) 5 state233_47.toFinset :=
  node_ok cuts233 [⟨state233_4,exclude233_4⟩] 0xe06028080a06028180e06022020e0600a02028081202200000a02068603818088081a18028201a18068600a18028081a180686012180414030700c1c038180818030700c1c020700c1c038700210130700c1c032700090130700e06020404e06020404480810404480810404e0c038300280808404c8c0323006860024046160 (by decide +kernel)

def state233_48 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_48 : Impossible true (goalAt 233) 6 state233_48.toFinset :=
  node_ok cuts233 [⟨state233_6,exclude233_6⟩,⟨state233_27,exclude233_27⟩,⟨state233_38,exclude233_38⟩,⟨state233_42,exclude233_42⟩,⟨state233_47,exclude233_47⟩] 0xe06012020e06028081000828080e06040014a06028080480828180810118580616038180c1c030700810130700c1c038180616018580410120600818012020c1c030700410130700c1c012020818020701000230700c1c00a02061601858200031858061600a020c1c030701000030700c1c01a18009081a18200020242009081a180c1c030702000430700c1c040004616018582000118580616040004c1c030700e0600a020e06022021000222020e06040014e0602202028080a02100020a02028081202100021202100024002200001202028080a021000040000e0c02202068601a180e06040000e06022021000522020e0601a18068601202028200a08041011a18068601202068601a18041010a08028600a02100020a02100001a180686040001000012181000040008c8c03818100043818081014001481013818100053818081014001081011202100031202041014002041011202100081202041014000c4101 (by decide +kernel)

def state233_49 : List Sig := [0x5555555555555555555555555555555555005500550055005500550055005500,input 0,input 3,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_49 : Impossible true (goalAt 233) 5 state233_49.toFinset :=
  node_ok cuts233 [⟨state233_14,exclude233_14⟩] 0x480822022000012020a08038300e0c028300280838300e0c00a020888032300c8c022300c8c038300280832300880832300c8c012300212018580616008580414038300616038300616038580810118580616032300090132300480810404480810404e0c008404e0c008404e06038180880820404c8c01a180c8c002404c1c0 (by decide +kernel)

def state233_50 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_50 : Impossible true (goalAt 233) 6 state233_50.toFinset :=
  node_ok cuts233 [⟨state233_32,exclude233_32⟩,⟨state233_39,exclude233_39⟩,⟨state233_45,exclude233_45⟩,⟨state233_16,exclude233_16⟩,⟨state233_49,exclude233_49⟩] 0x100041202048082202100042202100084001200032202048081202100081040441014000c48081202100081202048084000c410110405000828200a08012020e0c038301000538300e0c012020a0802830100040a020280822020e0c038301000538300e0c02202028080a021000508404210140008e0c038301000538300e0c040008210108404410120600818012020c1c030700410130700c1c012020818020700210130700c1c038300616038300210118580616038300c1c030701000418580616022020c1c030702000230700c1c022020616018581000030700c1c032300090832302000102420090832300c1c030702000418580616040004c1c030702000030700c1c040004616018581000040000e06012020888022200410132300c8c012020c8c03230041012220088c00a020c8c032300e0c040000e0c00a02100050a020e0c032300c8c022021000422021000032300c8c0400010000123010000400106860 (by decide +kernel)

def state233_51 : List Sig := roots 233
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude233_51 : Impossible true (goalAt 233) 7 state233_51.toFinset :=
  node_ok cuts233 [⟨state233_9,exclude233_9⟩,⟨state233_19,exclude233_19⟩,⟨state233_40,exclude233_40⟩,⟨state233_43,exclude233_43⟩,⟨state233_46,exclude233_46⟩,⟨state233_48,exclude233_48⟩,⟨state233_50,exclude233_50⟩] 0x4000ce06012020e0604000ca0204000ca0204000ce06080004a0604000ca02012020a06040010e0600a020e06040008880838300e0c040014e06038300e0c04001088080a02028084000d000328200a0804000c480838300e0c04000e000038300e0c04000c480828200a0c04001088081a180686040000e06032300c8c080018880832300c8c040000e0601a18068604000c48082220088804000c410132300c8c04000c480832300c8c04000c41012220088c040008280832300c8c040000e0c01a180e0c08001428081a180686040000e0c032300c8c040010810118580616040004e06030700c1c080010810130700c1c040010e0601858061604000c41012060081804000c480830700c1c04000c410130700c1c04000c48082060081c040008210130700c1c040004e0c018580e0c08000c210118580616040004e0c030700c1c040000090130700c1c040004c8c002420c8c080008090102420090840000c8c030700c1c0 (by decide +kernel)

theorem lower233 : Claim 233 8 :=
  fromSearch 3 (by decide +kernel) exclude233_51

theorem lower249 : Claim 249 9 :=
  fromLift 9 16 3 lower233 (by decide +kernel)

def cuts145 : Cuts (goalAt 145) := []

def state145_0 : List Sig := roots 145
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude145_0 : Impossible true (goalAt 145) 3 state145_0.toFinset :=
  node_ok cuts145 [] 0x240401101240408101242009080240409080242008101044041101204041110044409010206008180204048180206009010044401110044048180206009080044409080044041110044409080206008180 (by decide +kernel)

theorem lower145 : Claim 145 4 :=
  fromSearch 4 (by decide +kernel) exclude145_0

theorem lower209 : Claim 209 5 :=
  fromLift 5 64 4 lower145 (by decide +kernel)

theorem lower177 : Claim 177 5 :=
  fromLift 5 16 4 lower161 (by decide +kernel)

def cuts81 : Cuts (goalAt 81) := []

def state81_0 : List Sig := roots 81
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x140401101140404101141005040140405040141004101044041101104041110044405010105004140104044140105005010044401110044044140105005040044405040044041110044405040105004140 (by decide +kernel)

theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

theorem lower113 : Claim 113 5 :=
  fromLift 5 32 4 lower81 (by decide +kernel)

def rule241_0 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower225 none (by decide +kernel)

def rule241_1 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower209 none (by decide +kernel)

def rule241_2 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower177 none (by decide +kernel)

def rule241_3 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower113 none (by decide +kernel)

def cuts241 : Cuts (goalAt 241) := [rule241_0,rule241_1,rule241_2,rule241_3]

def state241_0 : List Sig := roots 241
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_0 : Impossible true (goalAt 241) 6 state241_0.toFinset :=
  node_ok cuts241 [] 0x40008e0601c0c0e06040008b03040008b03040008e0604000ca06040008b0301c0c0a06040004e06008404e06040004901038300e0c040004e06038300e0c040004901008404903040004703028200a08040004501038300e0c040004703038300e0c040004501028200a0c040000b0301c180706040000e06034300d0c040000b03034300d0c040000e0601c180706040000703024200908040000410134300d0c040000703034300d0c04000041012420090c040001000034300d0c040000e0c01c180e0c04000100001c180706040000e0c034300d0c04000c81011858061604000ce06030700c1c04000c810130700c1c04000ce06018580616040008410120600818040008703030700c1c040008410130700c1c04000870302060081c040004210130700c1c040004e0c018580e0c040004210118580616040004e0c030700c1c040000110130700c1c040000d0c00c4c0d0c04000011010c4c0313040000d0c030700c1c0 (by decide +kernel)

theorem lower241 : Claim 241 7 :=
  fromSearch 4 (by decide +kernel) exclude241_0

theorem lower243 : Claim 243 8 :=
  fromLift 8 2 68 lower241 (by decide +kernel)

theorem lower184 : Claim 184 5 :=
  fromLift 5 16 808931328 lower168 (by decide +kernel)

def cuts178 : Cuts (goalAt 178) := []

def state178_0 : List Sig := roots 178
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude178_0 : Impossible true (goalAt 178) 3 state178_0.toFinset :=
  node_ok cuts178 [] 0x2c0c0a28228a0890302c0c0928224a08a03024a08a2820c88892820c8c0b03028088323028a08a08028208a08224a089080242089082 (by decide +kernel)

theorem lower178 : Claim 178 4 :=
  fromSearch 1081147456 (by decide +kernel) exclude178_0

def cuts154 : Cuts (goalAt 154) := []

def state154_0 : List Sig := roots 154
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude154_0 : Impossible true (goalAt 154) 3 state154_0.toFinset :=
  node_ok cuts154 [] 0x26060928224a088818260608a8222a08901822a089282048288a82068609818220281a1824a08908024208908222a088880222088882 (by decide +kernel)

theorem lower154 : Claim 154 4 :=
  fromSearch 805400640 (by decide +kernel) exclude154_0

def rule186_0 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower184 none (by decide +kernel)

def rule186_1 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower168 none (by decide +kernel)

def rule186_2 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower178 none (by decide +kernel)

def rule186_3 : {c : Cut // CutGood (goalAt 186) c} :=
  ruleFor 186 lower154 none (by decide +kernel)

def cuts186 : Cuts (goalAt 186) := [rule186_0,rule186_1,rule186_2,rule186_3]

def state186_0 : List Sig := [0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc,0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_0 : Impossible true (goalAt 186) 4 state186_0.toFinset :=
  node_ok cuts186 [] 0x28088a0822820828180c8c0a082282081a1822208a0820e0c088820e0c088822220838300e0c088822220832302c0c090820c888a0822420888820e0c088822420832222420890820c8890001 (by decide +kernel)

def state186_1 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_1 : Impossible true (goalAt 186) 5 state186_1.toFinset :=
  node_ok cuts186 [⟨state186_0,exclude186_0⟩] 0xa0220e060a02222028a08228208a02228208a0822202838180e06032300e060323006860a08228208323028208a0820686038180686038182420890822820832222820838180c88832222820890822420900010c88832222808890822420900012420890822808832220c88832308000032304000490822420832302420890824000500014000438182220888822820838302820838180e0c03830282088882222081a0a222088882242083830242081a0a0e0c0383024208888222208880a0e0c0383028088888222208880a2220888822808838300e0c01a180e0c038300c8c08882222081a182220888820c8c038300c8c1000040000b030 (by decide +kernel)

def state186_2 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_2 : Impossible true (goalAt 186) 5 state186_2.toFinset :=
  node_ok cuts186 [] 0xb03024a089282280c092820c888322224a0892820c888322224a0832302c0c0a0220c8c09282242009082242081a180c8c032300686032300e0c028220c8c012100c8c0323004840b03026060b0300e060a2820e0c0b0302606038300a88892820e0c092820e0603830400088a822c0c090102c0c09010 (by decide +kernel)

def state186_3 : List Sig := [0xffffffff00000000ffffffff00000000ff00ff0000000000ff00ff00,input 3,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_3 : Impossible true (goalAt 186) 4 state186_3.toFinset :=
  node_ok cuts186 [] 0x2c0c0928224a08a03024a0890802420890820c8c0b03028088323022a08888022208888222a0892820e0c08a820e0c08a8222a08383024a08322224a08a28228208a08228a08a080240c0a28228a08b03022a08383022a08a282 (by decide +kernel)

def state186_4 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_4 : Impossible true (goalAt 186) 5 state186_4.toFinset :=
  node_ok cuts186 [⟨state186_3,exclude186_3⟩] 0x381828a08a2820e062000028a08a2824000c928228a08322224a08322224a0892820c888322224a0892820c888a28228200a08228208928224200908224208323026060880a0c8c08a82222008882222083230068601a180c8c0b03022a08a2820e0608a8222a089282068288a82260608a82240603830 (by decide +kernel)

def state186_5 : List Sig := [0xccffccffccffccffccffccffccffccffcccccccccccccccccccccccccccccccc,input 3,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_5 : Impossible true (goalAt 186) 4 state186_5.toFinset :=
  node_ok cuts186 [] 0x28088a08228208381824208a0820c88890820c888908224208322222a08a0820e0c08a8222a0890820e0c08a820e0c08a8222a083830282083230282081a182420832302420900010c8c0b03028088323022a083830222088882 (by decide +kernel)

def state186_6 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000,input 3,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_6 : Impossible true (goalAt 186) 5 state186_6.toFinset :=
  node_ok cuts186 [⟨state186_5,exclude186_5⟩] 0x381828a08a2820e060928228a08322224a08322224a0892820c888a28228200a08228208928224200908224208323026060880a0c8c032300e0c028220c8c0381828a08383028a082a2224a08383024a08b83026060383028a08381828a08381824a08322224a0832224000032308000032302c0c08a82 (by decide +kernel)

def state186_7 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff00000000,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_7 : Impossible true (goalAt 186) 4 state186_7.toFinset :=
  node_ok cuts186 [] 0x2c0c0928224a08a03024a08a2820c888928224a0890802420890820c8c0b03028088323028a08a08028208a0822c0c0a28228a08903022a08383024a088a8222208888222a0888800e0c08a8222a08383022a08383028a088a82 (by decide +kernel)

def state186_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_8 : Impossible true (goalAt 186) 5 state186_8.toFinset :=
  node_ok cuts186 [⟨state186_7,exclude186_7⟩] 0xb03024a089282280c0928228a08322224a081a0a24a089282068288a8224a08383022a08383022a088a820e0c08a8228a08383022a0a000022a088a82400089282242009082242088a822220088822220832302c0c0a0220c8c0a28228200a082282081a180c8c032300686098182c0c0a282240c03818 (by decide +kernel)

def state186_9 : List Sig := [0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc,input 5,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_9 : Impossible true (goalAt 186) 4 state186_9.toFinset :=
  node_ok cuts186 [] 0x2c0c0908224208a03024208a2820c88890822220890820e0c088820e0c0888222208383022208a2820e0c088822c0c0a28228a0838182420832302420900012220838302220832300c8c0b03028088323028a08323028208a082 (by decide +kernel)

def state186_10 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_10 : Impossible true (goalAt 186) 5 state186_10.toFinset :=
  node_ok cuts186 [⟨state186_9,exclude186_9⟩] 0xb03024a089282280c092820c888322224a088a8224a08383022a08383022a088a820e0c08a820e0c0383022a089282242009082242088a822220088822220832302c0c0a0220c8c01a180c8c0323006860b8182c0c0381824a08322224a08322222a08383022a08383040000323080000323026060a282 (by decide +kernel)

def state186_11 : List Sig := roots 186
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude186_11 : Impossible true (goalAt 186) 6 state186_11.toFinset :=
  node_ok cuts186 [⟨state186_1,exclude186_1⟩,⟨state186_2,exclude186_2⟩,⟨state186_4,exclude186_4⟩,⟨state186_6,exclude186_6⟩,⟨state186_8,exclude186_8⟩,⟨state186_10,exclude186_10⟩] 0x80014b0300e060b0304000c981828a08a28280010b03028a08a2824000c98180e060903040004b0300c888b03040004a22224a08928240004b03024a08928240004a2220c888a03040004381824a08928240004a2820c888a2824000438180c888322240004a28224a0892828000c98180e0c0383040008b03022a088a8280008981822a088a8240008b0300e0c038304000c381822a088a8240008a2820e0c0a2828000438180e0c0383040008a28222a088a82400041a0a22a088a824000892820e0c09282400041a0a0e0c0383040008928222a088a8240000a2220c8c0323040000b03040000b03040000a22280000a02240000b0300c8c0323040000a28206860a28240000a0800c8c0a08040000a2820c8c0a08240000a08006860a0824000092824000492824000090800c8c090804000092820c8c09082400009080400009082400008a820c8c08a82400008880068608880400008a820686088824000088800c8c08882 (by decide +kernel)

theorem lower186 : Claim 186 7 :=
  fromSearch 808538176 (by decide +kernel) exclude186_11

theorem lower250 : Claim 250 8 :=
  fromLift 8 64 858869824 lower186 (by decide +kernel)

theorem lower153 : Claim 153 5 :=
  fromLift 5 8 3 lower145 (by decide +kernel)

theorem lower147 : Claim 147 5 :=
  fromLift 5 2 68 lower145 (by decide +kernel)

def cuts27 : Cuts (goalAt 27) := []

def state27_0 : List Sig := roots 27
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude27_0 : Impossible true (goalAt 27) 3 state27_0.toFinset :=
  node_ok cuts27 [] 0x6828130304828120a068281a18068601103048401a1806860121802c281918064600b0a044401918064601118064601a1802c281918 (by decide +kernel)

theorem lower27 : Claim 27 4 :=
  fromSearch 67 (by decide +kernel) exclude27_0

def rule155_0 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower153 none (by decide +kernel)

def rule155_1 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower147 none (by decide +kernel)

def rule155_2 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower154 none (by decide +kernel)

def rule155_3 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower137 none (by decide +kernel)

def rule155_4 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower27 none (by decide +kernel)

def rule155_5 : {c : Cut // CutGood (goalAt 155) c} :=
  ruleFor 155 lower145 none (by decide +kernel)

def cuts155 : Cuts (goalAt 155) := [rule155_0,rule155_1,rule155_2,rule155_3,rule155_4,rule155_5]

def state155_0 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_0 : Impossible true (goalAt 155) 4 state155_0.toFinset :=
  node_ok cuts155 [] 0x6828908224208128006860908224209000322208908204828888222028888222208090306860888222208121820e0890820440c838220e08888202c28838202c28838220e080b0a064609818 (by decide +kernel)

def state155_1 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_1 : Impossible true (goalAt 155) 4 state155_1.toFinset :=
  node_ok cuts155 [] 0x981824208908222060888224208120a22208981822208888224060838224208110320e088382222080b0a20e08991820e088382260601a0a242081a18242081210222081a1822208191820e080b0a20e08880a (by decide +kernel)

def state155_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_2 : Impossible true (goalAt 155) 5 state155_2.toFinset :=
  node_ok cuts155 [⟨state155_0,exclude155_0⟩,⟨state155_1,exclude155_1⟩] 0x981806828981822828928224a08981824a089282228281a0a2206098180240c9818240408a8222a08981822a088a82240400903240601a0a22a088a8224a09000524a081a0a4000c120a24a088a8222a08810302c280b0a26060838220e08810320e088382260600b0a26060110320e08838224a0900022460811034000c110324a08838220e08090320e08838222a080b0a22608090302c280b0a22a08838220e090000400008180228281a180686098188000498182282a0000220289818068601a1824a09000324a08908006860908024a081a182420890804000c908222a08121022a08888006860888022a081a18222088880048408882 (by decide +kernel)

def state155_3 : List Sig := [0x5555555555555555555555555555555544444444444444444444444444444444,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_3 : Impossible true (goalAt 155) 4 state155_3.toFinset :=
  node_ok cuts155 [] 0x1a0a24208908204a00888224208120a22208880a2220888820240c09082420819182420811102220819182220819182646081030646090820686090820440c8882068608882048601a1826060880a068608382 (by decide +kernel)

def state155_4 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_4 : Impossible true (goalAt 155) 5 state155_4.toFinset :=
  node_ok cuts155 [⟨state155_0,exclude155_0⟩,⟨state155_3,exclude155_3⟩] 0x10003068281a0a220289082242090003242089082220281a0a04a001a18044041a184000c9082242081a182420890824000c11010440c1a0a222088882242090005242081a0a4000c120a24208888222208880a02c0c880a2040c888222208880a2220888822040c0b0302c0c1a18024041a18048408882222081a1822208888204840090104860130320e08838224208191824208130306460191824208838220e080b0320e088382222081918222080b0306460191822208838220e08810306460191822028838220e08810320e08838222028191806462000106460191806860838220e0a000020e088382068601918064610000400009818 (by decide +kernel)

def state155_5 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa,input 0,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_5 : Impossible true (goalAt 155) 4 state155_5.toFinset :=
  node_ok cuts155 [] 0x26060928224a08881824a089080242089082068609818220281a1820e08928206460838220600838220e08818206460838220e08191822a08120a24a088a8222208888222a088880240608a8222a08981820e08191820e088a82 (by decide +kernel)

def state155_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_6 : Impossible true (goalAt 155) 5 state155_6.toFinset :=
  node_ok cuts155 [⟨state155_0,exclude155_0⟩,⟨state155_5,exclude155_5⟩] 0x1a0a24a089282068281a0a24a089282068288a8224a08120a22a080b0322a088a8202c0e000122a088a82400049282242009082242088a82222008882222081a18204048103068601a1840002000006860981820e08928204c0c838220e088a8202c0c838220600838220e08818220c0c8382400081918 (by decide +kernel)

def state155_7 : List Sig := roots 155
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude155_7 : Impossible true (goalAt 155) 6 state155_7.toFinset :=
  node_ok cuts155 [⟨state155_2,exclude155_2⟩,⟨state155_4,exclude155_4⟩,⟨state155_6,exclude155_6⟩] 0x4000c98180682898184000c8a0a24a0892824000c981824a0892824000c8a0a06828881840004981802c0c981840004901022a088a8240004981822a088a8240004901002c0c9018400041a0a22a088a82400049282400049282400041a0a4000c120a40004928222a088a82400008a0a068601a18400009818400009818400008a0a80004880a400009818068601a184000092824000c9282400009080068609080400009282068609082400009080400009082400008a82048408a82400008880068608880400008a8206860888240000888004840888240010830306460191840008981820e08838280008830320e0883824000898180646019184000c130320e0883824000892820646092824000c130306460191840008928220e088382400040b0320e088382400048a82064608a82400040b03064601918400048a8220e088382400010000206008180400001a1820e08838240002000020e088382400001a18206008182 (by decide +kernel)

theorem lower155 : Claim 155 7 :=
  fromSearch 67 (by decide +kernel) exclude155_7

theorem lower219 : Claim 219 8 :=
  fromLift 8 64 67 lower155 (by decide +kernel)

theorem lower57 : Claim 57 5 :=
  fromLift 5 16 3 lower41 (by decide +kernel)

def rule185_0 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower177 none (by decide +kernel)

def rule185_1 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower184 none (by decide +kernel)

def rule185_2 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower169 none (by decide +kernel)

def rule185_3 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower153 none (by decide +kernel)

def rule185_4 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower57 none (by decide +kernel)

def rule185_5 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower145 none (by decide +kernel)

def rule185_6 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower137 none (by decide +kernel)

def rule185_7 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower41 none (by decide +kernel)

def rule185_8 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower161 none (by decide +kernel)

def rule185_9 : {c : Cut // CutGood (goalAt 185) c} :=
  ruleFor 185 lower168 none (by decide +kernel)

def cuts185 : Cuts (goalAt 185) := [rule185_0,rule185_1,rule185_2,rule185_3,rule185_4,rule185_5,rule185_6,rule185_7,rule185_8,rule185_9]

def state185_0 : List Sig := [0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 7,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_0 : Impossible true (goalAt 185) 4 state185_0.toFinset :=
  node_ok cuts185 [] 0xa060a0802820028180e0c0a08028201000622200a0800a06088802206088802220009010e0c088802220100022a0c08180282002101206008180222001918206001918206008180064603130 (by decide +kernel)

def state185_1 : List Sig := [0x5555555555555555555555555555555555005500550055005500550055005500,input 0,input 7,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_1 : Impossible true (goalAt 185) 4 state185_1.toFinset :=
  node_ok cuts185 [] 0x281828200a0800a06088802820028182220088182220088800240411102820031302820021202220031302220031302a4c081010c4c0a0800e0c0a0800840488800e0c088800240438302a0c088180e0c08180 (by decide +kernel)

def state185_2 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_2 : Impossible true (goalAt 185) 4 state185_2.toFinset :=
  node_ok cuts185 [] 0x383028200a08008404281828200a0800a06088802820028182220038302220088800440488182220088804002081802820021012060081802220011012060081012060081800e0c031302a0c03830220603830 (by decide +kernel)

def state185_3 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 0,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_3 : Impossible true (goalAt 185) 5 state185_3.toFinset :=
  node_ok cuts185 [⟨state185_0,exclude185_0⟩,⟨state185_1,exclude185_1⟩,⟨state185_2,exclude185_2⟩] 0x100070a060281822060a08028201000528200a0802206028180a060383008404383040018a08028200383028200a0804001821010840421012060081802820031302820021010c4c031302820081802060011012060081802220031302220011010c4c031302220081802060100070c4c031302206081802060200022060081802206031300c4c200010c4c031300e0c081802060200002060081800e0c031300c4c028182220088802820100052820028184001428182820088802220088180440488184002088802220088182220088804001c110104404383004404383040008888022200383022200888040008110104405000040000a830 (by decide +kernel)

def state185_4 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_4 : Impossible true (goalAt 185) 4 state185_4.toFinset :=
  node_ok cuts185 [] 0xa83028200a080220c0888028200281822200a830222008880280c0818028200210120600818022200191820600a9302060081802a0c02818282003830282002820222003830222003130206001918206008818 (by decide +kernel)

def state185_5 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_5 : Impossible true (goalAt 185) 4 state185_5.toFinset :=
  node_ok cuts185 [] 0x281828200a0800a060281828200a0800646090802820028182420009012420090800240419182420090804002081802820038302060081802220038302060038302060081800e0c031302060081800e0c0b030 (by decide +kernel)

def state185_6 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_6 : Impossible true (goalAt 185) 5 state185_6.toFinset :=
  node_ok cuts185 [⟨state185_0,exclude185_0⟩,⟨state185_4,exclude185_4⟩,⟨state185_5,exclude185_5⟩] 0xb0300a060b03022060a08028200b03028200a080220602818240c0b03002404b03028080908024200b030242009080280800901280c028182420090802820100052820028184001428182820090802420081010646019182c0c100092c0c081018000881012c0c019182c0c021010646019182820100052820021014001421012820019182820009014002009012420019182420009010646019182420100082420100004000081802206038300e0c0b03080004a83022062000022060b0300e0c038300a06100060a060a0800e0c0a0800a06038300e0c0a08040018a0800240500022220090800e0c088800240438300e0c09080400089080 (by decide +kernel)

def state185_7 : List Sig := [0xff000000ff000000ff000000ff000000aa000000aa000000aa000000aa,input 0,input 7,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_7 : Impossible true (goalAt 185) 4 state185_7.toFinset :=
  node_ok cuts185 [] 0xb03028200a080240c028182820038302820038302a0c088180e0c081802820031302060081800e0c019182060031302060081800c4c090800a060a080242008880280c0908024200b030206003130206009080 (by decide +kernel)

def state185_8 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_8 : Impossible true (goalAt 185) 5 state185_8.toFinset :=
  node_ok cuts185 [⟨state185_5,exclude185_5⟩,⟨state185_0,exclude185_0⟩,⟨state185_2,exclude185_2⟩,⟨state185_7,exclude185_7⟩] 0xa060a0802820028180a060a0802820028180a060a0800e0c0a0802220038302040600020e0c038304000200010e0c0908028200281824200110124200908004406000324200908040020b03020600a0800840481802060038308000081802060090800440481802040481804001c3130 (by decide +kernel)

def state185_9 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_9 : Impossible true (goalAt 185) 6 state185_9.toFinset :=
  node_ok cuts185 [⟨state185_3,exclude185_3⟩,⟨state185_6,exclude185_6⟩,⟨state185_8,exclude185_8⟩] 0x4001cb0300a060b03040018881828200a08040014b03028200a0804001888180a06090304001c81010c4c0313040024b0302060081808000881012060081804001cb0300c4c0313040018210120600818040014a0800c4c0a0804001421010c4c0313040018a0802060081804000100002060081804000038300646038304000200010646019184000038302060081804002011012060081804002090800c4c090804002011010c4c031304002090802060081804000088180e0c0383040000b03040000a83040000881880000881840000b0300e0c0383040000281840018281840000a0800e0c0a0804000028180e0c0383040000a08040000a0804000900024000888804001cb03004404b03040020a02024200908040020b0302420090804001ca02004404a03040018281824200908040014a08040014a08040014281840014281840018a080242009080 (by decide +kernel)

def state185_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_10 : Impossible true (goalAt 185) 4 state185_10.toFinset :=
  node_ok cuts185 [] 0x2220090800e0c088800e0c088802220038300a0608880222010005240c090802420011010a06090802420100022606081802220009012060081802420031302060031302060081800c4c01918 (by decide +kernel)

def state185_11 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_11 : Impossible true (goalAt 185) 4 state185_11.toFinset :=
  node_ok cuts185 [] 0x88802420038302220038302220088800e0c09030242009080044041110222001918222000908242001918242001918240c08101240c088800a06088800240490800a06090800440490302606090300a0608180 (by decide +kernel)

def state185_12 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_12 : Impossible true (goalAt 185) 4 state185_12.toFinset :=
  node_ok cuts185 [] 0x88802420038302220028182220088800240438302220088800e0c028182420090800440490302420090804001881802220009012060081802420011012060081012060081800a0603130260609030240c02818 (by decide +kernel)

def state185_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_13 : Impossible true (goalAt 185) 5 state185_13.toFinset :=
  node_ok cuts185 [⟨state185_10,exclude185_10⟩,⟨state185_11,exclude185_11⟩,⟨state185_12,exclude185_12⟩] 0x100062220088802420038302420100050e0c038302420088802220100070e0c03830240c08880222010005222008880240c038300e0c028180240428184001488802220028182220088804001409010240409012060081802220019182220009010646019182220081802060011012060081802420031302420011010c4c031302420081802060100070c4c03130240c08180206020002206008180240c031300c4c200010646019180a06081802060200002060081800a06019180646090300440490304001890802420090302420090804001811010440428180440428184000890802420028182420090804000811010440500034000c9818 (by decide +kernel)

def state185_14 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_14 : Impossible true (goalAt 185) 4 state185_14.toFinset :=
  node_ok cuts185 [] 0x88802420038302220038302220088800e0c098182420090802206081802220009012060081802420031302060031302060081800c4c03830222003830222002808242002818242003130206003130206009030 (by decide +kernel)

def state185_15 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_15 : Impossible true (goalAt 185) 4 state185_15.toFinset :=
  node_ok cuts185 [] 0x88802420038302220088802060038302060038302220088800e0c038302220088800c4c011012420090800440431302420090804001881802420028182060028182060081800a06031302060081800a0609130 (by decide +kernel)

def state185_16 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_16 : Impossible true (goalAt 185) 5 state185_16.toFinset :=
  node_ok cuts185 [⟨state185_10,exclude185_10⟩,⟨state185_14,exclude185_14⟩,⟨state185_15,exclude185_15⟩] 0x98180e0c03830280c08880222009818222008880280c038300e0c100062220088802420038302420100050e0c038302420088802220028182220088804001438300e0c028180e0c0383040014888022200a03004404a03022020908024200a0302420090802202011012206081010c4c03130280c10009244c08101800088101280c031300c4c009010c4c031302220100052220009014001409012220031302220011014001811012420031302420011010c4c031302420100062420100034000c8180280c02818280c09818800049818280c20000240c098180a06090300440500022820090800a06090800440428180a0609080400089080 (by decide +kernel)

def state185_17 : List Sig := [0xffff000000000000ffff000000000000aaaa000000000000aaaa,input 0,input 7,input 5,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_17 : Impossible true (goalAt 185) 4 state185_17.toFinset :=
  node_ok cuts185 [] 0x88800e0c038302220038302220088800e0c0a030260609030240c081802220019182060081800c4c031302060031302060081800c4c088800e0c0888024200a08022060908024200a030206003130206009080 (by decide +kernel)

def state185_18 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_18 : Impossible true (goalAt 185) 5 state185_18.toFinset :=
  node_ok cuts185 [⟨state185_15,exclude185_15⟩,⟨state185_10,exclude185_10⟩,⟨state185_12,exclude185_12⟩,⟨state185_17,exclude185_17⟩] 0x2220038300e0c088802220090800e0c088800e0c088802220038300e0c088802220038302820028182040600020a06028184000e00010a060110124200908004406000324200908040018a0302060088800240481802060028188000081802060090800440481802040481804001c3130 (by decide +kernel)

def state185_19 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 3,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_19 : Impossible true (goalAt 185) 6 state185_19.toFinset :=
  node_ok cuts185 [⟨state185_13,exclude185_13⟩,⟨state185_16,exclude185_16⟩,⟨state185_18,exclude185_18⟩] 0x4001c98180e0c0383040014a0302220088804001498182220088804001ca0300e0c038304000c28182220088804000d00050e0c038304000c28180e0c038304000d00032220088804001900062220088804001890800e0c090804001900050e0c038304001890802220088804001c81010c4c0313040024a0302060081808000881012060081804001ca0300c4c031304001409012060081804001488800646088804001409010646019184001488802060081804000d00032060081804000c28180c4c031304000e00010c4c031304000c28182060081804001811012060081804001890800c4c090804001811010c4c031304001890802060081804000ca0300a060a0304000c98184000c98184000ca0308000090304000c98180a060903040009000240008a08040018a03004404a03040018880824200908040018a030242009080400188808044048818 (by decide +kernel)

def state185_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffaa0000ffaa0000ffaa0000ffaa,input 7,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_20 : Impossible true (goalAt 185) 4 state185_20.toFinset :=
  node_ok cuts185 [] 0x2c0c0a08028200903022200a0800e0c088800e0c0888022200383020600a0800c4c081802060088800646081800c4c08180206003130242002818282009080222003830222009080206003130206009080280c0908024200b030 (by decide +kernel)

def state185_21 : List Sig := [0xffffffff00000000ffffffff00000000ffaaffaa00000000ffaaffaa,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_21 : Impossible true (goalAt 185) 4 state185_21.toFinset :=
  node_ok cuts185 [] 0x2c0c0908024200a0302220090800e0c088800e0c088802220038302060090800c4c081802060088800646081800c4c0818020600313024200281824200a08022200383022200a08020600313020600a080240c0a08028200b030 (by decide +kernel)

def state185_22 : List Sig := [0xffffffffffffffffffffffffffffffffffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_22 : Impossible true (goalAt 185) 5 state185_22.toFinset :=
  node_ok cuts185 [⟨state185_0,exclude185_0⟩,⟨state185_20,exclude185_20⟩,⟨state185_21,exclude185_21⟩] 0x381828200a0800e062000228200a0804000c908028200281824200981824200908022062000124200908040008888028200381822200888024202000022200981822200888024060383020600a0800840481802060090800646081802060088800646081800646081802060019180c4c0b030 (by decide +kernel)

def state185_23 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaa,input 7,input 0,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_23 : Impossible true (goalAt 185) 5 state185_23.toFinset :=
  node_ok cuts185 [⟨state185_4,exclude185_4⟩] 0xb03028200a080240c0908028200281824200b030242009080280c0888028200381822200888024202000022200b8302220088802c0c0818028200210120600818024200191820600818022200191820600b1302060081802c0c03818282003818282001101242001101242003830222000901222003130206001918206009818 (by decide +kernel)

def state185_24 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_24 : Impossible true (goalAt 185) 4 state185_24.toFinset :=
  node_ok cuts185 [] 0xe060a08028200191808404a08028200090124200a0800a060908006460908024200811804404908024200090120600a0800e06081802060090800440481800c4c081802060090180e0c081802060100042c0c0b030064601118 (by decide +kernel)

def state185_25 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_25 : Impossible true (goalAt 185) 5 state185_25.toFinset :=
  node_ok cuts185 [⟨state185_5,exclude185_5⟩,⟨state185_24,exclude185_24⟩] 0xe060a0802820038180e060a08028200191824200a0800a06090800440490802420011010646090802420009180e060a0800e060a08002404908080000908022200090120406000102404191802404191804460818028200381820600818024200110120600810120600818040010313020600818040000b030 (by decide +kernel)

def state185_26 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 7,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_26 : Impossible true (goalAt 185) 5 state185_26.toFinset :=
  node_ok cuts185 [⟨state185_24,exclude185_24⟩] 0xe060a08028200381808404a08028200090124200a0800a060908026060908024200881804404908024200090106460a08008404a08002420908006460908020600191824462000006460090106460191804460888028200381822200888024200110122200981822200888024060383022200888040010b030 (by decide +kernel)

def state185_27 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_27 : Impossible true (goalAt 185) 6 state185_27.toFinset :=
  node_ok cuts185 [⟨state185_6,exclude185_6⟩,⟨state185_22,exclude185_22⟩,⟨state185_23,exclude185_23⟩,⟨state185_25,exclude185_25⟩,⟨state185_26,exclude185_26⟩] 0xb0300e060b03026060a08028200b03028200a080260603818240c0b03004404b03028080908024200b030242009080280801101280c038182420090802820100052820038184001428182820090802420098180240498182c0c100002c0c098188001098182c0c009012c0c0381802404381828201000028200381840014381828200090128201000002404090124201000024201000040022000024200090124201000040004888020404191806460b03040004b03020406000320404b03006460b03008404191806460a08040004a08008405000508404a08006460a08004404090802420908006460908004404191806460908002420908002405000002405000106460191840001000004461000040000818026061000426060b03080008b03026062000126060b03040010b0300e06100030e060a08040014a0800e06100050e060a0804000ca080044050002044049080400209080044050008044049080400089080 (by decide +kernel)

def state185_28 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00ff00ff00aa00aa,input 7,input 0,input 5,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_28 : Impossible true (goalAt 185) 4 state185_28.toFinset :=
  node_ok cuts185 [] 0x24200a0800a06090802c0c0908024200a0302c0c0a0802820090302060090800c4c0818020600a0800c4c081800c4c081802060031302220038302420088802220038302820088802060019182060088800e0c08880222003830 (by decide +kernel)

def state185_29 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000aaaa0000ffff0000aaaa,input 7,input 0,input 5,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_29 : Impossible true (goalAt 185) 4 state185_29.toFinset :=
  node_ok cuts185 [] 0x22200a0800e0c088800e0c088802220038302c0c0a08028200903020600888006460818020600a0800c4c081800c4c08180206003130222003830222009080242002818282009080206003130206009080280c0908024200b030 (by decide +kernel)

def state185_30 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_30 : Impossible true (goalAt 185) 5 state185_30.toFinset :=
  node_ok cuts185 [⟨state185_10,exclude185_10⟩,⟨state185_28,exclude185_28⟩,⟨state185_29,exclude185_29⟩] 0x908028202000024200b030242009080280c200022420090804000888802420038302220088802820038302220038302220088800e0c2000122200888040000b03028200a080240c038182060090800c4c0818020600888002404818020600a0800c4c081800c4c08180206003130064609818 (by decide +kernel)

def state185_31 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_31 : Impossible true (goalAt 185) 5 state185_31.toFinset :=
  node_ok cuts185 [⟨state185_14,exclude185_14⟩] 0x90802820200002420098182420090802206088802420038302220088802820038302220038302220088800e0c0b81828200a0802606081802420031302060081802220009012060081802820031302060031302060081800c4c0110124200110124200383022200383022200381828200210128200313020600313020600b030 (by decide +kernel)

def state185_32 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_32 : Impossible true (goalAt 185) 4 state185_32.toFinset :=
  node_ok cuts185 [] 0x2420081800440481800c4c090802420081300440490802420011012220090800e0c088802220081800e0c081800e0c088802220031300240488802220009010c4c081802060090300e06081802060100042606031300c4c01130 (by decide +kernel)

def state185_33 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_33 : Impossible true (goalAt 185) 5 state185_33.toFinset :=
  node_ok cuts185 [⟨state185_15,exclude185_15⟩,⟨state185_32,exclude185_32⟩] 0x2420021018000090802420081800440481800440490802420011010c4c090802420021302220090800e0c088802220038300e0c088802220081800e0c081800e0c088802220038300e0c08880222003130282002101204060001084043130084043130044c0810120600818040010313020600818040010b030 (by decide +kernel)

def state185_34 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_34 : Impossible true (goalAt 185) 5 state185_34.toFinset :=
  node_ok cuts185 [⟨state185_32,exclude185_32⟩] 0x24200a0800440490802c0c0908024200a0300440490802420011012220090800e0c0888022200a0800e0c088800e0c088802220038300240488802220009010848090800c4c090800c4c08880024048880206003130244c200000c4c021010c4c03130044c0b03028200a080240c0381828200a080400109818 (by decide +kernel)

def state185_35 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 3,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_35 : Impossible true (goalAt 185) 6 state185_35.toFinset :=
  node_ok cuts185 [⟨state185_16,exclude185_16⟩,⟨state185_30,exclude185_30⟩,⟨state185_31,exclude185_31⟩,⟨state185_33,exclude185_33⟩,⟨state185_34,exclude185_34⟩] 0xb03004404b03028080908024200b030242009080280801101280c100032420090800840500030840500064000e00000840490802420100062420090804000811010440500060440411014000890802420098180e0c038302c0c088802220098182220088802c0c038300e0c100062220088802420038302420100050e0c038302420088802220100032220088800840438300e0c100050e0c038300840488802220100052220088804000038300e0c100050e0c0383040000888022200b03008404b03026061000326060b03080010b03026060210126061000140004a0802040431300c4c0b03040004b03020406000320404b0300c4c031300440421200848090800c4c090800440431300c4c090800848090800240431300c4c088804000488800240500050240488800c4c088800840500030840500010c4c03130400050001044c100014000c81802c0c100042c0c098188000898182c0c200012c0c09818400109818 (by decide +kernel)

def state185_36 : List Sig := [0xff00ffff00000000ff00ffff00000000ff00ffaa00000000ff00ffaa,input 3,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_36 : Impossible true (goalAt 185) 3 state185_36.toFinset :=
  node_ok cuts185 [] 0xc4c081802060031302060088800646081800e0c088802220038300a0609080242009030206003130206009080222003830222009080 (by decide +kernel)

def state185_37 : List Sig := [0xff00ffffff00ffffff00ffffff00ffffff00ffaaff00ffaaff00ffaaff00ffaa,input 3,input 0,input 7,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_37 : Impossible true (goalAt 185) 4 state185_37.toFinset :=
  node_ok cuts185 [⟨state185_36,exclude185_36⟩] 0xb03028200a080240c081802820031302060031302060081800c4c081802220019182060031302060081802420088802820028182220088182220088802c0c03830242020000282009080280c0908024200b030 (by decide +kernel)

def state185_38 : List Sig := [0xff00ff000000ff00ff00ff000000ff00ff00ff000000aa00ff00ff000000aa,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_38 : Impossible true (goalAt 185) 3 state185_38.toFinset :=
  node_ok cuts185 [] 0xc4c0818020600313020600a0800c4c08180280c0a0802820028180e0c08880222003830206001918206008880222003830282008880 (by decide +kernel)

def state185_39 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff0000aaaaffffffff0000aaaa,input 5,input 0,input 7,input 3]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_39 : Impossible true (goalAt 185) 4 state185_39.toFinset :=
  node_ok cuts185 [⟨state185_38,exclude185_38⟩] 0x38302220088800e0c088802820038302220200002220088802420081802220019182060031302060081800c4c0818028200313020600191820600818024200a03028200a080260602818280c09080242009818 (by decide +kernel)

def state185_40 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 7,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_40 : Impossible true (goalAt 185) 5 state185_40.toFinset :=
  node_ok cuts185 [⟨state185_7,exclude185_7⟩,⟨state185_17,exclude185_17⟩,⟨state185_37,exclude185_37⟩,⟨state185_39,exclude185_39⟩] 0x2c0c028182c0c0981828200a0802c0c0a0802820098180a06090300a060888022200a0800e0c0a0800a06038300e0c0a0802220088802606038300e0c0b03022200888026060888022200b0300e0c0383008404818020600a0800c4c0a0800840431300c4c0a0802060081800240481802060088800646088800240419180646088802060081802040431300c4c0b03020600818020404818020600b0300c4c03130282009080242002818800042818282020003282002818242009080222009080222003830800003830222020002222003830242009080204041101280c0b03024200908020404908024200b03004404b030206009080206003130044043130206001101206003130242009080 (by decide +kernel)

def state185_41 : List Sig := [0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa,input 3,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_41 : Impossible true (goalAt 185) 5 state185_41.toFinset :=
  node_ok cuts185 [⟨state185_7,exclude185_7⟩] 0x381828200a0800e06090802820028182420098182420090802206081802820021012060081802420019182060019182060081800646081800e0c019182060038182820038302820028202420038302420038302e0c098180e0c0a0800e060a0800e060908080000908040008b0302c0c081012606081800c4c08180064608880 (by decide +kernel)

def state185_42 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_42 : Impossible true (goalAt 185) 5 state185_42.toFinset :=
  node_ok cuts185 [⟨state185_2,exclude185_2⟩,⟨state185_24,exclude185_24⟩] 0xe060a08028200381808404a08028200210124200a0800a060908026060908024200881804404908024200110120600a0800840481802060090800440481800c4c0818022202000120600810120600818040004b0302c0c09818400008880282003818222008880242020000222009818222008880240603830 (by decide +kernel)

def state185_43 : List Sig := [0xffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_43 : Impossible true (goalAt 185) 5 state185_43.toFinset :=
  node_ok cuts185 [] 0xa060a0802820028180a060a08028200281822200a0800e0c088800e0c088802220038300e0c088802220038302c0c081802820021012060081802220009012060081012060100070c4c090800a060a0802420088800e0c08880242001101242009080044048180044048180242010002 (by decide +kernel)

def state185_44 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 0,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_44 : Impossible true (goalAt 185) 5 state185_44.toFinset :=
  node_ok cuts185 [⟨state185_17,exclude185_17⟩] 0xb030242009080280c090800a02028182420088802420038302220038302220088800e0c088800e0c038302220081802420031302060081802220009012060031302060081800c4c081800c4c0313020600b0302e060b0300e06090808000090804000888800e0c088800e0c098182c0c081012c0c081800c4c081800c4c0a080 (by decide +kernel)

def state185_45 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_45 : Impossible true (goalAt 185) 5 state185_45.toFinset :=
  node_ok cuts185 [⟨state185_32,exclude185_32⟩,⟨state185_12,exclude185_12⟩] 0x2c0c0908024200a03024200a0808000490800440490802420011012220090800e0c088800e0c0888022200383022200a0800e0c088800240488802220009012060090800440481802060088800240481800c4c081802820200002060081012060081804000498182c0c0b03040004b03028200a080240c03818 (by decide +kernel)

def state185_46 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_46 : Impossible true (goalAt 185) 6 state185_46.toFinset :=
  node_ok cuts185 [⟨state185_25,exclude185_25⟩,⟨state185_33,exclude185_33⟩,⟨state185_22,exclude185_22⟩,⟨state185_8,exclude185_8⟩,⟨state185_18,exclude185_18⟩,⟨state185_30,exclude185_30⟩,⟨state185_40,exclude185_40⟩,⟨state185_41,exclude185_41⟩,⟨state185_42,exclude185_42⟩,⟨state185_43,exclude185_43⟩,⟨state185_44,exclude185_44⟩,⟨state185_45,exclude185_45⟩] 0x100040e060381820404a08028202000b28200a0802040438180e062000a0e06038184000ca08028202000528200a0804000c38180e06038182420090802820100072820038188001028182820090802420100040440411012040490802420100072420090802040411010440500078002600064000890802420100072420090804000900074000838182220088802820038302820038180e0c038302820088802220100072220088802420038302420200030e0c038302420088802220100040e0c038302040488802220200082220088802040438300e0c200070e0c038304000088802220200022220088804000038300e0c1000440004b03008404818020600a08040004a08008406000108404a080206008180044048180206009080400049080044050007044049080206008180024048180206008880400048880024060000024048880206008180204050004204050001206008180400110004400110004400103130 (by decide +kernel)

def state185_47 : List Sig := [0x5555555555555555555555555555555555005500550055005500550055005500,input 0,input 3,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_47 : Impossible true (goalAt 185) 5 state185_47.toFinset :=
  node_ok cuts185 [⟨state185_1,exclude185_1⟩] 0x381828200a0800e06090802820028182420098182420090802206088802820038182220088802420200002220098182220088802406011102820031302820021202420031302420031302c4c081010c4c0313022200090122200a08008404a08008404908004404908004404b0302c0c098182040488800e0c08880024048180 (by decide +kernel)

def state185_48 : List Sig := [0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,input 3,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_48 : Impossible true (goalAt 185) 6 state185_48.toFinset :=
  node_ok cuts185 [⟨state185_3,exclude185_3⟩,⟨state185_22,exclude185_22⟩,⟨state185_26,exclude185_26⟩,⟨state185_42,exclude185_42⟩,⟨state185_47,exclude185_47⟩] 0x100040e060381826060a08028201000528200a0802606038180e06100050840421014000ca08028201000528200a0804000c21010840438182420090802820100072820038184001428182820090802420098180440498182202090802420098182420090802202011012206100070440411014000890802420100072420090804000811010440421012060081802820031302820021010c4c031302820081802060011012060081802420031302420011010c4c031302420081802060100040c4c031302606081802060200032060081802606031300c4c100002060081802220019182220200020646019182220081802060200040c4c031304000481802060200012060081804000431300c4c1000040000b0300e060888022200a08040000a0800e06100050e060a080222008880400008880222009080400009080400010007800009080222008880260610004260610000222008880400010000240610000400103830 (by decide +kernel)

def state185_49 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 5,input 7,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_49 : Impossible true (goalAt 185) 5 state185_49.toFinset :=
  node_ok cuts185 [⟨state185_11,exclude185_11⟩] 0xb030242009080280c090802820200002420088802420038302220038302220088800e0c0888028200383022200b03028200a080240c009082420019182420011102220019182220019182c0c081012c0c0191828200210128200908004404908004404888002404888002404b03026060b03020404a0800e060a080084048180 (by decide +kernel)

def state185_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_50 : Impossible true (goalAt 185) 6 state185_50.toFinset :=
  node_ok cuts185 [⟨state185_30,exclude185_30⟩,⟨state185_34,exclude185_34⟩,⟨state185_45,exclude185_45⟩,⟨state185_13,exclude185_13⟩,⟨state185_49,exclude185_49⟩] 0xb03004404b03028080908024200b030242009080280801101280c100032420090802820100032820100064000e00032820090802420100060440411014000890802420100062420090804000811010440500062220088802420038302420100050e0c038302420088802220100040e0c038302c0c088802220100052220088802c0c038300e0c100032220088802820038302820100050e0c038302820088802220100050240409014000088802220100052220088804000009010240411012060081802420031302420011010c4c031302420081802060009012060081802220019182220009010646019182220081802060100040c4c031302c0c081802060200022060081802c0c031300c4c100032060081802820031302820200010c4c031302820081802060200040646019184000481802060200002060081804000419180646100044000c98182c0c100042c0c1000328200a080400110004240c10004400103818 (by decide +kernel)

def state185_51 : List Sig := roots 185
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude185_51 : Impossible true (goalAt 185) 7 state185_51.toFinset :=
  node_ok cuts185 [⟨state185_9,exclude185_9⟩,⟨state185_19,exclude185_19⟩,⟨state185_27,exclude185_27⟩,⟨state185_35,exclude185_35⟩,⟨state185_46,exclude185_46⟩,⟨state185_48,exclude185_48⟩,⟨state185_50,exclude185_50⟩] 0x40010b0300e060b0304000c981828200a08080018b03028200a0804001098180e060903040008b03004404b03040008a02024200908040008b03024200908040008a02004404a03040008381824200908040008a08040008a08040008381880004281840008a0802420090804001098180e0c0383040000b03022200888080014981822200888040000b0300e0c038304000c381822200888040000a0800e0c0a0804001438180e0c0383040000a0802220088804000900022220088804000890800e0c090804000a00000e0c038304000890802220088804001081010c4c0313040004b03020600818080010810120600818040010b0300c4c031304000c210120600818040004a0800c4c0a0808000c21010c4c0313040004a0802060081804000811012060081804000890800c4c090804000811010c4c03130400089080206008180400000901206008180400048880064608880800080901064601918400008880206008180 (by decide +kernel)

theorem lower185 : Claim 185 8 :=
  fromSearch 3 (by decide +kernel) exclude185_51

theorem lower187 : Claim 187 9 :=
  fromLift 9 2 67 lower185 (by decide +kernel)

theorem lower89 : Claim 89 5 :=
  fromLift 5 8 3 lower81 (by decide +kernel)

def rule121_0 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower113 none (by decide +kernel)

def rule121_1 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower105 none (by decide +kernel)

def rule121_2 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower89 none (by decide +kernel)

def rule121_3 : {c : Cut // CutGood (goalAt 121) c} :=
  ruleFor 121 lower57 none (by decide +kernel)

def cuts121 : Cuts (goalAt 121) := [rule121_0,rule121_1,rule121_2,rule121_3]

def state121_0 : List Sig := roots 121
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude121_0 : Impossible true (goalAt 121) 6 state121_0.toFinset :=
  node_ok cuts121 [] 0x4000870300e06070304000858184000858184000870304000c50304000858180e06050304000470300440470304000448081c18070604000470301c18070604000448080440448184000438181410050404000428081c18070604000438181c18070604000428081410050604000058180e0c038304000070301a18068604000058181a18068604000070300e0c038304000038181210048404000021011a18068604000038181a18068604000021011210048604000100001a18068604000070600e0c070604000100000e0c038304000070601a18068604000c41010c4c031304000c70301858061604000c41011858061604000c70300c4c031304000821011050041404000838181858061604000821011858061604000838181050041604000411011858061604000470600c4c070604000411010c4c03130400047060185806160400000901185806160400006860064606860400000901064601918400006860185806160 (by decide +kernel)

theorem lower121 : Claim 121 7 :=
  fromSearch 3 (by decide +kernel) exclude121_0

theorem lower115 : Claim 115 6 :=
  fromLift 6 2 68 lower113 (by decide +kernel)

theorem lower83 : Claim 83 5 :=
  fromLift 5 2 68 lower81 (by decide +kernel)

def cuts90 : Cuts (goalAt 90) := []

def state90_0 : List Sig := roots 90
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude90_0 : Impossible true (goalAt 90) 3 state90_0.toFinset :=
  node_ok cuts90 [] 0x160605242149084818160604a42129085018129085242048284a42068605818120281a18149085040141085042129084840121084842 (by decide +kernel)

theorem lower90 : Claim 90 4 :=
  fromSearch 50421824 (by decide +kernel) exclude90_0

def rule91_0 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower89 none (by decide +kernel)

def rule91_1 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower83 none (by decide +kernel)

def rule91_2 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower90 none (by decide +kernel)

def rule91_3 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower73 none (by decide +kernel)

def rule91_4 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower27 none (by decide +kernel)

def rule91_5 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower81 none (by decide +kernel)

def cuts91 : Cuts (goalAt 91) := [rule91_0,rule91_1,rule91_2,rule91_3,rule91_4,rule91_5]

def state91_0 : List Sig := [0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_0 : Impossible true (goalAt 91) 4 state91_0.toFinset :=
  node_ok cuts91 [] 0x6828504214108124006860504214109000312108504204828484212028484212108090306860484212108121810d0850420440c434210d08484202c28434202c28434210d080b0a064605818 (by decide +kernel)

def state91_1 : List Sig := [0xeeeeeeeeeeeeeeee0000000000000000eeeeeeeeeeeeeeee,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_1 : Impossible true (goalAt 91) 4 state91_1.toFinset :=
  node_ok cuts91 [] 0x581814108504212060484214108120a12108581812108484214060434214108110310d084342121080b0a10d08591810d084342160601a0a141081a18141081210121081a1812108191810d080b0a10d08480a (by decide +kernel)

def state91_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_2 : Impossible true (goalAt 91) 5 state91_2.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_1,exclude91_1⟩] 0x5818068285818128285242149085818149085242128281a0a1206058180240c5818140404a42129085818129084a42140400903140601a0a129084a42149090005149081a0a4000c120a149084a4212908410302c280b0a16060434210d08410310d084342160600b0a16060110310d0843421490900021450811034000c110314908434210d08090310d084342129080b0a12508090302c280b0a12908434210d090000400004140128281a180686058188000458181282a0000120285818068601a18149090003149085040068605040149081a181410850404000c5042129081210129084840068604840129081a18121084840048404842 (by decide +kernel)

def state91_3 : List Sig := [0x5555555555555555444444444444444455555555555555554444444444444444,input 0,input 6,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_3 : Impossible true (goalAt 91) 4 state91_3.toFinset :=
  node_ok cuts91 [] 0x1a0a14108504204900484214108120a12108480a1210848420240c09081410819181410811101210819181210819181646041030646050420686050420440c4842068604842048601a1816060480a068604342 (by decide +kernel)

def state91_4 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_4 : Impossible true (goalAt 91) 5 state91_4.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_3,exclude91_3⟩] 0x10003068281a0a120285042141090003141085042120281a0a049001a18044041a184000c5042141081a181410850424000c11010440c1a0a121084842141090005141081a0a4000c120a14108484212108480a02c0c480a1040c484212108480a1210848421040c0b0302c0c1a18024041a18048404842121081a1812108484204840090104860130310d08434214108191814108130306460191814108434210d080b0310d084342121081918121080b0306460191812108434210d08410306460191812028434210d08410310d08434212028191806462000106460191806860434210d0a000010d084342068601918064610000400005818 (by decide +kernel)

def state91_5 : List Sig := [0xff00ff00ff00ff00aa00aa00aa00aa00ff00ff00ff00ff00aa00aa00aa00aa,input 0,input 6,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_5 : Impossible true (goalAt 91) 4 state91_5.toFinset :=
  node_ok cuts91 [] 0x160605242149084818149085040141085042068605818120281a1810d08524206460434210500434210d08414206460434210d08191812908120a149084a42121084842129084840140604a4212908581810d08191810d084a42 (by decide +kernel)

def state91_6 : List Sig := [0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,input 0,input 6,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_6 : Impossible true (goalAt 91) 5 state91_6.toFinset :=
  node_ok cuts91 [⟨state91_0,exclude91_0⟩,⟨state91_5,exclude91_5⟩] 0x1a0a149085242068281a0a149085242068284a4214908120a129080b03129084a4202c0e0001129084a42400045242141005042141084a42121004842121081a18104044103068601a1840002000006860581810d08524204c0c434210d084a4202c0c434210500434210d08414210c0c4342400081918 (by decide +kernel)

def state91_7 : List Sig := roots 91
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude91_7 : Impossible true (goalAt 91) 6 state91_7.toFinset :=
  node_ok cuts91 [⟨state91_2,exclude91_2⟩,⟨state91_4,exclude91_4⟩,⟨state91_6,exclude91_6⟩] 0x4000c58180682858184000c4a0a1490852424000c58181490852424000c4a0a06828481840004581802c0c5818400045010129084a42400045818129084a4240004501002c0c5018400041a0a129084a42400045242400045242400041a0a4000c120a400045242129084a42400004a0a068601a18400005818400005818400004a0a80004480a400005818068601a184000052424000c5242400005040068605040400005242068605042400005040400005042400004a42048404a42400004840068604840400004a4206860484240000484004840484240010430306460191840008581810d08434280008430310d0843424000858180646019184000c130310d0843424000852420646052424000c130306460191840008524210d084342400040b0310d084342400044a42064604a42400040b03064601918400044a4210d084342400010000105004140400001a1810d08434240002000010d084342400001a18105004142 (by decide +kernel)

theorem lower91 : Claim 91 7 :=
  fromSearch 67 (by decide +kernel) exclude91_7

def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x4c0c32220c88812220484032300c8c012300c88832300c8c011030444031300c4c0113008c8831300c4c023220c4c0323008c883130 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 68 (by decide +kernel) exclude51_0

def rule59_0 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower57 none (by decide +kernel)

def rule59_1 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower51 none (by decide +kernel)

def rule59_2 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower41 none (by decide +kernel)

def rule59_3 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower27 none (by decide +kernel)

def cuts59 : Cuts (goalAt 59) := [rule59_0,rule59_1,rule59_2,rule59_3]

def state59_0 : List Sig := [0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_0 : Impossible true (goalAt 59) 4 state59_0.toFinset :=
  node_ok cuts59 [] 0xa06038300e0c0090302c28232208c88281808c88383002c2838300c4c01a180c8c032300686032300e0c02a220c8c012220c88832220a0602a220e0c02a220e0c023220440c23220c4890002 (by decide +kernel)

def state59_1 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_1 : Impossible true (goalAt 59) 5 state59_1.toFinset :=
  node_ok cuts59 [⟨state59_0,exclude59_0⟩] 0x38180682838180a82832220c88838180c88832220a8281a0a0a06038180240c38180840c38300e0c038180e0c038300840c09030240c1a0a0a8882a220c88838300e0c01a0a0e0c038300c8882a220a0c0210302c280b0a0e060232208c88210308c8823220e0600b0a0e060110308c8823220c88900020c48811034000811030c888232208c88090308c8823220e0c00b0a0e0c0090302c280b0a0e0c023220e0c100004000031300a8281a180686038180c8c032300a82832300c8c03818068601a180c88900020c88a00000c8c032300c88832300c8c100024000900020a88832300c8c038300686038300a8881a180a08838300c8c03230 (by decide +kernel)

def state59_2 : List Sig := [0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 0,input 3,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_2 : Impossible true (goalAt 59) 4 state59_2.toFinset :=
  node_ok cuts59 [] 0xc88832300c8c011030c8c038300a08832300a88838300e0c0283008c8831300c4c023220c4c0323008c8831300c4c038300646031300a06032220e060322206860323006860323002c0c38300e0603830064603130064603130 (by decide +kernel)

def state59_3 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_3 : Impossible true (goalAt 59) 5 state59_3.toFinset :=
  node_ok cuts59 [⟨state59_2,exclude59_2⟩] 0x38180c88832220a0601a180c8c032300686032220c8c032300440c3230068601a180c8c03230068601a180c8c0381808c0c381802c0c1a0a0c8881a0a0c888383006460381808c0c191802c28322206460322206460323002c28323002c0c19180446031300e06200000e0610003068283222068283222 (by decide +kernel)

def state59_4 : List Sig := [0xcceecceecceecceecceecceecceecceecceecceecceecceecceecceecceeccee,input 0,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_4 : Impossible true (goalAt 59) 4 state59_4.toFinset :=
  node_ok cuts59 [] 0xe06032220c88828180e06038300e0c00b030a88838300e0c0283006460232208c88191808c8831220646023220e4c038300646038300c4c0313008c8832300686032300c8c01a180c88832300c8c100020c8c038300a0883230 (by decide +kernel)

def state59_5 : List Sig := [0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,input 0,input 3,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_5 : Impossible true (goalAt 59) 5 state59_5.toFinset :=
  node_ok cuts59 [⟨state59_4,exclude59_4⟩] 0x38180c88832220a0601a180c8c032300686032220c8c032300440c32300e0c028220c8c038180e0c0383008c0c2a220e0c038300a0c019180e0602303064600b0a0c88819180c88819180c8c00b0a0c8c0393006460383008c0c381808c0c381804c0c322204c0c322240000323080000323002c0c3130 (by decide +kernel)

def state59_6 : List Sig := [0xff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa,input 0,input 5,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_6 : Impossible true (goalAt 59) 4 state59_6.toFinset :=
  node_ok cuts59 [] 0xe06032220c88828180c88832300c8c011030686032300c8c01a1808c8831300c4c023220c4c0323008c8831300646031300c4c019180a0c038300e0c02a220c8c028220c8c0383002c0c38300e0c038180c4c019180c4c03830 (by decide +kernel)

def state59_7 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_7 : Impossible true (goalAt 59) 5 state59_7.toFinset :=
  node_ok cuts59 [⟨state59_6,exclude59_6⟩] 0x1a0a0c8883222068281a0a0c8883222068282a220e0c038300a0c00b030e0c0383002c0e00000e0c038304000432220c8c032300440c32300e0c028220c8c01a180c8c03230068601a180c8c0323006860381808c8831300c4c023220c4c0383002c0c31300c4c0323008c88313008c0c3130044c01918 (by decide +kernel)

def state59_8 : List Sig := [0xcccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeee,input 0,input 5,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_8 : Impossible true (goalAt 59) 4 state59_8.toFinset :=
  node_ok cuts59 [] 0xe06032220c88828180a88838300e0c028300e06038300e0c0090308c8831300c4c023220c4c0383002c2831300e46031300c4c038180c4c0323008c8831300c88832300c8c100020c8c038300a08832300686032300c8c01a18 (by decide +kernel)

def state59_9 : List Sig := [0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,input 0,input 5,input 1,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_9 : Impossible true (goalAt 59) 5 state59_9.toFinset :=
  node_ok cuts59 [⟨state59_8,exclude59_8⟩] 0x38180c88832220a0602a220e0c038300a0c038180e0c0383002c0c32220c8c032300440c32300e0c028220c8c01a180c8c032300686023220c4c0313008c8831300e0c00b030c4c031300c8c023220c4c039180c4c0381804c0c322204c0c322202c0c383002c0c383040000323080000323008c0c1918 (by decide +kernel)

def state59_10 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_10 : Impossible true (goalAt 59) 5 state59_10.toFinset :=
  node_ok cuts59 [] 0x38180c88832220a06013030c888322204c0c32220c8c032300440c1a180c8c032300686032300e0c028220c8c012100c8c032300484023220c4c0313008c8831300c8c023220c4c019180c4c031300646031300e0c019180c4c011100c4c031300444023030a88838300e0c028300e0603830400040b03 (by decide +kernel)

def state59_11 : List Sig := roots 59
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude59_11 : Impossible true (goalAt 59) 6 state59_11.toFinset :=
  node_ok cuts59 [⟨state59_1,exclude59_1⟩,⟨state59_3,exclude59_3⟩,⟨state59_5,exclude59_5⟩,⟨state59_7,exclude59_7⟩,⟨state59_9,exclude59_9⟩,⟨state59_10,exclude59_10⟩] 0x400083818068283818400082a0a0c88832224000838180c8883222400082a0a0682828184000c381802c0c38184000423030e0c038308001438180e0c0383040004230302c0c0b03400081a0a0a8882a224000432220e0c03830400081a0a0e0c038304000432220a8882830400002a0a068601a184000038180c8c03230400002a0a0c8c03230400003818068601a184000032224000832224000011010c8c032304000032220c8c03230400001101400001103400002a220c8c03230400003830068603830400002a220686028224000038300c8c032304000c23030646019188001038180c4c031308000c23030c4c031304000c381806460191840008130308c8823224000832220c4c031304000813030c4c0313040008322208c882322400040b030c4c03130800083830064603830800040b030646019184000438300c4c031304000100000c4c0313040000323008c88323040002000008c8823224000032300c4c03130 (by decide +kernel)

theorem lower59 : Claim 59 7 :=
  fromSearch 67 (by decide +kernel) exclude59_11

def cuts120 : Cuts (goalAt 120) := []

def state120_0 : List Sig := roots 120
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude120_0 : Impossible true (goalAt 120) 3 state120_0.toFinset :=
  node_ok cuts120 [] 0x1c0c05818140c050301c0c070601c18048181410070601c18050600e0c068601a18038301210068601a18048601a18070600e0c06860 (by decide +kernel)

theorem lower120 : Claim 120 4 :=
  fromSearch 53891072 (by decide +kernel) exclude120_0

theorem lower122 : Claim 122 5 :=
  fromLift 5 2 53563456 lower120 (by decide +kernel)

def rule123_0 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 none (by decide +kernel)

def rule123_1 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower115 none (by decide +kernel)

def rule123_2 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower105 none (by decide +kernel)

def rule123_3 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower91 none (by decide +kernel)

def rule123_4 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 none (by decide +kernel)

def rule123_5 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower113 none (by decide +kernel)

def rule123_6 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower120 none (by decide +kernel)

def rule123_7 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower89 none (by decide +kernel)

def rule123_8 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower91 (some (1,input 0,input 1)) (by decide +kernel)

def rule123_9 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower57 none (by decide +kernel)

def rule123_10 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 (some (1,input 0,input 1)) (by decide +kernel)

def rule123_11 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 none (by decide +kernel)

def rule123_12 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower90 none (by decide +kernel)

def rule123_13 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower81 none (by decide +kernel)

def rule123_14 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower73 none (by decide +kernel)

def rule123_15 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower41 none (by decide +kernel)

def rule123_16 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower83 none (by decide +kernel)

def rule123_17 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 (some (1,input 0,input 3)) (by decide +kernel)

def rule123_18 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 (some (2,input 0,input 3)) (by decide +kernel)

def cuts123 : Cuts (goalAt 123) := [rule123_0,rule123_1,rule123_2,rule123_3,rule123_4,rule123_5,rule123_6,rule123_7,rule123_8,rule123_9,rule123_10,rule123_11,rule123_12,rule123_13,rule123_14,rule123_15,rule123_16,rule123_17,rule123_18]

def state123_0 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_0 : Impossible true (goalAt 123) 5 state123_0.toFinset :=
  node_ok cuts123 [] 0x7030160605030140c031301c0c0480a0c4c019180c4c031300646063621858063624001431300e0c019180c4c011030c4c0313008cc0703018d88636208d88434218d88636210d8863621c5880b0a18d8838301c0c050180e0c038180e0c038300840c0b0a18d88383018d886a621c0c041031c0c011030e06021030e0601103 (by decide +kernel)

def state123_1 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_1 : Impossible true (goalAt 123) 6 state123_1.toFinset :=
  node_ok cuts123 [⟨state123_0,exclude123_0⟩] 0x70300e060703016061000e1606070304003c5030160603818140c058180e0c038301c0c06a621a98858181a9886a621c0c038300e0c03818129084a420840c6a621a98838181a9886a620840c4a421298900021a9886a620440c38300e0c200000e0c038300440c6a621a9880b0a1a988696218d88383018d880b0a0e0c0383018d886a6218d884a0a0c4c031301c0c1000f1c0c04a0a4003c480a1c0c031300c4c02a0a0646019180e06031300c4c02a0a0c4c031300e0601918064606a620c4c06a621a18019181a1806a620646068621a18031301a18811034000811034001831300c4c011030c4c0313040009000208cc063624000863624000031301858063620c4c063624000100024000070300440c70301282900021282870304003c70301282811031282838180440c38180a82900020a82838184003838180a82811030a82900024002c71621c0c023221c0c04a0a18d8863621c0c0636218d884a0a08c8823620e060434210d082a0a18d8863620e060636218d882a0a10d084362 (by decide +kernel)

def state123_2 : List Sig := [0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_2 : Impossible true (goalAt 123) 6 state123_2.toFinset :=
  node_ok cuts123 [] 0x1c0c038181c0c058184003858181c0c1000f140c058180e06050301606038300e0c070301a9886a62160606a621a98870300e0c038300e0604a421290821031a9886a620e0606a621a9882103129084a62064286a621a98871620e0c071620642838300e0c071621a9886a621282831300c4c070304003c703012829000f1202870300c4c031300a82819180646038180c4c031300a82831300c4c038180646019181a98831301a98868600646068601a98819181a18868600c4c068621c58900021c58870600c4c070601c58831301c18870604000870621c0c031221c0c04a0a1c58871621c0c071621c5884a0a0c48833620e0605142145082a0a1c58871620e06071621c5882a0a1450853621040c232208c88703018d8863621040c636218d88703008c8870300840c434210d08381818d8863620840c636218d88381810d0843620240c636218d886a6202c2869620240c0b0a02c286a6218d88636240009000218581000b400081103 (by decide +kernel)

def state123_3 : List Sig := [0xffeeffee00000000ffeeffee00000000ffeeffee00000000ffeeffee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_3 : Impossible true (goalAt 123) 5 state123_3.toFinset :=
  node_ok cuts123 [] 0x50301c98872620c988232218d886362140c063621c588110318d8863621a5880b0a18d8861600e0c06a621a98838301a98872620e0c06a620c8c050301202832301c98870601c18870621a98868601a18868620e060503016060503014988726214908726210d88636210d086362129886a62129086a62068603230068603230 (by decide +kernel)

def state123_4 : List Sig := [0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_4 : Impossible true (goalAt 123) 6 state123_4.toFinset :=
  node_ok cuts123 [⟨state123_3,exclude123_3⟩] 0x7030160605030140c070301c98872620c98852421c988726214988232218d8863621c0c0434218d88636210d8863621c588110318d8863621a5880b0a18d881918400142a221a9886a621c0c04a421a9886a62129886a621c988120a1a98868600686070301202870300686038180a0281a181c98870601c98870601a9881a181a18832301606070301606070300e06200000e06100071c98870601c9887060 (by decide +kernel)

def state123_5 : List Sig := [0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_5 : Impossible true (goalAt 123) 6 state123_5.toFinset :=
  node_ok cuts123 [] 0x7030160605030140c038301a9886a620e0c04a421a9886a62129886a621c98838301a98868601a9886a621a180232218d8863621c0c0434218d88636210d8863621a5880b0a18d8863621c588110318d8831304000870301c98872620c98852421c98872621498870600c8c070301282832300686032300c8c01a181a98868601a98868601c98832301c18900021c0c048081c0c048080e06028080e0602808 (by decide +kernel)

def state123_6 : List Sig := [0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 0,input 3,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_6 : Impossible true (goalAt 123) 5 state123_6.toFinset :=
  node_ok cuts123 [] 0x50301c98872620c9083230140c0480a0c8c072621c18070621c1886a621a18068621a18838301a9886a620e0c06a621c98838301a988232218d886362140c063621c588110318d88616018d88696202c2863620e06050301606050300a06072620e0607262068603230068603230129886a620e0606a6210d88636202c286362 (by decide +kernel)

def state123_7 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_7 : Impossible true (goalAt 123) 6 state123_7.toFinset :=
  node_ok cuts123 [⟨state123_6,exclude123_6⟩] 0x1c0c05818140c050301c0c072621c98832621490872621c98852620c8c070301202832300686032300c8c01a181c98870601c18870620c8c01a180686032300c8c01a180686032301606070301606070300e06021030e06009030682872620682872621a9880b0a1c0c041031c0c00b0a0e06021030e0600b0a1c98811031c98819180240c0b0a4001463621606070301606070300e06200000e0610007068287262068287262 (by decide +kernel)

def state123_8 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_8 : Impossible true (goalAt 123) 6 state123_8.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050300e0c06a621a9883830129086a621a9884a621a98838300e0c06a621a98838300e0c06a620c8c070301202832300686032300c8c01a181a98868601a18868620440c32300c8c100024000832300c8c100001c0c04a0a1c0c04a0a0e0602a0a0e0602a0a1c98841031c0c041031c0c021030e06021030e06009031a98809031a98831300440d000b0480c63621c0c04a0a1c0c04a0a0e0602a0a0e0602a0a (by decide +kernel)

def state123_9 : List Sig := [0x1111110011111100111111001111110011111100111111001111110011111100,input 3,input 4,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_9 : Impossible true (goalAt 123) 5 state123_9.toFinset :=
  node_ok cuts123 [] 0x7030160605030140c0232218d8863621c0c0434218d88636210d8063621c588110318d8863621a5880b0a18d8870301c98872620c98052421c98872621498038301a9886a620e0c04a421a9886a62129806a621c98838301a98832301202870300c8c01a180c8c032300686031301c18870620c8c072621a18868620e0c06a62 (by decide +kernel)

def state123_10 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_10 : Impossible true (goalAt 123) 6 state123_10.toFinset :=
  node_ok cuts123 [⟨state123_0,exclude123_0⟩,⟨state123_9,exclude123_9⟩] 0x1c0c05818140c0503008c88636218d88703010d08636218d8843621858063620642a000018d8863620e0c00b0a18d88636202c280b0a18d8832301c0c0480a0c8c01a180c8c03230068601a0a0c8c032304000832300e0c01a180c8c200010c8c032304001870301282870301206038180a82828180a06072620e0c070301406038300e06038300e0c021030682838300a0c06a621c0c041031c0c041030e06021030e0602103 (by decide +kernel)

def state123_11 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_11 : Impossible true (goalAt 123) 7 state123_11.toFinset :=
  node_ok cuts123 [⟨state123_1,exclude123_1⟩,⟨state123_2,exclude123_2⟩,⟨state123_4,exclude123_4⟩,⟨state123_5,exclude123_5⟩,⟨state123_7,exclude123_7⟩,⟨state123_8,exclude123_8⟩,⟨state123_10,exclude123_10⟩] 0x4002470300e06070304001c58184002058184002070304002850304002458180e06050304002470300c8887030400084a0a1c98872624003c70301c9887262400084a0a0c88832624001c3818149085242400082a0a1c98872624003838181c9887262400082a0a1490852624002458180e0c038304001470301a9886a624002858181a9886a624001470300e0c038304001c3818129084a424001421031a9886a624003438181a9886a62400142103129084a62400081a0a1a9886a624001472620e0c07262800181a0a0e0c038304001472621a9886a6240024410308c8823224002c703018d88636240028410318d88636240024703008c8870304001c210310d0843424002c381818d88636240030210318d8863624001c381810d08436240008110318d8863624002c726280004716280014110380000110340008726218d88636240014090318d8863624002c6a6202c28696280010090302c280b0a400146a6218d886362400010000400006160400244a0a0c8c03230400187030400287030400284a0a40028480a4002470300c8c032304001c2a0a068601a184001838180c8c03230400202a0a0c8c032304001c3818068601a184000872624000872624001870600c8c070608000c72620c8c07062400087060400087062400146a620c8c06a62400186860068606860800086a620686068624001468600c8c06862 (by decide +kernel)

def state123_12 : List Sig := [0xbbbbaaaabbbbaaaabbbbaaaabbbbaaaabbbbaaaabbbbaaaabbbbaaaabbbbaaaa,input 0,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_12 : Impossible true (goalAt 123) 6 state123_12.toFinset :=
  node_ok cuts123 [] 0x70300e060703016061000e1606070304003c5030160603818140c058180e0c038301c0c068621a18858181a18868621c0c038300e0c038181210848420840c68621a18838181a18868620840c4842129801a0a1a18868621c98838301c9881a0a0e0c038301c98868621a18870300c88870301202872621c98870301c98872621202832220c98038181490852420a02872621c98838181c98872620a02852421498041030c4c031301c0c1000f1c0c041034003c41031c0c031300c4c021030646019180e06031300c4c021030c4c031300e06019180646009030c4c031301a18819181a18809030646019181a18831301a18811034000811031c98831301c98811030c4c031301c98900021c98900024000863621c0c032300c8c0480a4003c480a1c0c1000f1c0c0480a0c8c032300e0601a1806860280a0c8c032300e06032300c8c0280a068601a180e0c032300c8c068620686068620e0c01a180e0c068620c8c068620440d00001c18872620c8c070620440c32300c8c07262400007262 (by decide +kernel)

def state123_13 : List Sig := [0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 0,input 3,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_13 : Impossible true (goalAt 123) 5 state123_13.toFinset :=
  node_ok cuts123 [] 0x50301c98872620c90032301202850300c8c070620c8c068620e0c068620c4c063620c4c063620e0c068621a18838301a18872620e0c068620c4c0636218d88313018d8872620c4c0636218d8868620646063620e06050301606050300682872620e06072620686032300686032301298068620e060686210d806362064606362 (by decide +kernel)

def state123_14 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_14 : Impossible true (goalAt 123) 6 state123_14.toFinset :=
  node_ok cuts123 [⟨state123_13,exclude123_13⟩] 0x1c0c05818140c050301c0c072621c98832601490872621c98852600c8c0480a1c0c032300686032300c8c01a181c1883230068601a180c8c0323002c2819180c8c03230068601a180c8c058181c0c058181c0c038180840c38180240c1a0a1c9881a0a1c98868620646070301040c70300646038180840c191802c2872620646072620240c19180446063621606070301606070300e06200000e0610007068287262068287262 (by decide +kernel)

def state123_15 : List Sig := [0x33bb00aa33bb00aa33bb00aa33bb00aa33bb00aa33bb00aa33bb00aa33bb00aa,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_15 : Impossible true (goalAt 123) 5 state123_15.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050301c0c072621c98832601490872621c98852600e0c068621a18838301210868621a1884a601a18872620e0c068620c4c070301040c31300646031300c4c0191802c2872620c4c072621a58868620646068620c8c0480a1c0c032300686032300c8c01a181c18870620c8c072620c8c068620e0c0686218d8863620c4c03230 (by decide +kernel)

def state123_16 : List Sig := [0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,input 0,input 3,0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_16 : Impossible true (goalAt 123) 6 state123_16.toFinset :=
  node_ok cuts123 [⟨state123_15,exclude123_15⟩] 0x1c0c05818140c050301c0c072621c98832601490872621c98852600c8c0480a1c0c032300686032300c8c01a181c18832301a18838301a188323002c2819180c8c038301a18868620e0c048421a18868621298068621c98838301a18819181c0c041031c0c019180e0602103064600b0a1c98819181c98869620646068621040c70301040c70300840c38180840c381804c0c726204c0c72624000832308000032300240c6362 (by decide +kernel)

def state123_17 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_17 : Impossible true (goalAt 123) 7 state123_17.toFinset :=
  node_ok cuts123 [⟨state123_12,exclude123_12⟩,⟨state123_14,exclude123_14⟩,⟨state123_16,exclude123_16⟩] 0x4002470300e06070304001c58184003858184003870304003c50304002458180e06050304002458180e0c038304001470301a18868624003c58181a18868624001470300e0c038304001c38181210848424001421031a18868624003838181a1886862400142103121084a60400081a0a1a18868624001472620e0c07262400081a0a0e0c038304001472621a18868624002441030c4c031304003c703018d8863624003c410318d8863624002470300c4c031304001c210310d08434240038381818d88636240038210318d8863624001c381810d08436040014090318d88636280008686206460686280004090306460191840014686218d88636240008130318d8863624000872620c4c072624000813030c4c0313040008726218d8863624000870300c888703040008480a1c98872624000870301c988726240008480a0c888326040008381814908524240008280a1c98872624000838181c988726240008280a1490852604000870300c8c0323040008480a40008480a4000870304003c703040008480a0c8c03230400083818068601a1840008280a0c8c032304000838180c8c0323040008280a068601a184001438300c8c032304000868620686068624000838300686038304001468620c8c068624000831300c8c031304000863624000863624000831308000031304000863620c8c06362400010000400007062 (by decide +kernel)

def state123_18 : List Sig := [0xffffffffffffffff00000000ffaaffaaffffffffffffffff00000000ffaaffaa,input 6,input 0,input 3,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_18 : Impossible true (goalAt 123) 5 state123_18.toFinset :=
  node_ok cuts123 [] 0x32221c98872620c88832221c98872620c88872621c18070621c1886a621a18068621a188323016060480a0c8c03230068601a180c8c06a621c98838301a98838301a9886a620e0c038301a9886a620e0c063621c988313018d88616018d8863621858863621a988191818d88313018d8863620c4c0313018d8863620c4c05030 (by decide +kernel)

def state123_19 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffaaffaa000000000000000000000000ffaaffaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_19 : Impossible true (goalAt 123) 4 state123_19.toFinset :=
  node_ok cuts123 [] 0xc8c070621c18811031a18870620e0c068620e0c068621a188323018d8870620c4c0636218d8868620646063620c4c0636218d8831300a06070620e060706202c0c68620e0606862064606362064606362068603230068603230 (by decide +kernel)

def state123_20 : List Sig := [0xffaaffaa000000000000000000000000ffaaffaa,input 6,input 0,input 3,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_20 : Impossible true (goalAt 123) 5 state123_20.toFinset :=
  node_ok cuts123 [⟨state123_19,exclude123_19⟩] 0x50301c98872620c90872621c18070621c1886a621a18068621a1883230140c200000c8c06a621c98838301a98838301a9886a620e0c063621c988313018d88616018d8863621858863621a988191818d88313018d8863620c4c028181c98838181c9881a180c8c01a180c8c00b031a98838181a988191818d88191818d885818 (by decide +kernel)

def state123_21 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_21 : Impossible true (goalAt 123) 5 state123_21.toFinset :=
  node_ok cuts123 [⟨state123_19,exclude123_19⟩] 0x32221c18870620c90032301c18870620440c68621c18838301a18838301a18868620e0c038301a18868620c8c063621c188313018d8863621a188191818d88313018d8863620c4c0313018d8863620c4c028181c18838181c1884a601a18838181a188436018d88191818d88381880000480a0e0601a180c8c01a180c8c05030 (by decide +kernel)

def state123_22 : List Sig := [0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 0,input 3,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_22 : Impossible true (goalAt 123) 6 state123_22.toFinset :=
  node_ok cuts123 [⟨state123_6,exclude123_6⟩,⟨state123_13,exclude123_13⟩,⟨state123_18,exclude123_18⟩,⟨state123_20,exclude123_20⟩,⟨state123_21,exclude123_21⟩] 0x140c03222140c04a0a1c9887262140c072621c9884a0a0c88832421282832300c8c050304003450301282a00041202850300c8c032301c98a00011c98870600c8c070601c98832301c18870604003470621a98832301a98868600686068601a9881a181a18868600c8c068621606038300e0c050301a9886a62160606a621a98850300e0c03830068286a621a98872620e0c072620682838300e0c072621a9886a6210c0c31300c4c0503018d88636210c0c636218d8850300c4c0313004c0c636218d8872620c4c0726204c0c31300c4c0726218d88636240034616018580323018d88636280000636218d88323018580616202c0c636218d886a62064606a6202c0c1918064606a6218d8863621606038180e06050308000c50301606200021606050300e0605030068282a0a0a06072620e06072620682838180e06072620a82872620686038180686032300a8283230068602a0a0686032300e060323002c0c2303129886a620e0606a6202c0c38180e0606a6208c0c6a6206460381810d88636208c0c63620646023030646063620e0606362 (by decide +kernel)

def state123_23 : List Sig := [0xffffffaa00000000ffffffaa00000000ffffffaa00000000ffffffaa,input 4,input 0,input 3,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_23 : Impossible true (goalAt 123) 5 state123_23.toFinset :=
  node_ok cuts123 [] 0xc8c070301202832301a98868601a18868621c98870601c18870620e0c06a621a98838301a98872620e0c06a620c4c0636218d88313018580636218d88616218d886a6206460636218d8872620c4c063621c0c072621c9883242140c05030160607030068603230068603230129886a620e0606a6210d8863620646063621498872620e0607262 (by decide +kernel)

def state123_24 : List Sig := [0xffffffaaffffffaa0000000000000000ffffffaaffffffaa,input 4,input 0,input 3,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_24 : Impossible true (goalAt 123) 5 state123_24.toFinset :=
  node_ok cuts123 [] 0x686032300c8c01a181a98868601a18868621c98870601c1887062129086a621a9884a621a98872620e0c06a6210d08636218d88436218580636218d88616218d886a6206460636218d8872620c4c063621490872621c9885262140c050301c0c058180c8c0480a0c8c070300e0c06a620e0c06a620c4c063620c4c063620c98872621c0c07262 (by decide +kernel)

def state123_25 : List Sig := [0x3333332233333322333333223333332233333322333333223333332233333322,input 4,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_25 : Impossible true (goalAt 123) 5 state123_25.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050300e0c06a621a9883830129086a621a9884a601a98872620e0c06a620c4c0636218d88313010d08636218d88436018d886a6206460636218d8872620c4c063621c0c072621c98832601490872621c98852600c8c0480a1c0c032300686032300c8c01a181a18868620e0c06a621858863620c4c063621c18870620c8c07262 (by decide +kernel)

def state123_26 : List Sig := [0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaa,input 4,input 0,input 3,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_26 : Impossible true (goalAt 123) 6 state123_26.toFinset :=
  node_ok cuts123 [⟨state123_23,exclude123_23⟩,⟨state123_24,exclude123_24⟩,⟨state123_25,exclude123_25⟩] 0x7030160605030140c032301c0c0480a0c8c01a180c8c032300686032300e0c01a180c8c01a0a0c8c032300440e00020c8c032304000038301c0c050180e0c038180e0c0383002c0c1a0a0e0c038300a0c06a620c4c0703010c0c31300646031300c4c019180c4c0323002c2831300c4c0383006460313002c2831300c4c0213018d8870301282870301206038180a82828180a06072621c0c200011c0c100040e06200000e0610003 (by decide +kernel)

def state123_27 : List Sig := [0xccccffeeccccffeeccccffeeccccffeeccccffeeccccffeeccccffeeccccffee,input 4,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_27 : Impossible true (goalAt 123) 5 state123_27.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050300e0c068621a18838301210868621a1884a621a18872620e0c068620c4c0636218d88313010d08636218d88436218d88686206460636218d8872620c4c0636218580636218d8831301c0c072621c98832621490872621c98852620c8c070301202832300686032300c8c01a181a18868601a18832301c98870601c1887062 (by decide +kernel)

def state123_28 : List Sig := [0xffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa,input 4,input 0,input 3,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_28 : Impossible true (goalAt 123) 6 state123_28.toFinset :=
  node_ok cuts123 [⟨state123_27,exclude123_27⟩] 0x7030160605030140c032301c0c0480a0c8c01a180c8c032300686032300e0c01a180c8c072621c18070621c18838301c0c050180e0c038180e0c0383002c0c7a621c98838301c98831301c0c043030c4c019180c4c031300646031300c8c00b0a0c4c031300e0c019180c4c073621c98831301c98870301c98872620c98852421c9887262149884a0a1c0c04a0a1c0c02a0a0e0602a0a0e06100000c8c200000c8c06a621a9880b030e0c0636218d880b0a0c4c01a0a (by decide +kernel)

def state123_29 : List Sig := [0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_29 : Impossible true (goalAt 123) 6 state123_29.toFinset :=
  node_ok cuts123 [] 0x140c072621c98832420c8c050301202832301c98870601c18870620c8c01a180686032300c8c01a180686032301606050301606050300682872620682872621a9881918140c04303140c00b0a1c98819181c98819180c8c00b0a0c8c00b0306460111818d885818140c05818140c01a0a1c9881a0a1c9883818140c05818140c028181c98838181c9881a180c8c01a180c8c00b030e060381808c0c191808c0c19180e0610003 (by decide +kernel)

def state123_30 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_30 : Impossible true (goalAt 123) 6 state123_30.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050300c8c070301202832300686032300c8c01a180c8c038300686032300682832300c8c1000502c0c32300c8c0090306460703010c0c703006460311808c0c191806460323002c28323018d880b0a06460191802c280b030646019184002c38301c0c050180e0c038180e0c03830400401a0a0e0c038300a0c06a621a98838304000870301282870301206038180a82828180a06072621c0c043031c0c00b030e06023030e0600b03 (by decide +kernel)

def state123_31 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_31 : Impossible true (goalAt 123) 7 state123_31.toFinset :=
  node_ok cuts123 [⟨state123_7,exclude123_7⟩,⟨state123_14,exclude123_14⟩,⟨state123_22,exclude123_22⟩,⟨state123_26,exclude123_26⟩,⟨state123_28,exclude123_28⟩,⟨state123_29,exclude123_29⟩,⟨state123_30,exclude123_30⟩] 0x70300e0607030160610010160607030400445030160603818140c070300c88870301282872621c98870301c98872621282832220c98838181490852420a82872621c98838181c98872620a8285242149884a0a0c8c032301c0c100051c0c04a0a40044480a1c0c032300c8c02a0a068601a180e06032300c8c02a0a0c8c032300e0601a180686072628000472621c18032301c18072620c8c070621c18100051c1880b030c8c03230024041a18068600b03068601a180240432300c8c100050c8c03230400001a18068610005068601a184000032300c8c0581802c0c58181c0c100011c0c058184004458181c0c00b031c0c0381802c0c381808c0d000108c0c381840040381808c0c0b0302c0c1a0a02c0c1a0a1c98900011c9881a0a800181a0a1c9880b031c98900014002c6a6210c0c191806460703040044703010c0d001110c0c703006460703008c0c191806460381840040381808c0d001008c0c381806460191804c0c0b0a02c28726206460726204c0c191806460726202c28726240014191806460323002c283230800000b0a02c28323006460323002c0d000102c0d000b0646019184000500010446100014000463621606100041606070304004470301606100111606070304001070300e06100030e06200054004200020e06100100e06100104000d00030682900020682872628001072620682a0003068287262400087262 (by decide +kernel)

def state123_32 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffcceecceecceecceeffffffffffffffffcceecceecceeccee,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_32 : Impossible true (goalAt 123) 4 state123_32.toFinset :=
  node_ok cuts123 [] 0xc8c070621c189000e0e06070621c18828181a18870620e0c068620e0c068621a18832300e06068621a1880b0318d88706206460636218d8868620646063620c4c0636218d88323006460636218d8819180686032300c8c01a18 (by decide +kernel)

def state123_33 : List Sig := [0xffffffffffffffffcceecceecceecceeffffffffffffffffcceecceecceeccee,input 6,input 0,input 3,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_33 : Impossible true (goalAt 123) 5 state123_33.toFinset :=
  node_ok cuts123 [⟨state123_32,exclude123_32⟩] 0x38181202a00000e06032300686032300686050421c18870621498032221c18870620c98032301c18870624000848421a18868621298068621c18838301a18838301a18868620e0c038301a18868620c8c0434218d88636210d8063621c188191818d8863621a188191818d88232218d88636208d80313018d8863620c8c07030 (by decide +kernel)

def state123_34 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xcceecceecceecceecceecceecceecceecceecceecceecceecceecceecceeccee,input 0,input 3,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_34 : Impossible true (goalAt 123) 5 state123_34.toFinset :=
  node_ok cuts123 [⟨state123_32,exclude123_32⟩] 0x50301c98872620c90838181c98872620a0606a621c98838301a98838301a9886a620e0c038181a9886a6202c0c63621c588191818d8863621a988191818d88616018d8863620c8c0232218d886362140c0191818d8863620646072621c18070621c1886a621a18068621a1883230140c200000c8c01a180c8c03230068605818 (by decide +kernel)

def state123_35 : List Sig := [0xcceecceecceecceecceecceecceecceecceecceecceecceecceecceecceeccee,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_35 : Impossible true (goalAt 123) 6 state123_35.toFinset :=
  node_ok cuts123 [⟨state123_33,exclude123_33⟩,⟨state123_34,exclude123_34⟩] 0x1c0c038181c0c058184003458181c0c20001140c058180e06050301c0c032221c0c04a0a1c98872621c0c072621c9884a0a0c88832620e0605242149082a0a1c98872620e06072621c9882a0a1490852621606038300e0c070301a9886a62160606a621a98870300e0c038300e0604a421290821031a9886a620e0606a621a9882103129084a62068286a621a98872620e0c072620682838300e0c072621a9886a621040c232208c88703018d8863621040c636218d88703008c8870300840c434210d08381818d8863620840c636218d88381810d0843620440c636218d8872620646071620440c191806460726218d88636202c0c636218d886a62064606a6202c0c1918064606a6218d88636240000191818580323018d88636240000636218d8832300646032301282832300c8c070304001870301282a00001202870300c8c032300a8281a180686038180c8c032300a82832300c8c03818068601a181c98900021c98870600c8c070601c98832301c18870604000870621a98832301a98868600686068601a9881a181a18868600c8c06862 (by decide +kernel)

def state123_36 : List Sig := [0x3333002233330022333300223333002233330022333300223333002233330022,input 4,input 0,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_36 : Impossible true (goalAt 123) 5 state123_36.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050300e0c068621a18838301210868621a1884a601a18872620e0c068620c4c0636218d88313010d08636218d88436018d88686206460636218d8872620c4c063621c0c072621c98832601490872621c98852600c8c0480a1c0c032300686032300c8c01a180c8c068620e0c068621858863620c4c063621c18870620c8c07262 (by decide +kernel)

def state123_37 : List Sig := [0xffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aa,input 4,input 0,input 3,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_37 : Impossible true (goalAt 123) 6 state123_37.toFinset :=
  node_ok cuts123 [⟨state123_36,exclude123_36⟩] 0x7030160605030140c032301c0c0480a0c8c01a180c8c03230068606a621a18068621a18813030c8c032300440e00000c8c032304000038301a9886a620e0c04a421a9886a62129886a620e0c038301a9886a620e0c038301a98831301c0c043030c4c019180c4c031300646031300c8c00b0a0c4c06b621a98819181a9880b0a0c4c03130084c0636218d88313002c2870301282870301282838180a82838180a82872621c0c04a0a1c0c04a0a0e0602a0a0e0602a0a (by decide +kernel)

def state123_38 : List Sig := [0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,input 0,input 3,input 1,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_38 : Impossible true (goalAt 123) 7 state123_38.toFinset :=
  node_ok cuts123 [⟨state123_16,exclude123_16⟩,⟨state123_35,exclude123_35⟩,⟨state123_37,exclude123_37⟩] 0x70300e0607030160610010160607030400485030160603818140c070300c88870301282872621c98870301c98872621282832220c98838181490852420a82872621c98838181c98872620a8285242149884a0a0c8c032301c0c100051c0c04a0a40048480a1c0c032300c8c02a0a068601a180e06032300c8c02a0a0c8c032300e0601a180686072628000072621c18032301c18072620c8c070621c18100051c1886a620c8c06a621a1801a181a1806a620686068621a18032301a18858180e0c038301c0c06a621a98858181a9886a621c0c038300e0c03818129084a4208c0c6a621a98838181a9886a6208c0c4a42129881a0a1a9886a621c98838301c9881a0a0e0c038301c9886a621a98843030646019181c0c1000b1c0c043034004843031c0c019181c0c023030646019180e06100100e06023034004023030e060191806460130302c280b0a1c98819181c98813030646019181c9880b0a1c98900050646019180c8c00b0a0c8c1000b02c280b0a0c8c019180c8c10001400046b624002c1918064606a62400046a6210c0d000410c0c70304002c703010c0d001210c0c703040010703008c0d000308c0c381840040381808c0d001008c0c38184000c381804c0d000204c0c72624002c726204c0e000204c0c72624000872624001500004000032304001432304002d00058000432304000032304002d000102c0d0001400046362 (by decide +kernel)

def state123_39 : List Sig := [0x3333222233332222333322223333222233332222333322223333222233332222,input 0,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_39 : Impossible true (goalAt 123) 6 state123_39.toFinset :=
  node_ok cuts123 [] 0x1c0c038181c0c058184003858181c0c1000f140c058180e06050301606038300e0c070301a18868621606068621a18870300e0c038300e06048421210823031a18868620e06068621a1882303121084a600682868621a18872620e0c072620682838300e0c072621a18868621c0c032221c0c0480a1c98872621c0c072621c988480a0c88832600e060524214908280a1c98872620e06072621c988280a14908526010c0c31300c4c0703018d88636210c0c636218d8870300c4c0313008c0c434210d08381818d88636208c0c636218d88381810d08436002c0c636218d88686206460686202c0c191806460686218d88636204c0c636218d8872620c4c0726204c0c31300c4c0726218d8863621c0c032300c8c0480a4003c480a1c0c1000f1c0c0480a0c8c032300e0601a1806860280a0c8c032300e06032300c8c0280a068601a180e0c032300c8c068620686068620e0c01a180e0c068620c8c068620440500001c18872620c8c070620440432300c8c072624000072620c4c032301858863624000863620c4c100020c4c063620c8c06362 (by decide +kernel)

def state123_40 : List Sig := [0x3333222233332222333322223333222233332222333322223333222233332222,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_40 : Impossible true (goalAt 123) 6 state123_40.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050300e0c068621a18838301210868621a1884a601a18838300e0c068621a18838300e0c068621c0c0480a1c0c0480a0e060280a0e060280a1c98831301c0c043030c4c019180c4c031300646031301a18819181a18813030c4c0213018d8870301202870301202838180a02838180a02832301202870300c8c01a180c8c032300686032301a18838301a18811030c8c0323004c0c31304000831300c8c10000 (by decide +kernel)

def state123_41 : List Sig := [0xff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa,input 3,input 0,input 4,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_41 : Impossible true (goalAt 123) 6 state123_41.toFinset :=
  node_ok cuts123 [] 0x7030160605030140c032301c0c0480a0c8c01a180c8c03230068601a0a0c8c032300440c6a621a18068621a18870301282870301206038180a82828180a06031301c0c043030c4c019180c4c031300646031300c8c00b0a0c4c00b0a0c4c03130084c06b621a98819181a9882a221a9886a621c0c04a421a9886a62129886a621e9881a0a1a98870301606070301606023030e06023030e06032300686032300686072621c988130306828636218d883130064603830 (by decide +kernel)

def state123_42 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_42 : Impossible true (goalAt 123) 6 state123_42.toFinset :=
  node_ok cuts123 [⟨state123_0,exclude123_0⟩] 0x1c0c05818140c050300c8c070301202832300686032300c8c01a180682832300c8c100050c8c0383006860323004c0c32300c8c011030c4c0703010c0c31300646031300c4c019180c4c0323080000313018d8831300e0c019180c4c013030c4c03130084c070301282870301206038180a82828180a06072621c9881a0a4000438301c0c050180e0c038180e0c0383008c0c1a0a0e0c038300a0c06a621c0c043031c0c013030e06023030e0601303 (by decide +kernel)

def state123_43 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_43 : Impossible true (goalAt 123) 7 state123_43.toFinset :=
  node_ok cuts123 [⟨state123_1,exclude123_1⟩,⟨state123_8,exclude123_8⟩,⟨state123_26,exclude123_26⟩,⟨state123_39,exclude123_39⟩,⟨state123_40,exclude123_40⟩,⟨state123_41,exclude123_41⟩,⟨state123_42,exclude123_42⟩] 0x70300e060703016061000e1606070304003c5030160603818140c058180e0c038301c0c06a621a98858181a9886a621c0c038300e0c03818129084a4208c0c6a621a98838181a9886a6208c0c4a421298900021a9886a6204c0c38300e0c200060e0c0383004c0c6a621a98a00051a9886a624000438300e0c200020e0c03830400046a621a9884a0a0c8c032301c0c100021c0c04a0a4003c480a1c0c032300c8c02a0a068601a180e06032300c8c02a0a0c8c032300e0601a18068606a620c8c06a621a1801a181a1806a620686068621a18032301a18813034000813030440432300c8c013030c8c032300440500020440d00028001200034000032300c8c100020c8c0323040001000240000703004c0c70301282900021282870304003c703012828130312828381804c0c38180a82900020a82838184003838180a82813030a82900024002c726210c0c31300c4c070304003c703010c0d000f10c0c70300c4c0313008c0c19180646038180c4c0313008c0c31300c4c0381806460191802c0c31300c4c06a62064606a6202c0c1918064606a620c4c06a624000831300c4c032304000832308000500028000032300c4c0313004c0d000204c0d000b0c4c03130400090002084c100024000863621c0c100041c0c04a0a4003c4a0a1c0c1000f1c0c04a0a400104a0a0e06100030e0602a0a400382a0a0e061000e0e0602a0a4000c2a0a (by decide +kernel)

def state123_44 : List Sig := [0xcccceeeecccceeeecccceeeecccceeeecccceeeecccceeeecccceeeecccceeee,input 0,input 4,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_44 : Impossible true (goalAt 123) 6 state123_44.toFinset :=
  node_ok cuts123 [] 0x1c0c038181c0c058184003858181c0c1000f140c058180e06050301606038300e0c070301a9886a62160606a621a98870300e0c038300e0604a421290821031a9886a620e0606a621a9882103129084a62068286a621a98872620e0c072620682838300e0c072621a9886a621c0c032221c0c04a0a1c98872621c0c072621c9884a0a0c88832620e0605242149082a0a1c98872620e06072621c9882a0a1490852621040c31300c4c0703018d8863621040c636218d8870300c4c031300840c434210d08381818d8863620840c636218d88381810d0843620240c636218d886a620646069620240c1918064606a6218d88636204c0c636218d8872620c4c0726204c0c31300c4c0726218d88636240000313018580323018d88636240000636218d8832300c4c031301282832300c8c070304003c703012829000f1202870300c8c032300a8281a180686038180c8c032300a82832300c8c03818068601a181a98832301a98868600686068601a9881a181a18868600c8c068621c98900001c98870600c8c070601c98832301c1887060400007062 (by decide +kernel)

def state123_45 : List Sig := [0xff00ffaa00000000ff00ffaa00000000ff00ffaa00000000ff00ffaa,input 3,input 0,input 4,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_45 : Impossible true (goalAt 123) 5 state123_45.toFinset :=
  node_ok cuts123 [] 0xc8c050301202832301c98870601c18870621a98868601a1886862140c072621c98832420c4c0636218d88313018580636218d88616218d8872620c4c0636218d886a620646063620e0c06a621a98838301a98872620e0c06a620e06050301606050300686032300686032300a06072620e060726210d886362064606362129886a620e0606a62 (by decide +kernel)

def state123_46 : List Sig := [0xff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaa,input 3,input 0,input 4,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_46 : Impossible true (goalAt 123) 6 state123_46.toFinset :=
  node_ok cuts123 [⟨state123_45,exclude123_45⟩] 0x7030160605030140c032301c0c0480a0c8c01a180c8c032300686072621c18070621c1883230068601a180c8c03230068601a180c8c070301c98872620c98852421c98872621498831301c0c043030c4c019180c4c031300646031300c8c00b0a0c4c073621c98831301c98831300646019180c4c0636218d8819180c4c058181c0c058181c0c0381808c0c381802c0c1a0a1c9881a0a1c9886a621606070301606070300e06200000e0610003068287262068287262 (by decide +kernel)

def state123_47 : List Sig := [0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,input 0,input 4,input 1,input 3,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_47 : Impossible true (goalAt 123) 7 state123_47.toFinset :=
  node_ok cuts123 [⟨state123_2,exclude123_2⟩,⟨state123_44,exclude123_44⟩,⟨state123_46,exclude123_46⟩] 0x70300e060703016061000e1606070304003c5030160603818140c058180e0c038301c0c06a621a98858181a9886a621c0c038300e0c03818129084a4208c0c6a621a98838181a9886a6208c0c4a42129881a0a1a9886a621c98838301c9881a0a0e0c038301c9886a621a9884a0a0c8c032301c0c100021c0c04a0a4003c480a1c0c032300c8c02a0a068601a180e06032300c8c02a0a0c8c032300e0601a18068606a620c8c06a621a1801a181a1806a620686068621a18032301a18872624000872621c18032301c18072620c8c070621c18100021c18870300c88870301282872621c98870301c98872621282832220c98838181490852420a82872621c98838181c98872620a82852421498843030c4c031301c0c1000b1c0c043034003c43031c0c031300c4c023030646019180e06031300c4c023030c4c031300e0601918064600b030c4c031301a98819181a9880b030646019181a98831301a98900020c4c031300c8c100020c8c1000b4000a00000c8c031300c4c100024000873624002c31300c4c0726240008726210c0d000410c0c70304002c703010c0d000f10c0c703040010703008c0d000308c0c38184002c381808c0d000e08c0c38184000c381802c0d000102c0c6a624002c6a6202c0e000202c0c6a62400046a624000900004000032304000832304002d00028000432304000032304002d000204c0d0002400086362 (by decide +kernel)

def state123_48 : List Sig := [0xbbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaabbbbbbaa,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_48 : Impossible true (goalAt 123) 5 state123_48.toFinset :=
  node_ok cuts123 [] 0x7030160605030140c070301c98872620c98052421c98872621498038301a9886a620e0c04a421a9886a62129806a621c98838301a98831301c0c041030c4c019180c4c031300646009081c98831301c98831301a98819181a98863620c8c0480a1c0c032300686032300c8c01a181c18870620c8c072621a18868620e0c06a62 (by decide +kernel)

def state123_49 : List Sig := [0x3333330033333300333333003333330033333300333333003333330033333300,input 3,input 4,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_49 : Impossible true (goalAt 123) 6 state123_49.toFinset :=
  node_ok cuts123 [⟨state123_9,exclude123_9⟩,⟨state123_48,exclude123_48⟩] 0x1c0c038181c0c058184003858181c0c1000f140c058180e06050301040c31300c4c0703018d8863621040c636218d8870300c4c031300840c434210d08381818d8863620840c636218d88381810d08436004c0c636218d8872620c4c0726204c0c31300c4c0726218d88636202c0c636218d886a62064606a6202c0c1918064606a6218d8863621c0c032221c0c04a0a1c98872621c0c072621c9884a0a0c88832600e0605242149082a0a1c98872620e06072621c9882a0a1490852601606038300e0c070301a9886a62160606a621a98870300e0c038300e0604a421290821031a9886a620e0606a621a9882103129084a60068286a621a98872620e0c072620682838300e0c072621a9886a621c0c032300c8c04a0a4003c480a1c0c1000f1c0c04a0a0c8c032300e0601a18068602a0a0c8c032300e06032300c8c02a0a068601a180c4c032300c4c063628000063620c4c200010c4c063620c8c063624001500001c18872620c8c070624001432300c8c072624000072620e0c032301a1886a620686068620e0c01a180e0c06a620c8c06a62 (by decide +kernel)

def state123_50 : List Sig := [0x5555550055555500555555005555550055555500555555005555550055555500,input 0,input 3,input 4,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_50 : Impossible true (goalAt 123) 6 state123_50.toFinset :=
  node_ok cuts123 [⟨state123_9,exclude123_9⟩] 0x7030160605030140c032301c0c0480a0c8c01a180c8c03230068601a0a0c8c032300440c32300e0c01a180c8c070301282870301206038180a82828180a06038301c0c050180e0c038180e0c0383002c0c1a0a0e0c038300a0c0232218d8863621c0c0434218d88636210d88616018d8863621858863621cd88130318d8863621ad880b0318d88703010c0c703010c0c381808c0c381808c0c32308000032304000072621c9881a0a04c0c6a621a988383002c0c3130 (by decide +kernel)

def state123_51 : List Sig := [0x3333330033333300333333003333330033333300333333003333330033333300,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_51 : Impossible true (goalAt 123) 6 state123_51.toFinset :=
  node_ok cuts123 [] 0x1c0c05818140c050300c4c0636218d88313010d08636218d88436018d8831300c4c0636218d88383006460636218d8831300c4c063621c0c04a0a1c0c048180e0602a0a0a06028181c98838301c0c050180e0c038180e0c038300840c1a0a0e0c028301a98870301040c70301040c38180840c38180840c32301202870300c8c01a180c8c0323006860313018d88313018d8900050c8c032300682832300686038300c8c10000 (by decide +kernel)

def state123_52 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 3,input 4,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_52 : Impossible true (goalAt 123) 7 state123_52.toFinset :=
  node_ok cuts123 [⟨state123_26,exclude123_26⟩,⟨state123_30,exclude123_30⟩,⟨state123_42,exclude123_42⟩,⟨state123_10,exclude123_10⟩,⟨state123_49,exclude123_49⟩,⟨state123_50,exclude123_50⟩,⟨state123_51,exclude123_51⟩] 0x70300e06070301606100101606070304003c5030160603818140c04a0a0c8c032301c0c100051c0c04a0a4003c480a1c0c032300c8c02a0a068601a180e06032300c8c02a0a0c8c032300e0601a18068601a0a400081a0a4001432300c8c01a0a0c8c032304001500054001500010c8c032300e0c01a180e0c10005068601a180e0c032300c8c100058001a00044000032300c8c100050c8c032304000100054000043030c4c031301c0c0636218d88430318d8863621c0c031300c4c0230310d0843420e060636218d88230318d8863620e060434210d8900051858061600c8c0636218d8a000318d8863620c8c0616018589000218d8863620682831300c4c200020c4c0313006828636218d89000118d8863620e0c019180e0c200010646019180e0c0636218d8a000518d8863624002c31300c4c200000c4c031304002c636218d8870300682870301282900021282870304003c7030128281a0a1206038180682838180a82900020a82838184004028180a8281a0a0a06100014000472621606038300e0c0703040004703016061000f1406070300e0c038300e06100100e06023030e0c038300e06038300e0c023034000423030682900020682900010e0c038304000500010a0c10001400086a621c0c100041c0c043034003c43031c0c1000f1c0c043034001043030e06100030e06023034004023030e06100100e06023034000c2303 (by decide +kernel)

def state123_53 : List Sig := roots 123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude123_53 : Impossible true (goalAt 123) 8 state123_53.toFinset :=
  node_ok cuts123 [⟨state123_11,exclude123_11⟩,⟨state123_17,exclude123_17⟩,⟨state123_31,exclude123_31⟩,⟨state123_38,exclude123_38⟩,⟨state123_43,exclude123_43⟩,⟨state123_47,exclude123_47⟩,⟨state123_52,exclude123_52⟩] 0x4000c70300e06070304000c58184000c58184000c70304001050304000c58180e06050304001070300c8887030400104a0a1c98872624001070301c9887262400104a0a0c88832624000c38181490852424000c2a0a1c98872624000c38181c98872624000c2a0a1490852624001058180e0c038304001070301a9886a624001058181a9886a624001070300e0c038304000c3818129084a424000c23031a9886a624000c38181a9886a624000c2303129084a62400081a0a1a9886a624000472620e0c07262800181a0a0e0c038304000472621a9886a62400004a0a0c8c03230400007030400007030400004a0a40010480a4000070300c8c03230400002a0a068601a184000038180c8c03230400002a0a0c8c03230400003818068601a184000072628000472624000070600c8c070604000072620c8c07062400007060400007062400006a620c8c06a62400006860068606860400006a620686068624000068600c8c068624001043030c4c0313040010703018d88636240010430318d8863624001070300c4c031304000c230310d0843424000c381818d8863624000c230318d8863624000c381810d08436240008130318d8863628001472620c4c072628001013030c4c0313040008726218d886362400040b0318d8863628000c6a62064606a62800080b03064601918400046a6218d88636240001000018580616040000323018d88636240002000018d886362400003230185806162 (by decide +kernel)

theorem lower123 : Claim 123 9 :=
  fromSearch 67 (by decide +kernel) exclude123_53

theorem lower248 : Claim 248 6 :=
  fromLift 6 16 859197440 lower232 (by decide +kernel)

theorem lower217 : Claim 217 6 :=
  fromLift 6 8 3 lower209 (by decide +kernel)

def cuts240 : Cuts (goalAt 240) := []

def state240_0 : List Sig := roots 240
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude240_0 : Impossible true (goalAt 240) 3 state240_0.toFinset :=
  node_ok cuts240 [] 0x38180b03028180a06038180e0c038300903028200e0c038300a0c01c180d0c034300706024200d0c03430090c034300e0c01c180d0c0 (by decide +kernel)

theorem lower240 : Claim 240 4 :=
  fromSearch 1148583936 (by decide +kernel) exclude240_0

theorem lower242 : Claim 242 5 :=
  fromLift 5 2 1148256320 lower240 (by decide +kernel)

theorem lower211 : Claim 211 6 :=
  fromLift 6 2 68 lower209 (by decide +kernel)

theorem lower218 : Claim 218 5 :=
  fromLift 5 64 855728192 lower154 (by decide +kernel)

def rule179_0 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower177 none (by decide +kernel)

def rule179_1 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower178 none (by decide +kernel)

def rule179_2 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower161 none (by decide +kernel)

def rule179_3 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower147 none (by decide +kernel)

def rule179_4 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower51 none (by decide +kernel)

def cuts179 : Cuts (goalAt 179) := [rule179_0,rule179_1,rule179_2,rule179_3,rule179_4]

def state179_0 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_0 : Impossible true (goalAt 179) 4 state179_0.toFinset :=
  node_ok cuts179 [] 0x28088a0822820821030c8c0a08228208123024208a0820c88890820c88890822420832220c8c0908224209000220e08a08208c88838220e0890820440c838208c88838220e0823220c4c0b030 (by decide +kernel)

def state179_1 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_1 : Impossible true (goalAt 179) 4 state179_1.toFinset :=
  node_ok cuts179 [] 0xb03028208a082240c0908228208322224208b030242089082280c0838228208232220e08838224208110320e08b13020e0883822c0c0121028208323028208322224208323024208313020e08232220e08a022 (by decide +kernel)

def state179_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_2 : Impossible true (goalAt 179) 5 state179_2.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_1,exclude179_1⟩] 0xb0300840cb03024040a28228a08b03028a08a282240402103240c0b0300c888b03028888928224a08b03024a089282288883222280c1000224a08928228a08322228a0900020c888322228a08928224a08810308c8823222c0c0838220e08810320e0883822c0c023222c0c0210320e08838228a08232228608210308c88232228a08838220e08110320e08838224a09000124608110340008110324a08838220e0900004000081802888832300c8c0b03080004b0302888a000028088b0300c8c0323028a08121028a08a0800c8c0a08028a08323028208a08004840a08224a09000224a0890800c8c0908024a083230242089080400089082 (by decide +kernel)

def state179_3 : List Sig := [0x5555555555555555555555555555555544444444444444444444444444444444,input 0,input 7,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_3 : Impossible true (goalAt 179) 4 state179_3.toFinset :=
  node_ok cuts179 [] 0xa02228208a0820840c90822820832222420832222420890820c88811102820831302820821202420831302420831302c4c081030c4c0a0820c8c0a082048c090820c8c090820440c32302c0c0a0220c8c08382 (by decide +kernel)

def state179_4 : List Sig := [0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,input 7,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_4 : Impossible true (goalAt 179) 5 state179_4.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_3,exclude179_3⟩] 0xa02208c0ca0222040ca08228208a02228208a0822040c230308c0c323008404323004840a08228208323028208a082048402101048c100022420890822820832222820900020c88832222820890822420900020c88832222808890822420900022420890822808832220c88832300440432304000890822420832302420890824000811010440c230320e0883822820831302820823030c4c0313028208838220e08130320e0883822420831302420813030c4c0313024208838220e0881030c4c0313028088838220e08810320e0883822808831300c4c200010c4c031300c8c0838220e0a000020e0883820c8c031300c4c1000040000b030 (by decide +kernel)

def state179_5 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 0,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_5 : Impossible true (goalAt 179) 4 state179_5.toFinset :=
  node_ok cuts179 [] 0x2c0c0928224a08a03024a0890802420890820c8c0b03028088323020e0892820c4c0838220600838220e0881820c4c0838220e08313024a08322224a08a28228208a08228a08a080240c0a28228a08b03020e08313020e08a282 (by decide +kernel)

def state179_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_6 : Impossible true (goalAt 179) 5 state179_6.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_5,exclude179_5⟩] 0x230328a08a28208c0e000128a08a2824000c928228a08322224a08322224a0892820c888322224a0892820c888a28228200a0822820892822420090822420832302040481030c8c032304000200000c8c0b03020e08a28208c0c838220e08928204c0c838220600838220e08818220c0c8382400043130 (by decide +kernel)

def state179_7 : List Sig := roots 179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_7 : Impossible true (goalAt 179) 6 state179_7.toFinset :=
  node_ok cuts179 [⟨state179_2,exclude179_2⟩,⟨state179_4,exclude179_4⟩,⟨state179_6,exclude179_6⟩] 0x4000cb03008c0cb0304000c901028a08a2824000cb03028a08a2824000c901008c0c903040008b0300c888b03040008a22224a08928240008b03024a08928240008a2220c888a0304000d000324a0892824000ca2820c888a2824000d00020c88832224000ca28224a08928240000a2220c8c0323040000b03040000b03040000a22280004a02240000b0300c8c0323040000a28204840a28240000a0800c8c0a08040000a2820c8c0a08240000a08004840a0824000092824000892824000090800c8c090804000092820c8c090824000090804000090824001083030c4c0313040004b03020e08838280008830320e08838240004b0300c4c031304000c230320e0883824000ca2820c4c0a2824000c23030c4c031304000ca28220e08838240008130320e0883824000492820c4c092824000813030c4c0313040004928220e08838240001000020600818040000323020e08838240002000020e088382400003230206008182 (by decide +kernel)

theorem lower179 : Claim 179 7 :=
  fromSearch 68 (by decide +kernel) exclude179_7

def rule251_0 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower249 none (by decide +kernel)

def rule251_1 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower243 none (by decide +kernel)

def rule251_2 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 none (by decide +kernel)

def rule251_3 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower233 none (by decide +kernel)

def rule251_4 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower219 none (by decide +kernel)

def rule251_5 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower187 none (by decide +kernel)

def rule251_6 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower123 none (by decide +kernel)

def rule251_7 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower241 none (by decide +kernel)

def rule251_8 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower248 none (by decide +kernel)

def rule251_9 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower219 (some (1,input 0,input 1)) (by decide +kernel)

def rule251_10 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower185 none (by decide +kernel)

def rule251_11 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower121 none (by decide +kernel)

def rule251_12 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower123 (some (1,input 0,input 1)) (by decide +kernel)

def rule251_13 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower232 none (by decide +kernel)

def rule251_14 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower217 none (by decide +kernel)

def rule251_15 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower240 none (by decide +kernel)

def rule251_16 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower184 none (by decide +kernel)

def rule251_17 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower225 none (by decide +kernel)

def rule251_18 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower209 none (by decide +kernel)

def rule251_19 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower113 none (by decide +kernel)

def rule251_20 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower91 (some (1,input 0,input 1)) (by decide +kernel)

def rule251_21 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower201 none (by decide +kernel)

def rule251_22 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower145 none (by decide +kernel)

def rule251_23 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower81 none (by decide +kernel)

def rule251_24 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower250 (some (1,input 3,input 5)) (by decide +kernel)

def rule251_25 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower233 (some (1,input 3,input 5)) (by decide +kernel)

def rule251_26 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower242 none (by decide +kernel)

def rule251_27 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower233 (some (1,input 0,input 3)) (by decide +kernel)

def rule251_28 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower211 none (by decide +kernel)

def rule251_29 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower186 none (by decide +kernel)

def rule251_30 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower115 none (by decide +kernel)

def rule251_31 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower123 (some (1,input 0,input 3)) (by decide +kernel)

def rule251_32 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower83 none (by decide +kernel)

def rule251_33 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower147 none (by decide +kernel)

def rule251_34 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower218 none (by decide +kernel)

def rule251_35 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower179 none (by decide +kernel)

def rule251_36 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower91 none (by decide +kernel)

def rule251_37 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower249 (some (1,input 0,input 5)) (by decide +kernel)

def rule251_38 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower233 (some (1,input 0,input 5)) (by decide +kernel)

def rule251_39 : {c : Cut // CutGood (goalAt 251) c} :=
  ruleFor 251 lower155 none (by decide +kernel)

def cuts251 : Cuts (goalAt 251) := [rule251_0,rule251_1,rule251_2,rule251_3,rule251_4,rule251_5,rule251_6,rule251_7,rule251_8,rule251_9,rule251_10,rule251_11,rule251_12,rule251_13,rule251_14,rule251_15,rule251_16,rule251_17,rule251_18,rule251_19,rule251_20,rule251_21,rule251_22,rule251_23,rule251_24,rule251_25,rule251_26,rule251_27,rule251_28,rule251_29,rule251_30,rule251_31,rule251_32,rule251_33,rule251_34,rule251_35,rule251_36,rule251_37,rule251_38,rule251_39]

def state251_0 : List Sig := [0xffffffffffeeffeeffffffffffeeffeeffffffffffeeffeeffffffffffeeffee,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_0 : Impossible true (goalAt 251) 7 state251_0.toFinset :=
  node_ok cuts251 [] 0xe2622c0c0a26228988726234b08d2c21c988928234b08d2c224b08d2c238b08726234b08d0c034b08d2c234300636230f08c3c218d88838230f08c3c220f08c3c234708110330f08c3c2327080b0a30f08616030f08e1c218d88c3c2400486a6232b08cac21a9888a8232b08cac222b08cac234b08383032b08cac238b086a6232b08c8c038988e06038188e0620c8c0703012028323034b08d0c034b08d0c032b08686032308c8c238b08323038308e0c204840e26238b08e2c20e060a28238b08e2c228b08e0c03898890103898890101c0c050101c0c05010 (by decide +kernel)

def state251_1 : List Sig := [0xffffffff00000000ffffffff00000000ffeeffee00000000ffeeffee,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 0,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_1 : Impossible true (goalAt 251) 6 state251_1.toFinset :=
  node_ok cuts251 [] 0xe2622c0c0a26228988928234b08d2c224b08726234b08d2c21c988838230f08c3c220f08c3c234708110330f08c3c2327080b0a30f08c1c018d88c3c230f08636222a08cac232b088ac232b08d2c20e0c0cac21a988cac232b086a620c8c0503012028323034b08d0c034308d0c232b08c8c032308c8c238988e06038188e06228b08e2c238b08a28234b08726234b08e2c230f08636230f08e1c232b086a6232b08e2c238308e0c238b08e0c0240c0e2c238b08e262 (by decide +kernel)

def state251_2 : List Sig := [0xffffffffffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffee,input 7,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_2 : Impossible true (goalAt 251) 7 state251_2.toFinset :=
  node_ok cuts251 [⟨state251_1,exclude251_1⟩] 0xe26228888a2622898870301606058181c0c0a28238b08e2c228b08e26238b08e2c20e062000038b08e2c240038928234b08d2c224b08d2c238b08726234b08726234b08d2c21c988706034b08d2c21c180838230f08c3c220f08c3c238708636230f08c3c234708110330f08c3c2327080b0a30f08c1c018d88c3c230f0863624004c8a8232b08cac222b08cac238b086a6232b08cac234b08120a32b086a6232b08cac21a988686006860703012028703038b08e0c038308e0c234b08d0c034308d0c232b08c8c032308c8c238988981838188e0620c8c0e060 (by decide +kernel)

def state251_3 : List Sig := [0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee,input 5,0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,input 3,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_3 : Impossible true (goalAt 251) 7 state251_3.toFinset :=
  node_ok cuts251 [] 0x38988b03028988a2621c988d2c234b08726224a08d2c234b0892c234b08e2c21c988d2c234300d2c234b08d0c018d88c3c230f08636220e08c3c230f0883c230f08d1c20440cc3c230f08c9c202c28c3c218580c3c238708636230f0819181a188cac232b08686222a08cac232b088ac232b08d2c204828cac232300cac238b08686232b081a1832b08c8c232308e26238180e0623818832301c0c058180c8c0d2c234300d2c234300e2c20c8c0e0c2383081a180c8c032304001ce26238b08e2c226060a28238b08e2c228b08e0c0389889818389881a181c0c058181c0c01a18 (by decide +kernel)

def state251_4 : List Sig := [0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 7,0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,input 3,input 0,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_4 : Impossible true (goalAt 251) 7 state251_4.toFinset :=
  node_ok cuts251 [] 0x38988a22228988a2621c0c01a1812028703028a08e2c238b08a2c238988e2c238b0838180e060e2c238b081a1824a08d2c234b0892c234b08e2c21c988d2c21c988d2c234b0872621c180d2c234b08706020e08c3c230f0883c230f08e1c218d88c3c230f08d1c20440cc3c230f08c8c202c28c3c230700636230f08c3c218d88191822208c8c2323088ac232308e2c21a988c8c232308d2c204828c8c2323006a6232308c8c21a9881a1832308c8c21a18858181c0c058181c0c0e2c238300e0c238308d2c234300d0c234308e2624003ce0623818832300c8c01a184002ce060 (by decide +kernel)

def state251_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 0,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_5 : Impossible true (goalAt 251) 7 state251_5.toFinset :=
  node_ok cuts251 [] 0x28988e2c238b0838181c0c0e2c238b08503034b08e2c21c988d2c21c988d2c234b0872621c0c0d2c234b08326230f08e1c218d88c3c230f08d1c20440cc3c230f08c9c202c28c3c206461001318d88c3c230f08636208c88c3c230f08703032b08e2c21a988cac232b08d2c204828cac2323006a6232b08cac21a9882a2232b08cac21c0c0e2c238300e2c238300d2c234300d2c234300cac206860c8c20c8c0a26228180a262281801a181c0c0480a1c0c0e2c238300e2c238300d2c234300d2c234300a26228180a2622818058181c0c058181c0c0b030 (by decide +kernel)

def state251_6 : List Sig := [0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 3,input 0,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_6 : Impossible true (goalAt 251) 8 state251_6.toFinset :=
  node_ok cuts251 [⟨state251_0,exclude251_0⟩,⟨state251_2,exclude251_2⟩,⟨state251_3,exclude251_3⟩,⟨state251_4,exclude251_4⟩,⟨state251_5,exclude251_5⟩] 0xe2621c0c0e2622c0c100102c0c0e26280010a2622c0c0703028988e2620e060e26226060e2c238b08e26238b08e2c2260603818240c0703028a08a28216060e2c238b08703038b08e2c216060a28228b08b0301c988726238988d2c234b08b03034b08d2c23898872621c988703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c238b08726238b0838181c988726238b08d2c234b08810318d88636238988c3c230f08810330f08c3c238988636218d88410320e0883821c0c0c3c230f08410330f08c3c21c0c0838220f08210330f08c3c238b08636238708210318d88636238b08c3c230f08110330f08c3c234b09000834708110340034110334b08c3c230f08090330f08c3c232b080b0a32708090302c280b0a32b08c3c230f0900074001c19184001d00074001c98181a9886a6238988cac232b08981832b08cac2389886a621a988581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b08381832b08cac238b086a6238b0838181a9886a6238b08cac232b081a0a32b08cac234b09000734b081a0a40034120a34b08cac232b09000740020c8c0389881a1838988e06040020e0603898a000338988e06006860e060128281a1806860703040020703012829001012028703006860703038b081a1838b08e0c040020e0c038b0a000238b08e0c006860e0c034b09001134b08d0c006860d0c034b081a1834b08d0c040020d0c032b09000732b090008068601a184001d00073230900074001c323038989000b38988e0604003ce0603898a000138988e0604002ce06016061000a16060703040040703016061001016060703040028703038b09000e38b08e0c04003ce0c038b0a000038b08e0c040038e0c034b09000334b08d0c040034d0c034b09000d34b08d0c04000cd0c0 (by decide +kernel)

def state251_7 : List Sig := [0xff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00ee00ff00ff00ee00ee,input 3,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_7 : Impossible true (goalAt 251) 7 state251_7.toFinset :=
  node_ok cuts251 [] 0x38988b03028988a2621c988d2c234b08726224a08d2c234b0892c234b08e2c21c988d2c218d88c3c230f08636220e08c3c230f0883c230f08d1c20440cc3c230f08e1c218d88c3c218580c3c2323000b0a30f08e26238b08e2c20e060a28238b08e2c228b08e26238180e0623818832301c0c0480a0c8c0d2c234300d2c234300e2c20c8c0e0c238308cac0323001a1832300484032300c8c038988888032300c8c022300c8c034b081a0a34b08c8c038b08381838b08e26226060e26226060703016060703016060d2c234300d2c234300c3c202c28c3c202c28e2c238300e2c20e060323006860323006860cac2 (by decide +kernel)

def state251_8 : List Sig := [0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 5,input 0,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_8 : Impossible true (goalAt 251) 8 state251_8.toFinset :=
  node_ok cuts251 [⟨state251_3,exclude251_3⟩,⟨state251_0,exclude251_0⟩,⟨state251_7,exclude251_7⟩] 0xe2621c0c0e2622c0c100102c0c0e26240050a2622c0c0703028988b0301c988726238988d2c234b08b03034b08d2c23898872621c988703024a08928212828d2c234b08703034b08d2c212828928224b09000d34b08d2c238b08726238b09000d1c988726238b08d2c234b09000d34300d0c04000cd2c234b09000d34b08d2c24000cd0c03430098181a9886a6238988cac232b08981832b08cac2389886a621a988581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b081a0a32b08cac234b08383034b081a0a0e0c0383034b08cac232b082a0a32b08cac238b086a6238b082a0a1a9886a6238b08cac232b0a000232300c8c04001ccac232b0a000132b08cac24001cc8c032300810318d88636238988c3c230f08810330f08c3c238988636218d88410320e0883821c0c0c3c230f08410330f08c3c21c0c0838220f08110330f08c3c234b09000834708110340034110334b08c3c230f08090330f08c3c232b080b0a32708090302c280b0a32b08c3c230f08210330f08c3c238b08636238708210318d88636238b08c3c230f09000e40038616040039000e40038e2620a828e26226060e2c238b08e26238b08e2c2260602a0a26060703028a08a28216060e2c238b08703038b08e2c216060a28228b09000840020e0c038988323038988e06040020e06038989001438188e0600c8c0e0621282832300c8c070304002070301282900101282870300c8c0323034b09001534b08d0c00c8c0d0c034b08323034b08d0c040020d0c032b08323032b08c8c040020c8c032b0a000032b08c8c00c8c0c8c038b09000e38b0900080c8c0323040021000e38309000e400381a1838989000b3898898184005098183898900143898898184002c98181c0c1000a1c0c058184004058181c0c100101c0c05818400285818 (by decide +kernel)

def state251_9 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_9 : Impossible true (goalAt 251) 8 state251_9.toFinset :=
  node_ok cuts251 [⟨state251_0,exclude251_0⟩] 0x38988703038988b0304005cb03038989001728988b0301c0c0a2622c0c072621c988e26234b08d2c22c0c0d2c234b08e2621c98872621c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c20e060d2c234b082a0a1c98872620e06072621c9882a0a34b08d2c240048d2c234b0900031c98872624006472621c989000334b08d2c22040c636218d88e26230f08c3c22040cc3c230f08e26218d8863621040c838220e08703030f08c3c21040cc3c230f08703020e0883c20440cc3c230f08d2c240064d1c20440d00190440cd2c230f08c3c24001d000730701001230f08c3c20e060636218d89001818d8863620e060c3c230f09000730f08c3c21a9880b0a1a589001802c280b0a1a988c3c230f09001230f08c3c240008636218d89001818d88636240008c3c230f08e2620c8c0e26238181001738180e2624005ce062381803230381884a0a0c8c032301c0c100161c0c04a0a40058480a1c0c032300c8c0d2c240054d2c234300323034300d2c20c8c0d0c2343010015343082a0a068601a180e06032300c8c02a0a0c8c032300e0601a18068606a620c8c06a621a1801a181a1806a620686068621a18032301a18900120484012104002032300c8c200000c8c0323040020121004840e2620e060e26226061001226060e2624005ce2622606038180e06070300e06070301606100121606070304005870301606038180e06100074001ce2c2260606a621a988e2624001ce26226061001726060e2621a9886a621606038300e0c070301a9886a62160606a621a98870300e0c03830068286a621a988d2c20e0c0d2c20682838300e0c0d2c21a988d2c20e061000e0e06100071a9886a624001d000712989000740038cac238989000b3898890104004890103898900173898890104002c90101c0c1000a1c0c050104004850101c0c100161c0c05010400285010 (by decide +kernel)

def state251_10 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 0,input 3,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_10 : Impossible true (goalAt 251) 9 state251_10.toFinset :=
  node_ok cuts251 [⟨state251_6,exclude251_6⟩,⟨state251_8,exclude251_8⟩,⟨state251_9,exclude251_9⟩] 0x40028e2621c0c0e26240028b03040028b03040028e26240030a26240028b0301c0c0a2624002ce2620e060e26240030981838b08e2c240030e26238b08e2c24002c98180e060903040028703028a08a28240028581838b08e2c240028703038b08e2c240028581828a08a2c24000cb0301c98872624000ce26234b08d2c24000cb03034b08d2c24000ce2621c98872624000c703024a0892824000c4a0a34b08d2c24000c703034b08d2c24000c4a0a24a0892c24000c381834b08d2c24000ce2c21c988e2c24000c38181c98872624000ce2c234b08d2c24002c98181a9886a624001ce26232b08cac240030981832b08cac24002ce2621a9886a6240028581822a088a8240028703032b08cac240028581832b08cac240028703022a088ac240024381832b08cac24001ce2c21a988e2c28000838181a9886a624001ce2c232b08cac24000c1a0a32b08cac24000cd2c20e0c0d2c24000c1a0a0e0c038304000cd2c232b08cac240008810318d88636240008e26230f08c3c240008810330f08c3c240008e26218d88636240008410320e08838240008703030f08c3c240008410330f08c3c240008703020e0883c240008210330f08c3c240008e2c218d88e1c240008210318d88636240008e2c230f08c3c24000c110330f08c3c24000cd2c24000cd1c24000c11034000c11034000cd2c230f08c3c240008090330f08c3c240008cac202c28c9c240008090302c280b0a40008cac230f08c3c240001000040000c1c04002ce2620c8c0e26240020e06040030e06040030e26240030e0624002ce0600c8c0e062400284a0a0c8c03230400287030400287030400284a0a40028480a4002870300c8c0323040024e2c206860e2c240020e0c00c8c0e0c080004e2c20c8c0e0c240020e0c006860e0c24000cd2c24000cd2c24000cd0c00c8c0d0c04000cd2c20c8c0d0c24000cd0c04000cd0c24001ccac20c8c0cac240020c8c006860c8c080000cac206860c8c24001cc8c00c8c0c8c2 (by decide +kernel)

def state251_11 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa,input 5,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_11 : Impossible true (goalAt 251) 7 state251_11.toFinset :=
  node_ok cuts251 [] 0x38188b03028188a0621a188e0622606068620e0c068621a18838300e06068621a1884a6032308686234b08383034b08636238188810318d88313018d8863620c4c063621a188191818d88191818d88636210d80c3c218d88d2c20c4c0d2c23818898183818838181c0c058181c0c0381838308e06224040e06224040703014040703014040726234b08d2c21c988928234b08d2c224b00d2c21c988726234b08d2c21c988726234b08323038188b0303818832301202870300c8c032301a18838301a188313018d88313018d881a180c8c032300686012100c8c0323004840d0c2 (by decide +kernel)

def state251_12 : List Sig := [0xffffffffffffffaa0000000000000000ffffffffffffffaa,input 4,input 5,input 0,input 3,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_12 : Impossible true (goalAt 251) 6 state251_12.toFinset :=
  node_ok cuts251 [] 0x38988e06038188e06232b08c8c032308c8c238b08e0c038308e0c234b08d0c034308d0c21a988cac232b086a6232b08e2c21a988cac232b08d2c20e0c0cac218d88c3c230f08636230700c3c230f08c1c230f08cac206460c3c230f08e2c218d88c3c230f08d2c20c4c0c3c238988e2c238b0890301c988d2c234b08726234b08e2c21c988d2c228988a2622c0c0e2620c8c0480a0c8c0703022b08cac20e0c0cac220f08c3c20c4c0c3c228b08e2c21c0c0e2c224b08d2c21c0c0d2c2 (by decide +kernel)

def state251_13 : List Sig := [0xffffffffffffffaaffffffffffffffaa,input 4,input 5,input 0,input 3,input 1,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_13 : Impossible true (goalAt 251) 6 state251_13.toFinset :=
  node_ok cuts251 [] 0xc8c0703012028323032b08c8c032308c8c238b08e0c038308e0c234b08d0c034308d0c222a08cac232b088ac232b08e2c21a988cac232b08d2c20e0c0cac220e08c3c230f0883c230700c3c230f08c1c230f08cac206460c3c230f08e2c218d88c3c230f08d2c20c4c0c3c228a08e2c238b08a2c224a08d2c234b0892c234b08e2c21c988d2c228988a26238988b03038188e06238988e0601a988cac21a988cac218d88c3c218d88c3c2240c0e2c238988e2c21c988d2c21c988d2c2 (by decide +kernel)

def state251_14 : List Sig := [0x3333333333333322333333333333332233333333333333223333333333333322,input 4,input 5,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_14 : Impossible true (goalAt 251) 6 state251_14.toFinset :=
  node_ok cuts251 [] 0x38988b03028988a2621a988cac232b086a6222a08cac232b088ac032b08e2c21a988cac232b08d2c20e0c0cac218d88c3c230f08636220e08c3c230f0883c030f08cac206460c3c230f08e2c218d88c3c230f08d2c20c4c0c3c238988e2c238b08903028a08e2c238b08a2c01c988d2c234b08726224a08d2c234b0892c034b08e2c21c988d2c238188e06238180e2620c8c0480a1c0c0323032308c8c21a180cac230708c3c218580c3c238308e0c20c8c0e2c234308d0c21c180d2c2 (by decide +kernel)

def state251_15 : List Sig := [0xffffffffffffffaaffffffffffffffaaffffffffffffffaaffffffffffffffaa,input 4,input 5,input 0,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_15 : Impossible true (goalAt 251) 7 state251_15.toFinset :=
  node_ok cuts251 [⟨state251_12,exclude251_12⟩,⟨state251_13,exclude251_13⟩,⟨state251_14,exclude251_14⟩] 0x38988b03028988a26238988e06038188e0620c8c070301202832301a98868601a18868620686032300c8c01a181c98870601c18870628000832300c8c100001a988e262240606a620e0c06a621a98838300e0606a621a9884a621a98872620e0c06a6232b08636238988830318d88313018d8863620c4c0616018d8863621858863621a988191818d88191818d88636210d8863621c988313018d88c3c23898898183898890301c0c05818140c0503038b08726238988a0301c98870301c98872620c98838181c988726214988d2c23898a00013898900061c0c200001c0c10005 (by decide +kernel)

def state251_16 : List Sig := [0xccccffffccccffeeccccffffccccffeeccccffffccccffeeccccffffccccffee,input 4,input 5,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_16 : Impossible true (goalAt 251) 6 state251_16.toFinset :=
  node_ok cuts251 [] 0x38188b03028188a0621a188c8c232308686222208c8c2323088ac232308e0c21a188c8c232308d2c20e0c0c8c218d88c3c230f08636220e08c3c230f0883c230f08c8c206460c3c230f08e0c218d88c3c230f08d2c20c4c0c3c230700c3c230f08313038188e0c238308903028208e0c238308a2c21c988d2c234b08726224a08d2c234b0892c234b08e0c21c988d2c238188b0303818832300c8c0703012028323032308c8c032308323038308e0c0383081a1834b08d0c034308d0c2 (by decide +kernel)

def state251_17 : List Sig := [0xffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa0000ffff0000ffaa,input 4,input 5,input 0,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_17 : Impossible true (goalAt 251) 7 state251_17.toFinset :=
  node_ok cuts251 [⟨state251_16,exclude251_16⟩] 0xe2622c0c0a26228988e26238180e0623818832301c0c0480a0c8c06a621a18068621a1881a180c8c0323006860d2c234300d0c2343086a623898890181a98838301a9886a620e0c038181a9886a6212988dac234b08383034b08636238988830318d88313018d8863620c4c0616018d8863621858863621a988191818d88191818d88636210d88d3c234b08313034b08e26226060e262240c07030160605030140c0524234b08d2c238988928234b08d2c224b08d2c23cb08381834b08e2622c0c0e2622c0c04a0a1c0c04a0a1c0c100000c8c200000c8c0cac232b086a620e0c0c3c230f0863620c4c0e2c238b082a0a0e0607262 (by decide +kernel)

def state251_18 : List Sig := [0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa,input 5,input 0,input 3,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_18 : Impossible true (goalAt 251) 8 state251_18.toFinset :=
  node_ok cuts251 [⟨state251_11,exclude251_11⟩,⟨state251_15,exclude251_15⟩,⟨state251_17,exclude251_17⟩] 0xe2621c0c0e2622c0c100202c0c0e26240080a2622c0c0703028988b0301c988726238988d2c234b08b03034b08d2c23898872621c988703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c20a82872621c98838181c98872620a828d2c234b0a000234b08d2c24000c72621c98a00011c98872624000cd2c234b08e2620c8c0e26238181002038180e26240080e062381803230381884a0a0c8c032301c0c100211c0c04a0a40084480a1c0c032300c8c0d2c280000d2c234300323034300d2c20c8c0d0c2343010012343086a620c8c06a621a1801a181a1806a620686068621a18032301a1882a0a068601a180e06032300c8c02a0a0c8c032300e0601a180686100120484012104000032300c8c100120c8c032304000012100484098181a9886a6238989001c389889818400809818389886a621a98858180e0c038301c0c06a621a98858181a9886a621c0c038300e0c01a0a1a9886a6234b08383034b081a0a0e0c0383034b086a6234b08381802c0c381808c0c6a621a98838181a9886a6208c0c0b0312989001c40088cac220c0c636218d88e26240080e26220c0d002020c0ce26218d88636210c0c31300c4c0703018d88636210c0c636218d8870300c4c0313004c0c636218d88d2c20c4c0d2c204c0c31300c4c0d2c218d88d2c240048616018580323018d88636240060636218d88323018580616202c0c636218d886a62064606a6202c0c1918064606a6218d88636208c0c191806460381818d88636208c0c636218d88381806460436240071001c30f08e2620e060e26226061001c26060e26240080e2622606038180e06070300e060703016061001c1606070304008470301606038180e061001c40068e2c23898900063898890104008090103898900203898890104001890101c0c100051c0c050104008450101c0c100211c0c05010400145010 (by decide +kernel)

def state251_19 : List Sig := [0xffff0000ffffffaa0000000000000000ffff0000ffffffaa,input 4,input 5,input 0,input 3,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_19 : Impossible true (goalAt 251) 6 state251_19.toFinset :=
  node_ok cuts251 [] 0x28988a06028188a06232b08c8c032308c8c238b08e0c038308e0c234b08d0c034308d0c21a988cac232b086a6232b08e2c21a988cac232b08d2c20e0c0cac218d88c3c230f08636230700c3c230f08c1c230f08cac206460c3c230f08e2c218d88c3c230f08d2c20c4c0c3c228988e2c238b0890301c988d2c234b08726234b08e2c21c988d2c21c0c0a2622c0c0a2620c8c0480a0c8c0703022b08cac20e0c0cac220f08c3c20c4c0c3c2140c0e2c21c0c0e2c224b08d2c21c0c0d2c2 (by decide +kernel)

def state251_20 : List Sig := [0x3333000033333322333300003333332233330000333333223333000033333322,input 4,input 5,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_20 : Impossible true (goalAt 251) 6 state251_20.toFinset :=
  node_ok cuts251 [] 0x38188b03028188a0621a188cac232b08686222a08cac232b088ac032b08e0c21a188cac232b08d2c20e0c0cac218d88c3c230f08636220e08c3c230f0883c030f08cac206460c3c230f08e0c218d88c3c230f08d2c20c4c0c3c238188e0c238308903028208e0c238308a2c01c988d2c234b08726224a08d2c234b0892c034b08e0c21c988d2c20c8c0e0622c0c0e0620c8c0480a1c0c0323032308c8c20e0c0cac230708c3c20c4c0c3c206860e0c20c8c0e0c234308d0c20c8c0d2c2 (by decide +kernel)

def state251_21 : List Sig := [0xffff0000ffffffaaffff0000ffffffaaffff0000ffffffaaffff0000ffffffaa,input 4,input 5,input 0,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_21 : Impossible true (goalAt 251) 7 state251_21.toFinset :=
  node_ok cuts251 [⟨state251_19,exclude251_19⟩,⟨state251_20,exclude251_20⟩] 0xe2622c0c0a26228988e26238180e0623818832301c0c0480a0c8c06a621a18068621a188e2c238300e0c2383081a0a0c8c032300440e00010c8c03230400006a623898890181a98838301a9886a620e0c0eac238b086a6238b086a620e0c038301a988cac232b0838301a988636238988830318d88313018d8863620c4c0616018d8863621858863621a988191818d88e3c238b08636238b0863620c4c0313018d88c3c230f08313018d88e26238b08e2c2240c0a28238b08e2c228b08b03038988b03038988703012828703012060381838b08381838b08d2c22c0c0e2622c0c0e2621c0c200001c0c100050e060e2c20e060e2c2 (by decide +kernel)

def state251_22 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 5,input 0,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_22 : Impossible true (goalAt 251) 7 state251_22.toFinset :=
  node_ok cuts251 [] 0x38188b03028188a0621a188e0622606068620e0c068621a18838303a308e0c21a188e0c21a188d2c20e0c0d2c218d88e0622040c63620c4c0636218d88313018d88686206460636238708e0c218d88e0c218d88d2c20c4c0d2c238188e0c238308903028208e0c238308a2c026060e06226060e06216060703016060703032308c8c20240c686230f08c3c20646063620e0601a0a34b081a0a34b081a180c8c01a180c8c0726234b08d2c21c988928234b08d2c224b00d2c238308726234b08323038188b0303818832301202870300c8c032301a18838301a188313018d88313018d881a1838308323038308d0c2 (by decide +kernel)

def state251_23 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 0,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_23 : Impossible true (goalAt 251) 7 state251_23.toFinset :=
  node_ok cuts251 [] 0xe262240c0a26228988e26238180e062381883230140c0480a0c8c06a621a18068621a18872621c18070621c188e2c238300e0c2383086a623898898181a98838301a9886a620e0c06a621c98838301a988eac238b086a6238b08636238988830318d88313018d8863620c4c0616018d8863621858863621a988191818d8863621c988313018d88e3c238b08636238b083818389889818389883818140c05818140c01a180c8c01a180c8c0cac232b0838181a988c3c230f08191818d8828181c98838181c989000338b08381838b0872623498890301c98850301c98872620c988d2c238988e2c238b088a0a28a08e2c238b08a2c2 (by decide +kernel)

def state251_24 : List Sig := [0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa,input 5,input 0,input 3,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_24 : Impossible true (goalAt 251) 8 state251_24.toFinset :=
  node_ok cuts251 [⟨state251_21,exclude251_21⟩,⟨state251_22,exclude251_22⟩,⟨state251_23,exclude251_23⟩] 0xe2621c0c0e2622c0c100202c0c0e26240080a2622c0c0703028988b0301c988726238988d2c234b08b03034b08d2c23898872621c988703024a08928212828d2c234b08703034b08d2c212828928224b09001c34b08d2c238b08726238b0a00021c988726238b08d2c234b08e2620c8c0e26238181002038180e26240080e062381803230381884a0a0c8c032301c0c100211c0c04a0a40084480a1c0c032300c8c0d2c280004d2c234300323034300d2c20c8c0d0c2343010012343086a620c8c06a621a1801a181a1806a620686068621a18032301a188e2c206860e2c238300323038300e2c20c8c0e0c2383001a183830898181a9886a6238989001c389889818400809818389886a621a98858180e0c038301c0c06a621a98858181a9886a621c0c038300e0c01a0a1a9886a6234b08383034b081a0a0e0c0383034b086a6234b09001c02c0ceac238b086a6238b09001c1a9886a6238b080b0338b08830318d88636238989001a38988830340080830338988636218d8843030c4c031301c0c0636218d88430318d8863621c0c031300c4c0130318d88636234b08313034b0813030c4c0313034b08636234b09001a1858061600c8c0636218d89001a18d8863620c8c06160185880b0318d8863621a98819181a9880b030646019181a988636218d89001c06460e3c238b08636238b09001a18d88636238b08191838b08e26240080e26226060e2c238b08e26238b08e2c226061001c240c0703028a08a28216060e2c238b08703038b08e2c216060a28228b08981840018981838989001a3898898184008098183898900063898858184001458181c0c1001a1c0c058184008458181c0c100051c0c01a0a4000c1a0a34b09001a34b081a0a800001a0a34b09000334b081a18400001a180c8c1001a0c8c01a18400481a180c8c100000c8c00b0340004cac21a989000232b080b03400080b031a98900011a988191840008c3c218d89000130f08191840004191818d89000218d89001a400703818 (by decide +kernel)

def state251_25 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_25 : Impossible true (goalAt 251) 6 state251_25.toFinset :=
  node_ok cuts251 [] 0xe0622c0c0a06228188636232588981818d88313018d8863620c4c0c3c230f08636212980c8c232308636210d80636234b08313034b08e06226060e06206460703016060703006460e0c238308191804460e06224040e06224040703014040703014040726234b08d2c21c988928234b08d2c224b00d2c21c988726234b08d2c21c988726234b08323038188b0303818832301202870300c8c0313018d88313018d8819180c8c032300686012100c8c0323004840d0c2 (by decide +kernel)

def state251_26 : List Sig := [0xffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_26 : Impossible true (goalAt 251) 6 state251_26.toFinset :=
  node_ok cuts251 [] 0xe2622c0c0a26228988e26238180e0623818832301c0c0480a0c8c063621858063621a1881a180c8c032300646072621c18070621c1880b030c8c032300240c636232d88901818d88313018d8863620c4c0c3c230f0863621298863621c988313018d88cac232b08636210d88e26224460e262240c07030144605030140c0e2c238b08191840008726238988a0301c98870301c98872620c98819181c988726214988d2c2389888303389880b031c0c043031c0c00b03 (by decide +kernel)

def state251_27 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_27 : Impossible true (goalAt 251) 7 state251_27.toFinset :=
  node_ok cuts251 [⟨state251_25,exclude251_25⟩,⟨state251_26,exclude251_26⟩] 0x38988703038988b03040080b03038989002028988b0301c0c0a2622c0c072621c988e26234b08d2c22c0c0d2c234b08e2621c98872621c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c206460d2c234b080b0a1c98872620646072621c9880b0a34b08d2c240070d2c234b080b031c98872628000472621c9880b0334b08d2c238988323038988e06040080e06038989002038188e0600c8c0e0621282832300c8c070304008470301282900211202870300c8c0323034b0a000034b08d0c00c8c0d0c034b08323034308d0c040048d0c218d88323018d88616006860616018d881a1818d8861600c8c0686202c281a180686019180c8c0323002c2832300c8c0191806860191802c0c12100484009010c8c0323002c0c32300c8c0090104840121026060636218d88e26240080cb6226061002026060e26218d8863621606031300c4c0703018d88636216060636218d8870300c4c0313006828636218d88d2c20c4c0d2c20682831300c4c0d2c218d88d2c206461000430f09000118d88c3c206460636218d890001400104a6202c0d000432b09000218d88cac202c0c636218d8900024001043623898819183898898184008098183898900203898898180646019181c0c019181c0c058184008458181c0c100211c0c0581806460191802c0d000138b09000206460e2c202c0c1918064610002400041118389880b0338988901040070901038989002038988901002c0c90101c0c00b031c0c050104007050101c0c100211c0c0501002c0c5010 (by decide +kernel)

def state251_28 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_28 : Impossible true (goalAt 251) 6 state251_28.toFinset :=
  node_ok cuts251 [] 0x38988b03028988a26238988e06038188e0620c8c0703012028323018d88616018d8861620686032300c8c019181c98870601c18870620682832300c8c0210318d88e2622406063620c4c0636218d88313030f08c3c218d89001c32b08cac20c4c0636206828636218d8843623898891183898890301c0c05118140c0503038b08e2c2064600b0a1c988e262280c072621c0c072621c98832620646072621c988526234b08d2c21c9880b03389888a0a3898888181c0c04a0a1c0c04818 (by decide +kernel)

def state251_29 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_29 : Impossible true (goalAt 251) 7 state251_29.toFinset :=
  node_ok cuts251 [⟨state251_26,exclude251_26⟩,⟨state251_28,exclude251_28⟩] 0x38988b03028988a26238988e06038188e0620c8c0703012028323018d88616018d8861620686032300c8c01a180686032300c8c019180682832300c8c1001202c0c32300c8c0090318d88e2622406063620c4c0636218d88313008c0c636218d88436230f08c3c218d89000118d8831300c4c0636232b08cac20c4c063623898898183898898181c0c058181c0c0581838b08e26224460e26206460703014460703006460b03038988b030389887030128287030120601a0a08c0e000106828191802c28191802c28d2c22c0c0e2622c0c0e2621c0c043031c0c00b0302c0c2303800000b03064600b03064610022 (by decide +kernel)

def state251_30 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_30 : Impossible true (goalAt 251) 7 state251_30.toFinset :=
  node_ok cuts251 [⟨state251_25,exclude251_25⟩] 0xe0622c0c0a0622818898183818898183818858181c0c058181c0c0c8c20240c210380000090306460090306460111806828d2c206828d2c218d88e0622606063620c4c0636218d8831300840c636218d88436030f08c3c218d89000718d88d2c20c4c0d2c23818898183818898181c0c058181c0c0581838308e06226060e06206460703016060703006460726234b08d2c21c988928234b08d2c224b00d2c21c988726234b08d2c21c988726234b08323038188b0303818832301202870300c8c03230068601a180c8c0313018d88313018d881a180c8c032300686019180c8c0323006860d0c2 (by decide +kernel)

def state251_31 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_31 : Impossible true (goalAt 251) 7 state251_31.toFinset :=
  node_ok cuts251 [⟨state251_26,exclude251_26⟩,⟨state251_28,exclude251_28⟩] 0x38988b03028988a26238988e06038188e0620c8c070301202832300c8c01a1806860323018d88616018d8861620686032300c8c019181c98870601c188706208c0c32300c8c0210326060e26226060e26216060703016060703032b08191802c0c19180c4600b031c98a00011c9880b0308c0e000002c0c636238988981818d88313018d8863620c4c0c3c230f0863624001063621c988313018d88230318d88636210d88e26226060e262240c07030160605030140c0e2c238b08191802c28726238988a0301c98870301c98872620c98819181c988726214988d2c2389888a0a389888a0a1c0c04a0a1c0c04a0a (by decide +kernel)

def state251_32 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 3,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_32 : Impossible true (goalAt 251) 8 state251_32.toFinset :=
  node_ok cuts251 [⟨state251_27,exclude251_27⟩,⟨state251_29,exclude251_29⟩,⟨state251_30,exclude251_30⟩,⟨state251_31,exclude251_31⟩] 0x38988703038988b03040074b03038989002028988b0301c0c0a2622c0c072621c988e26234b08d2c22c0c0d2c234b08e2621c98872621c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c240070d2c234b0823031c98872628000c72621c988230334b08d2c206460d2c234b080b0a1c98872620646072621c9880b0a34b08d2c238988323038988e06040080e06038989002038188e0600c8c0e0621282832300c8c0703040074703012829001d1202870300c8c0323034b0a000234b08d0c00c8c0d0c034b08323034308d0c040048d0c202c0c32300c8c00901068601a1802c0c1a180686009010c8c0323018d88323018d88616006860616018d881a1818d8861600c8c0616208c0c1a180686021010c8c0323008c0c32300c8c02101068601a1802c281a180686019180c8c0323002c2832300c8c01918068601918260600b0326060e26240070e26226061002026060e26202c0ce262160600b0316060703040074703016061001d16060703002c0c7030068280b0306828d2c240070d2c20682a000106828d2c202c0cd2c240009000232b09001c02c0c0b0308c0d001c08c0d001c40072000008c0c0b0302c0c1918400881918400040b0302c0c191802c0c191840005001c04460981818d88636238989002038988981840080981838988636218d8858180c4c031301c0c0636218d88581818d8863621c0c031300c4c01a0a18d88636234b08313034b081a0a0c4c0313034b08636234b08230340010230340068636218d88230318d88636240071000410d88191840010c3c240004636230f08191818d88636240005000440004e26208c0ce26226061001c26060e26240080e26226060230326060703008c0c703016061001d16060703040074703016060230316061000240008e2c23898819183898898184008098183898900203898898180646019181c0c019181c0c058184007458181c0c1001d1c0c05818064601918 (by decide +kernel)

def state251_33 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_33 : Impossible true (goalAt 251) 7 state251_33.toFinset :=
  node_ok cuts251 [⟨state251_25,exclude251_25⟩] 0xe0622c0c0a0622818819183818881033818819181c0c041031c0c0c3c20646031188000019180240c191806460111802c28d2c206460d2c21a188e0622606068620e0c068621a18838300e06068621a1884a6032308c8c21a189000e1a188d2c20e0c0d2c23818898183818838181c0c058181c0c0381838308e06224040e06224040703014040703014040726234b08d2c21c988928234b08d2c224b00d2c21c988726234b08d2c21c988726234b08323038188b0303818832301202870300c8c0323002c2819180c8c032301a18838301a1881a180c8c032300686012100c8c0323004840d0c2 (by decide +kernel)

def state251_34 : List Sig := [0xffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00,input 4,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_34 : Impossible true (goalAt 251) 7 state251_34.toFinset :=
  node_ok cuts251 [⟨state251_26,exclude251_26⟩] 0xe2622c0c0a26228988e26238180e0623818832301c0c0480a0c8c06a621a18068621a1881a180c8c032300686072621c18070621c1880b030c8c032300240c19183898883033898819181c0c043031c0c019180c8c00b0a0c8c0c3c206460311880000191802c28726206460726202c0c19180646100021a988e262240606a620e0c06a621a98838300e0606a621a9884a621a98872620e0c06a6232b08cac21a98900023898898183898890301c0c05818140c0503038b08726238988a0301c98870301c98872620c98838181c988726214988d2c2389888303389880b031c0c043031c0c00b03 (by decide +kernel)

def state251_35 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 5,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_35 : Impossible true (goalAt 251) 8 state251_35.toFinset :=
  node_ok cuts251 [⟨state251_27,exclude251_27⟩,⟨state251_33,exclude251_33⟩,⟨state251_34,exclude251_34⟩] 0x38988703038988b0304008cb03038989002028988b0301c0c0a2622c0c072621c988e26234b08d2c22c0c0d2c234b08e2621c98872621c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c20e060d2c234b082a0a1c98872620e06072621c9882a0a34b08d2c240070d2c234b080b031c98872628000872621c9880b0334b08d2c238988323038988e0604001ce06038989002038188e0600c8c0e0621282832300c8c070304008c70301282900231202870300c8c0323034b0a000134b08d0c00c8c0d0c034b08323034308d0c04001cd0c21a98832301a98868600686068601a9881a181a18868600c8c068620a8281a180686038180c8c032300a82832300c8c03818068601a1802c0c12100484009010c8c0323002c0c32300c8c0090104840121020c0c191806460e26240080e26220c0d002020c0ce26206460e26210c0c19180646070304008c703010c0d002310c0c703006460703004c0c0b0a02c28d2c206460d2c204c0c191806460d2c202c28d2c24001c191806460323002c283230400600b0a02c28323006460323040005000130f09001c0646019180e061001c0c46100184007200000e0601918064600b03400700b03400081918064600b0306460191840009001c0446098181a9886a62389890020389889818400809818389886a621a98858180e0c038301c0c06a621a98858181a9886a621c0c038300e0c01a0a1a9886a6234b08383034b081a0a0e0c0383034b086a6234b083818400103818400686a621a98838181a9886a62400710004129880b0340010cac2400086a6232b080b031a9886a6240009000440008e2620e060e26226061001c26060e26240080e2622606038180e06070300e06070301606100231606070304008c70301606038180e061000140004e2c2389880b0338988901040070901038989002038988901002c0c90101c0c00b031c0c050104008c50101c0c100231c0c0501002c0c5010 (by decide +kernel)

def state251_36 : List Sig := [0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 5,input 0,input 3,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_36 : Impossible true (goalAt 251) 8 state251_36.toFinset :=
  node_ok cuts251 [] 0x38988b03028988a2621c988d2c234b08726224a08d2c234b0892c234b0872621c988d2c234b0872621c988d2c238988e06038188e0620c8c0703012028323034b08d0c034308d0c20c8c01a180686032300686032300c8c01a180c8c01a180686032300484032300c8c0121026060e26226060e26216060703016060703006828d2c206828d2c20e06023030e0600b031a989002206460e26220c0ce26206460703010c0c703002c28d2c206460d2c206460323002c28323002c0c19180446019180e060230306460636240070e26226060e2620e06070301606070300e060e2c226060e26226060e26216060703016060703006828d2c206828d2c20e061001a4007100043898890103898890101c0c050101c0c05010 (by decide +kernel)

def state251_37 : List Sig := [0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,input 0,input 3,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_37 : Impossible true (goalAt 251) 9 state251_37.toFinset :=
  node_ok cuts251 [⟨state251_18,exclude251_18⟩,⟨state251_24,exclude251_24⟩,⟨state251_32,exclude251_32⟩,⟨state251_35,exclude251_35⟩,⟨state251_36,exclude251_36⟩] 0x40074e2621c0c0e26240074b03040074b03040074e2624007ca26240074b0301c0c0a26240078e2620e060e26240070981838b08e2c240080e26238b08e2c24007098180e060903040074703028a08a28240074581838b08e2c240074703038b08e2c240074581828a08a2c240078b0301c988726240044e26234b08d2c24007cb03034b08d2c240078e2621c988726240074703024a089282400744a0a34b08d2c240074703034b08d2c2400744a0a24a0892c240070381834b08d2c240044e2c21c988e2c24006c38181c988726240070e2c234b08d2c24001ce2620c8c0e2624001ce0604001ce0604001ce2624007ce0624001ce0600c8c0e062400744a0a0c8c03230400747030400747030400744a0a40074480a4007470300c8c032304001ce2c206860e2c24001ce0c00c8c0e0c04001ce2c20c8c0e0c24001ce0c006860e0c24001cd2c24006cd2c24001cd0c00c8c0d0c04001cd2c20c8c0d0c24001cd0c04001cd0c2400040b030c8c03230400040901068601a18400040b03068601a184000409010c8c032304001d00070c8c032304001d0000068601a184001d0007068601a184001d00000c8c0323040004981802c0c981840004e26240004e2624000498184007c981840004e26202c0ce26240004581802c0c581840004703040004703040004581840074581840004703002c0c703040004381802c0c381840004e2c240004e2c24000438188000c381840004e2c202c0ce2c2400041a0a02c0c1a0a40004d2c240004d2c2400041a0a4006c1a0a40004d2c202c0cd2c240005000140008cac240008830306460191840008e26240008e2624000883034007c830340008e26206460e26240008430306460191840008703040008703040008430340074430340008703006460703040008230306460191840008e2c240008e2c240008230380008230340008e2c206460e2c240008130302c280b0a40008d2c206460d2c240008130306460191840008d2c202c28d2c240009000206460191840008323002c28323040009000202c280b0a400083230064603230400040b03400040b0340005000206460191840005000140004111840005000140004c3c240078981840018981840068e2624007ce2624007c98184007c981840078e26240018e26240074581840014581840074703040074703040074581840074581840074703040014703040070381840010381840068e2c280004e2c280010381880000381840070e2c240010e2c2400441a0a4000c1a0a40068d2c24006cd2c24006c1a0a4006c1a0a40068d2c24000cd2c2 (by decide +kernel)

def state251_38 : List Sig := [0x3333003333330022333300333333002233330033333300223333003333330022,input 4,input 3,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_38 : Impossible true (goalAt 251) 6 state251_38.toFinset :=
  node_ok cuts251 [] 0x38988b03028988a26238988e2c238b08903028a08e2c238b08a2c018d88c3c230f08636220e08c3c230f0883c030f08e2c218d88c3c230f08c8c206460c3c230f08d2c20c4c0c3c21a188c8c232308686222208c8c2323088ac032308e2c21a188c8c232308d2c20e0c0c8c21c988d2c234b08726224a08d2c234b0892c034b08e2c21c988d2c238188e06238180e2620c8c0480a1c0c0323038308e0c20c8c0e2c230708c3c218580c3c20c8c0c8c21a180c8c234308d0c21c180d2c2 (by decide +kernel)

def state251_39 : List Sig := [0xffff00ffffff00aaffff00ffffff00aaffff00ffffff00aaffff00ffffff00aa,input 4,input 3,input 0,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_39 : Impossible true (goalAt 251) 7 state251_39.toFinset :=
  node_ok cuts251 [⟨state251_38,exclude251_38⟩] 0xe2622c0c0a26228988e26238180e0623818832301c0c0480a0c8c01a180c8c0323006860cac232300c8c23230872621c18070621c18a00000c8c0323040000e26226060e262240c07030160605030140c0636238988830318d88313018d8863620c4c0616018d88636218588191818d88636210d88cbc232b08191832b0863621c988313018d88c3c230f08636202c284a4232b08cac2389888a8232b08cac222b08cac23ab08383032b08cac21c988383032b08cac20e0c06a6232b08726238988a0301c98870301c98872620c98838181c988726214988d2c2389888a0a389888a0a1c0c04a0a1c0c04a0a38b08e2c20e0602a0a (by decide +kernel)

def state251_40 : List Sig := [0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,input 4,0xff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa,input 0,input 5,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_40 : Impossible true (goalAt 251) 7 state251_40.toFinset :=
  node_ok cuts251 [] 0xe2622c0c0a26228988e26238180e0623818832301c0c0480a0c8c01a180c8c0323006860120a0c8c0323040048cac232300c8c232308e26224060e2620e06070301406070300e060636238988830318d88313018d8863620c4c0616018d88636218588191818d88636210d8863620c4c0313018d88cbc232b08313032b08e26224060e2620e0c038301406070300e0c032300686032300e0c0e2c238b0838300e060c3c230f0863620e0c028300e0c0383004829000332b086a6232b08b03038988b0303898870301282870301206038180a82828180a060d2c212908cac232b08e26222a08cac232b088ac232b08eac20e060cac2 (by decide +kernel)

def state251_41 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa,input 3,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_41 : Impossible true (goalAt 251) 7 state251_41.toFinset :=
  node_ok cuts251 [] 0x38188b03028188a0623818898183818838181c0c058181c0c0381818d88e0622040c63620c4c0636218d88313006460636218d88436032708c8c206460c8c218d88d2c20c4c0d2c212108c8c232308e06222208c8c2323088ac032308e8c20e060c8c232308d2c204828c8c23818898183818898181c0c058181c0c0581838308e0c20840c381830f08c3c218d8819181a188726234b08726234b08323006860323006860726234b08d2c21c988928234b08d2c224b00d2c21c988726234b08323038188b0303818832301202870300c8c01a180c8c0323006860313018d88313018d883230323081a1832308d0c2 (by decide +kernel)

def state251_42 : List Sig := [0xff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa00ff00ff00aa00aa,input 3,input 0,input 5,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_42 : Impossible true (goalAt 251) 8 state251_42.toFinset :=
  node_ok cuts251 [⟨state251_39,exclude251_39⟩,⟨state251_40,exclude251_40⟩,⟨state251_41,exclude251_41⟩] 0xe2621c0c0e2622c0c100202c0c0e26240080a2622c0c0703028988b0301c988726238988d2c234b08b03034b08d2c23898872621c988703024a08928212828d2c234b08703034b08d2c212828928224b08381834b08d2c20a82872621c98838181c98872620a828d2c234b08e2620c8c0e26238181002038180e26240080e062381803230381884a0a0c8c032301c0c100211c0c04a0a40084480a1c0c032300c8c0d2c280008d2c234300323034300d2c20c8c0d0c2343010012343082a0a068601a180e06032300c8c02a0a0c8c032300e0601a1806860cac20c8c0cac2323001a1832300cac206860c8c232300323032308e2620e060e26226061001c26060e26240080e2622606038180e06070300e060703016061001c1606070304008470301606038180e060830318d88636238989002038988830340080830338988636218d8843030c4c031301c0c0636218d88430318d8863621c0c031300c4c0130318d88636234b08313034b0813030c4c0313034b08636234b0900121858061600c8c0636218d89002218d8863620c8c061601858823030646019180e060636218d88230318d8863620e060191810d89001c18d88cbc232b08191832b09002206460191832b08636232b089818129084a4238988cac232b08981832b08cac2389884a4238988581822a088a821c0c0cac232b08581832b08cac21c0c08a8222b081a0a32b08cac234b09001c34b081a0a80004120a34b08cac232b08381832b08cac208c0d001c3ab08381840070381808c0ccac232b08e26240018e26226061002026060e26240080e2622606100062606070304001470301606100211606070304008470301606100051606072624000c726234b09002234b08726280000726234b09000334b08323040000323006861001206860323040048323006861000006860230340004e2c20e061000238b0823034000823030e06100010e060636240004c3c206461000430f086362400106362064610001064610022400706a62 (by decide +kernel)

def state251_43 : List Sig := [0x3333000033330000333300003333000033330000333300003333000033330000,input 4,0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_43 : Impossible true (goalAt 251) 7 state251_43.toFinset :=
  node_ok cuts251 [⟨state251_25,exclude251_25⟩] 0xe0622c0c0a06228188636238188810318d88313018d8863620c4c0c3c218d8868628000063620840c636218d88436018d88d2c20c4c0d2c23818898183818838181c0c058181c0c0381838308e0c20e06100071a188e0622606068620e0c068621a18838300e06068621a1884a6032308686234b08383034b08e06224040e06224040703014040703014040726234b08d2c21c988928234b08d2c224b00d2c21c988726234b08d2c21c988726234b08323038188b0303818832301202870300c8c0313018d88313018d881a180c8c032300686032301a18838301a18812100c8c0323004840d0c2 (by decide +kernel)

def state251_44 : List Sig := [0xffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00,input 4,input 3,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_44 : Impossible true (goalAt 251) 7 state251_44.toFinset :=
  node_ok cuts251 [⟨state251_26,exclude251_26⟩] 0xe2622c0c0a26228988e26238180e0623818832301c0c0480a0c8c01a180c8c03230068606a621a18068621a18872621c18070621c18823030c8c032300840c636238988830318d88313018d8863620c4c0616018d88636218588c3c218d886a6280000636218d8872620c4c0636208c0c636218d8843623898898183898890301c0c05818140c0503038b08e2c20e06100021a988e262240606a620e0c06a621a98838300e0606a621a9884a621a98872620e0c06a6232b08726238988a0301c98870301c98872620c98838181c988726214988d2c23898883033898823031c0c043031c0c02303 (by decide +kernel)

def state251_45 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_45 : Impossible true (goalAt 251) 8 state251_45.toFinset :=
  node_ok cuts251 [⟨state251_27,exclude251_27⟩,⟨state251_43,exclude251_43⟩,⟨state251_44,exclude251_44⟩] 0x38988703038988b03040090b03038989002428988b0301c0c0a2622c0c072621c988e26234b08d2c22c0c0d2c234b08e2621c98872621c0c0928224a084a0a34b08d2c21c0c0d2c234b084a0a24a0892c20e060d2c234b082a0a1c98872620e06072621c9882a0a34b08d2c240070d2c234b0823031c98872628000872621c988230334b08d2c238988323038988e06040090e06038989002438188e0600c8c0e0621282832300c8c070304009c70301282900271202870300c8c0323034b0a000134b08d0c00c8c0d0c034b08323034308d0c040048d0c20a8281a180686038180c8c032300a82832300c8c03818068601a181a98832301a98868600686068601a9881a181a18868600c8c0686208c0c12100484021010c8c0323008c0c32300c8c0210104840121020c0c636218d88e26240090e26220c0d002420c0ce26218d88636210c0c31300c4c0703018d88636210c0c636218d8870300c4c0313004c0c636218d88d2c20c4c0d2c204c0c31300c4c0d2c218d88d2c240048616018580323018d88636240060636218d88323018580616240011000430f09001c18d8863621a989001c1a98900184007200001a988636218d88230340070230340008636218d88230318d88636240009001c10d88e2620e060e26226061002426060e26240090e2622606038180e06070300e06070301606100271606070304009c70301606038180e060230340004e2c240008381838b0823030e06038184000900014000498181a9886a62389890024389889818400909818389886a621a98858180e0c038301c0c06a621a98858181a9886a621c0c038300e0c01a0a1a9886a6234b08383034b081a0a0e0c0383034b086a6234b083818400883818400046a621a98838181a9886a6240005001c12989000440010cac238988230338988901040090901038989002438988901008c0c90101c0c023031c0c050104009c50101c0c100271c0c0501008c0c5010 (by decide +kernel)

def state251_46 : List Sig := [0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa,input 3,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_46 : Impossible true (goalAt 251) 8 state251_46.toFinset :=
  node_ok cuts251 [] 0x38988b03028988a2621c988d2c234b08726224a08d2c234b0892c234b0872621c988d2c234b0872621c988d2c234b0872621c988d2c238988e06038188e0620c8c0703012028323034b08d0c034308d0c20686032300c8c01a180686032300c8c01a181a98868601a18868620484032300c8c012103898898183898898181c0c058181c0c058180e061001a18d88e26220c0c63620c4c0636218d88313018d88d2c20c4c0d2c218580636218d88616208c0c636210d88191818d886a6202c0c636240070e26226060e2622606070301606070301606100011a988e262260606a620e0c06a621a98838301a988d2c20e0c0d2c202c0c6a621a9880b03400886a6240070cac23898890103898890101c0c050101c0c05010 (by decide +kernel)

def state251_47 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 3,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_47 : Impossible true (goalAt 251) 9 state251_47.toFinset :=
  node_ok cuts251 [⟨state251_32,exclude251_32⟩,⟨state251_18,exclude251_18⟩,⟨state251_42,exclude251_42⟩,⟨state251_45,exclude251_45⟩,⟨state251_46,exclude251_46⟩] 0x40074e2621c0c0e26240074b03040074b03040074e26240090a26240074b0301c0c0a26240090b0301c988726240090e26234b08d2c240090b03034b08d2c240090e2621c988726240074703024a089282400744a0a34b08d2c240074703034b08d2c2400744a0a24a0892c240011000434b08d2c24001023031c98872624001100261c988726240010230334b08d2c240089002634b08d2c24005500031c98872624009900261c988726240055000334b08d2c24009098181a9886a6240090e26232b08cac240090981832b08cac240090e2621a9886a6240074581822a088a8240074703032b08cac240074581832b08cac240074703022a088ac2400541a0a32b08cac240070d2c20e0c0d2c2400981a0a0e0c0383040070d2c232b08cac240011000432b08cac24001023031a9886a624001200031a9886a6240010230332b08cac24008a000232b08cac24007100011a9886a628001200011a9886a6240071000132b08cac240090e2620c8c0e26240090e06040090e06040090e26240090e06240090e0600c8c0e062400744a0a0c8c03230400747030400747030400744a0a40074480a4007470300c8c0323040054d2c240098d2c240038d0c00c8c0d0c040054d2c20c8c0d0c240038d0c040094d0c240070cac20c8c0cac240038c8c006860c8c040048cac206860c8c240070c8c00c8c0c8c2400102303068601a184001021010c8c032304001023030c8c03230400102101068601a18400890025068601a184003900000c8c032304009500250c8c03230400390000068601a1840010e26208c0ce26240010981840010981840010e26240090e26240010981808c0c981840010703008c0c703040010581840010581840010703040074703040010581808c0c581840009000240008e2c240008830318d88636240008e26240008e26240008830340090830340008e26218d8863624000843030c4c0313040008703018d88636240008430318d8863624000870300c4c0313040008130318d88636240008d2c20c4c0d2c24000813030c4c0313040008d2c218d88d2c2400080b0318d88636240008cac240008cac2400080b03800000b0340008cac218d88cac240009000218580616040008323018d88636240009000218d88636240008323018580616240008230340010230340009000218d88636240009000240008436240009000240010c3c240090e26240018e26240090981840090981840090e26240090e262400909818400189818400747030400147030400745818400745818400747030400747030400745818400145818 (by decide +kernel)

def state251_48 : List Sig := [0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,input 3,input 5,input 0,input 1,input 4,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_48 : Impossible true (goalAt 251) 9 state251_48.toFinset :=
  node_ok cuts251 [⟨state251_18,exclude251_18⟩,⟨state251_35,exclude251_35⟩,⟨state251_45,exclude251_45⟩,⟨state251_9,exclude251_9⟩] 0x40090e2621c0c0e26240090b03040090b03040090e26240090a26240090b0301c0c0a26240090b0301c988726240090e26234b08d2c240090b03034b08d2c240090e2621c98872624009c703024a0892824009c4a0a34b08d2c24009c703034b08d2c24009c4a0a24a0892c240010381834b08d2c2400102a0a1c98872624001038181c9887262400102a0a34b08d2c240071001c34b08d2c24007100031c98872624007100191c988726240071000334b08d2c240090e2620c8c0e26240090e06040090e06040090e26240090e06240090e0600c8c0e0624009c4a0a0c8c032304009c70304009c70304009c4a0a4009c480a4009c70300c8c032304001cd2c240064d2c24001cd0c00c8c0d0c04001cd2c20c8c0d0c24001cd0c04001cd0c2400102a0a068601a184001038180c8c03230400102a0a0c8c03230400103818068601a18400046a620c8c06a62400046860068606860400046a620686068624000468600c8c068624001d00070484012104001d00000c8c032304001d00070c8c032304001d000004840121040090830318d88636240090e26230f08c3c240090830330f08c3c240090e26218d8863624009c430320e0883824009c703030f08c3c24009c430330f08c3c24009c703020e0883c240054130330f08c3c240064d2c20c4c0d2c24006413030c4c0313040054d2c230f08c3c24001d000730700c1c04001c323030f08c3c24001e000330f08c3c24001c323030700c1c240011000430f08c3c240010381818d88636240012000218d88636240010381830f08c3c240005000130f08c3c2400046a62064606a62400060001064601918400046a6230f08c3c240071001c30f08c3c240071000218d88636240072000018d88636240071000230f08c3c240010e2620e060e26240010981840010981840010e26240090e2624001098180e06038184001070300e06070304001058184001058184001070304009c70304001058180e060381840005000140004e2c24000498181a9886a6240004e26240004e26240004981840090981840004e2621a9886a624000458180e0c038304000470301a9886a624000458181a9886a624000470300e0c03830400041a0a1a9886a6240004d2c20e0c0d2c2400041a0a0e0c0383040004d2c21a988d2c24000438184001038184000500011a9886a62400050001400044a6240005000140010cac240090e26240018e26240090901040090901040090e26240090e2624009090104001890104009c70304001470304009c50104009c50104009c70304009c70304009c5010400145010 (by decide +kernel)

def state251_49 : List Sig := roots 251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude251_49 : Impossible true (goalAt 251) 10 state251_49.toFinset :=
  node_ok cuts251 [⟨state251_10,exclude251_10⟩,⟨state251_37,exclude251_37⟩,⟨state251_47,exclude251_47⟩,⟨state251_48,exclude251_48⟩] 0x40018e2621c0c0e26240018b03040018b03040018e26240018a26240018b0301c0c0a26240018e2620e060e26240018981838b08e2c240018e26238b08e2c24001898180e060903040014703028a08a28240014581838b08e2c240014703038b08e2c240014581828a08a2c240018b0301c988726240018e26234b08d2c240018b03034b08d2c240018e2621c988726240014703024a089282400144a0a34b08d2c240014703034b08d2c2400144a0a24a0892c24000c381834b08d2c24000ce2c21c988e2c24000c38181c98872624000ce2c234b08d2c24001898181a9886a6240018e26232b08cac240018981832b08cac240018e2621a9886a6240014581822a088a8240014703032b08cac240014581832b08cac240014703022a088ac240010381832b08cac240004e2c21a988e2c28000c38181a9886a6240004e2c232b08cac24000c1a0a32b08cac240004d2c20e0c0d2c24000c1a0a0e0c0383040004d2c232b08cac240000e2620c8c0e26240000e06040000e06040000e26240018e06240000e0600c8c0e062400004a0a0c8c03230400007030400007030400004a0a40014480a4000070300c8c0323040000e2c206860e2c240000e0c00c8c0e0c040000e2c20c8c0e0c240000e0c006860e0c240000d2c24000cd2c240000d0c00c8c0d0c040000d2c20c8c0d0c240000d0c040000d0c240000cac20c8c0cac240000c8c006860c8c040000cac206860c8c240000c8c00c8c0c8c240018830318d88636240018e26230f08c3c240018830330f08c3c240018e26218d88636240014430320e08838240014703030f08c3c240014430330f08c3c240014703020e0883c240010230330f08c3c240008e2c218d88e2c280008230318d88636240008e2c230f08c3c24000c130330f08c3c24000cd2c20c4c0d2c24000c13030c4c031304000cd2c230f08c3c2400040b0330f08c3c240008cac206460cac2800040b0306460191840004cac230f08c3c240001000030700c1c040000323030f08c3c240002000030f08c3c240000323030700c1c2 (by decide +kernel)

theorem lower251 : Claim 251 11 :=
  fromSearch 67 (by decide +kernel) exclude251_49


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [4, 1]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def eightInputs : List Sig := roots 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r graph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([3, 4, 5, 0, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩


theorem replaceShort
    (lower : Impossible true graph 11 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates, smallCircuit.output, witnessMonotone, (by simpa only [witnessSize] using big), witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates, o, noNotReuse fit mono, Nat.le_refl _, correct⟩
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot, hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fit g hg
  obtain ⟨k, hk, run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

theorem lowerGraph : Impossible true graph 11 eightInputs.toFinset :=
  (ruleFor 255 lower251 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31243_aux

open PEqualNP.Outside.L_meta_31243_aux in
theorem PEqualNP.Outside.L_meta_31243 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31357_aux


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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)


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




def cuts193 : Cuts (goalAt 193) := []

def state193_0 : List Sig := roots 193
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude193_0 : Impossible true (goalAt 193) 3 state193_0.toFinset :=
  node_ok cuts193 [] 0x30100410130100810130200c08030100c08030200810110404410120404414010500c04020600818020404818020600c04010500414010404818020600c08010500c08010404414010500c080206008180 (by decide +kernel)

theorem lower193 : Claim 193 4 :=
  fromSearch 6 (by decide +kernel) exclude193_0

theorem lower225 : Claim 225 5 :=
  fromLift 5 32 5 lower193 (by decide +kernel)

theorem lower209 : Claim 209 5 :=
  fromLift 5 16 393222 lower193 (by decide +kernel)

def cuts240 : Cuts (goalAt 240) := []

def state240_0 : List Sig := roots 240
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude240_0 : Impossible true (goalAt 240) 3 state240_0.toFinset :=
  node_ok cuts240 [] 0x38180d09034240a06038180b0902c240c0602c240d090140c0b0901c180e060280c0706034240c08030240c0902c240a08028240a090 (by decide +kernel)

theorem lower240 : Claim 240 4 :=
  fromSearch 1417019392 (by decide +kernel) exclude240_0

def cuts161 : Cuts (goalAt 161) := []

def state161_0 : List Sig := roots 161
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude161_0 : Impossible true (goalAt 161) 3 state161_0.toFinset :=
  node_ok cuts161 [] 0x28080210128080810128200a08028080a08028200810108404210120404212008480a02020600818020404818020600a02008480212008404818020600a08008480a08008404212008480a080206008180 (by decide +kernel)

theorem lower161 : Claim 161 4 :=
  fromSearch 5 (by decide +kernel) exclude161_0

def cuts113 : Cuts (goalAt 113) := []

def state113_0 : List Sig := roots 113
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude113_0 : Impossible true (goalAt 113) 3 state113_0.toFinset :=
  node_ok cuts113 [] 0x1c0c05111140c050301c0c070601c18041111410070601c18050600c4c061601858031301050061601858041601858070600c4c06160 (by decide +kernel)

theorem lower113 : Claim 113 4 :=
  fromSearch 393221 (by decide +kernel) exclude113_0

def rule241_0 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower225 none (by decide +kernel)

def rule241_1 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower209 none (by decide +kernel)

def rule241_2 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower240 none (by decide +kernel)

def rule241_3 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower161 none (by decide +kernel)

def rule241_4 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower113 none (by decide +kernel)

def rule241_5 : {c : Cut // CutGood (goalAt 241) c} :=
  ruleFor 241 lower193 none (by decide +kernel)

def cuts241 : Cuts (goalAt 241) := [rule241_0,rule241_1,rule241_2,rule241_3,rule241_4,rule241_5]

def state241_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaa,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_0 : Impossible true (goalAt 241) 4 state241_0.toFinset :=
  node_ok cuts241 [] 0x1c0c0c0903024050801c180c09030241000328240c090140c0a090280c0a0902824021111c180a09028240506024640c09010444919024640a0900c4c091900c4c0919024640313018580e060 (by decide +kernel)

def state241_1 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaa,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_1 : Impossible true (goalAt 241) 4 state241_1.toFinset :=
  node_ok cuts241 [] 0xe06030240c09028180a09030240503028240e06028240a09030180919030240411124640919028240313024640e16024640919038180703030240706030240504028240706028240616024640313024640a030 (by decide +kernel)

def state241_2 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_2 : Impossible true (goalAt 241) 5 state241_2.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_1,exclude241_1⟩] 0xe0601c0c0e0602c0c0d09034240e06034240d0902c0c0703028180e06008444e06030100b0902c240e0602c240b0903010021113018070302c240b0903424100053424070304000c503034240b0902c24081110c4c031303818091902464081112464091903818031303818041112464091903424100023064041114000c41113424091902464021112464091902c24031302864021110c4c031302c24091902464100004000081802c0c070601c180e06080004e0602c0c20000280c0e0601c180706034241000334240c0801c180c08034240706030240c0804000cc0902c24050402c240a0801c180a0802c240706028240a08014100a090 (by decide +kernel)

def state241_3 : List Sig := [0x5555555555555555555555555555555555550000555500005555000055550000,input 0,input 7,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_3 : Impossible true (goalAt 241) 4 state241_3.toFinset :=
  node_ok cuts241 [] 0x703030240c09014200a09030240503028240a03028240a09008444212030240616030240414028240616028240616038580811118580c0901c180c09010444a0901c180a09014180706038180a0301c1809190 (by decide +kernel)

def state241_4 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 0,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_4 : Impossible true (goalAt 241) 5 state241_4.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_3,exclude241_3⟩] 0x100031c0c07030280c0c09030241000330240c090280c070301420070601040470604000cc09030240706030240c0904000c410110444703028240a0903024100053024070304000c503030240a09028240a0300c444a03020444a09028240a03028240a0902044431110c444706008404706014100a09028240706028240a090141002101141805111246409190302406160302405111185806160302409190246403111246409190282406160282403111185806160282409190246408111185806160280c09190246408111246409190280c061601858200011858061601c18091902464200002464091901c180616018581000040000e060 (by decide +kernel)

def state241_5 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 0,input 7,input 4,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_5 : Impossible true (goalAt 241) 4 state241_5.toFinset :=
  node_ok cuts241 [] 0x38180d09034240a06034240c08030240c0901c180e060280c0706024640d0901858091902060091902464081901858091902464061602c240503034240b09028240a0902c240a08030180b0902c240e06024640616024640b090 (by decide +kernel)

def state241_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 4,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_6 : Impossible true (goalAt 241) 5 state241_6.toFinset :=
  node_ok cuts241 [⟨state241_0,exclude241_0⟩,⟨state241_5,exclude241_5⟩] 0x703034240d0901c0c0703034240d0901c0c0b0903424050302c24031112c240b0900c44600012c240b09040004d09030200c09030240b09028200a0902824070602040481111c18070604000200001c180e06024640d09014444919024640b0900c4449190206009190246408190244449190400086160 (by decide +kernel)

def state241_7 : List Sig := roots 241
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude241_7 : Impossible true (goalAt 241) 6 state241_7.toFinset :=
  node_ok cuts241 [⟨state241_2,exclude241_2⟩,⟨state241_4,exclude241_4⟩,⟨state241_6,exclude241_6⟩] 0x4000ce0601c0c0e0604000cb03034240d0904000ce06034240d0904000cb0301c0c0a06040004e0600c444e06040004c0402c240b09040004e0602c240b09040004c0400c444c0604000470302c240b09040004d09040004d0904000470304000c503040004d0902c240b09040000b0301c180706040000e06040000e06040000b03080004a03040000e0601c180706040000d0904000cd09040000c0801c180c08040000d0901c180c09040000c08040000c09040000b09014100b09040000a0801c180a08040000b0901c180a09040000a08014100a09040010911118580616040008e06024640919080008911124640919040008e0601858061604000c511124640919040008d09018580d0904000c511118580616040008d09024640919040004311124640919040004b09018580b09040004311118580616040004b090246409190400010000206008180400007060246409190400020000246409190400007060206008190 (by decide +kernel)

theorem lower241 : Claim 241 7 :=
  fromSearch 393221 (by decide +kernel) exclude241_7

def cuts84 : Cuts (goalAt 84) := []

def state84_0 : List Sig := roots 84
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude84_0 : Impossible true (goalAt 84) 3 state84_0.toFinset :=
  node_ok cuts84 [] 0x140401404140404404141005040140405040141004404050101404110101410050405010111004440110104440111005010050401410050104440111005040050405040050101410050405040111004440 (by decide +kernel)

theorem lower84 : Claim 84 4 :=
  fromSearch 33686528 (by decide +kernel) exclude84_0

theorem lower212 : Claim 212 5 :=
  fromLift 5 128 1644299264 lower84 (by decide +kernel)

theorem lower244 : Claim 244 6 :=
  fromLift 6 32 1377960960 lower212 (by decide +kernel)

theorem lower229 : Claim 229 6 :=
  fromLift 6 4 1285 lower225 (by decide +kernel)

theorem lower197 : Claim 197 5 :=
  fromLift 5 4 1542 lower193 (by decide +kernel)

theorem lower85 : Claim 85 5 :=
  fromLift 5 1 132102 lower84 (by decide +kernel)

def rule213_0 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower209 none (by decide +kernel)

def rule213_1 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower197 none (by decide +kernel)

def rule213_2 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower212 none (by decide +kernel)

def rule213_3 : {c : Cut // CutGood (goalAt 213) c} :=
  ruleFor 213 lower85 none (by decide +kernel)

def cuts213 : Cuts (goalAt 213) := [rule213_0,rule213_1,rule213_2,rule213_3]

def state213_0 : List Sig := roots 213
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude213_0 : Impossible true (goalAt 213) 6 state213_0.toFinset :=
  node_ok cuts213 [] 0x4000cc04014444c0404000c911134240d0904000cc04034240d0904000c911114444509040004911114100504040004c04025210948440004911125210948440004c04014100504040004d09025210d09040004c48414100c48440004d09014100c09040004c48425210c09040000850511100444040000c04025240949040000850525240949040000c04011100444040000c48425240949040000d09011100d09040000c48411100c08440000d09025240949040000948411100948440000504025240949040000948425240949040000504011100444040008911110500414040008c04024640919040008911124640919040008c04010500414040008511124640919040008d09010500d09040008511110500414040008d090246409190400041505216108584400049484246409190400041505246409190400049484216108584400001511246409190400009490216109490400001511216108584400009490246409190 (by decide +kernel)

theorem lower213 : Claim 213 7 :=
  fromSearch 132102 (by decide +kernel) exclude213_0

def cuts180 : Cuts (goalAt 180) := []

def state180_0 : List Sig := roots 180
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude180_0 : Impossible true (goalAt 180) 3 state180_0.toFinset :=
  node_ok cuts180 [] 0x2c0c0b0902c24024842c0c0948425210a0302c240a48428240a0900d0c0949025240343025240b090282109490252109490252402430 (by decide +kernel)

theorem lower180 : Claim 180 4 :=
  fromSearch 1344406528 (by decide +kernel) exclude180_0

theorem lower165 : Claim 165 5 :=
  fromLift 5 4 1285 lower161 (by decide +kernel)

def cuts53 : Cuts (goalAt 53) := []

def state53_0 : List Sig := roots 53
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude53_0 : Impossible true (goalAt 53) 3 state53_0.toFinset :=
  node_ok cuts53 [] 0xc44425050844421110544434300d0c014300908034300d0c024300c44431300c4c024050848031300c4c021300c4c03430050443130 (by decide +kernel)

theorem lower53 : Claim 53 4 :=
  fromSearch 132101 (by decide +kernel) exclude53_0

def rule181_0 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower180 none (by decide +kernel)

def rule181_1 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower161 none (by decide +kernel)

def rule181_2 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower165 none (by decide +kernel)

def rule181_3 : {c : Cut // CutGood (goalAt 181) c} :=
  ruleFor 181 lower53 none (by decide +kernel)

def cuts181 : Cuts (goalAt 181) := [rule181_0,rule181_1,rule181_2,rule181_3]

def state181_0 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_0 : Impossible true (goalAt 181) 4 state181_0.toFinset :=
  node_ok cuts181 [] 0xc4c0919024640313024640a0900c4c09190216109190246408584280c0a09028240211129210a0302521094840520034302524094900d0c091902161091902524094900d0c0a090252410001 (by decide +kernel)

def state181_1 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_1 : Impossible true (goalAt 181) 5 state181_1.toFinset :=
  node_ok cuts181 [⟨state181_0,exclude181_0⟩] 0x85050d0c03430280c09490252408505252409490280c034300d0c100012524094902824034302824100010d0c034302824094902524094848000094844000494902524094842524094904000500014000491110c4c03130280c09190246409111246409190280c031300c4c015112464091902524085842524015112161085842524091902464021112464091902824031302824021110c4c0313028240919024640150521610858425210919024640150524640919025210858421610a03008444a03024444a09028240a03028240a09024444211108445000240008a484280c01505280c08505252109484280c09484252108505054141484 (by decide +kernel)

def state181_2 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_2 : Impossible true (goalAt 181) 4 state181_2.toFinset :=
  node_ok cuts181 [] 0x2c240a48428240a09025210949025240243025240b09028210949021610919024640858424640949021610919024640b0900c4c09190280c094842c0c094840d0c094900d0c0949009210b0902c0c0b0900c4c091900c4c09190 (by decide +kernel)

def state181_3 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_3 : Impossible true (goalAt 181) 5 state181_3.toFinset :=
  node_ok cuts181 [⟨state181_2,exclude181_2⟩] 0xb030252109484280c094840941421112521094840541415052521034302524094900d0c09484252409490090c094900d0c034302524094900d0c0343025240b03024444b0300c444b0900c4c0b0302444431300848094840c4c094840c4c094900544494900c44431300901491902c0c200002c0c10003 (by decide +kernel)

def state181_4 : List Sig := [0xffff5555ffff0000ffff5555ffff0000ffff5555ffff0000ffff5555ffff0000,input 0,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_4 : Impossible true (goalAt 181) 4 state181_4.toFinset :=
  node_ok cuts181 [] 0xd0c0949025240343025240a0900d0c09490252109490252410001280c0a0902824031110c4c0919024640313024640949021610919024640a0900c4c09190216109190246408584280c0948425210148428240a484282409484 (by decide +kernel)

def state181_5 : List Sig := [0x5555555500000000555555550000000055555555000000005555555500000000,input 0,input 5,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_5 : Impossible true (goalAt 181) 5 state181_5.toFinset :=
  node_ok cuts181 [⟨state181_4,exclude181_4⟩] 0xb030252109484280c094840941421112521034302524094900d0c09484252409490090c094900d0c0343025240b03024444b0300c44491112464091902c0c0858424640919021610919025240858424640b1900c44491902c0c091112c0c091114000894848000094840d0c094900d0c094902c2403130 (by decide +kernel)

def state181_6 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_6 : Impossible true (goalAt 181) 5 state181_6.toFinset :=
  node_ok cuts181 [] 0x31112c240b0900c44424042c240b09009010b09029210a0902824091112521094842044414042521094840501094902c240a084252409484252409490090c034302524094900d0c034302524094900d0c0b03024640b0900c4449190216109190246408584246409490216109190244449190400003130 (by decide +kernel)

def state181_7 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_7 : Impossible true (goalAt 181) 4 state181_7.toFinset :=
  node_ok cuts181 [] 0x2c0c0948425210a0302c240a48428240a0902521094902524024300d0c0949025240343025240b0902821094902c0c0b0902c24024842161091902464085842464085842524091900c4c091902464031302464031302c2409190 (by decide +kernel)

def state181_8 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_8 : Impossible true (goalAt 181) 5 state181_8.toFinset :=
  node_ok cuts181 [⟨state181_7,exclude181_7⟩] 0xb030252109484280c0b09029210a090282401505252109484054149484252409490090c034302524094900d0c094902c240a0842524015112524094900544485842464091902161091902524085842464031302464091900c4c091902c24031302464200002464091904000091112c0c0b090092103111 (by decide +kernel)

def state181_9 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_9 : Impossible true (goalAt 181) 4 state181_9.toFinset :=
  node_ok cuts181 [] 0xd0c0949025240343025240b0902821094902521094902524100012464094902161091900c4c0919024640313024640b0900c4c091902161091902464085842c0c0b0902c24021112c0c0948425210a0302c240a48428240a090 (by decide +kernel)

def state181_10 : List Sig := [0xffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_10 : Impossible true (goalAt 181) 5 state181_10.toFinset :=
  node_ok cuts181 [⟨state181_9,exclude181_9⟩] 0x911125210948405210b09029210a090282409484252409490090c034302524094900d0c094902c240a0842524085842464091902161091902524085842464031302464091900c4c091902c240313024640b1112c24091114000894848000094840d0c094900d0c094900c4c091900c4c091902c0c03111 (by decide +kernel)

def state181_11 : List Sig := roots 181
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude181_11 : Impossible true (goalAt 181) 6 state181_11.toFinset :=
  node_ok cuts181 [⟨state181_1,exclude181_1⟩,⟨state181_3,exclude181_3⟩,⟨state181_5,exclude181_5⟩,⟨state181_6,exclude181_6⟩,⟨state181_8,exclude181_8⟩,⟨state181_10,exclude181_10⟩] 0x4000cb0300c444b0308001491112c240b09080010b0302c240b0904000c91110c444248440008b03005414b03040008a02025210948440008b03025210948440008a02005414a03040008b09025210b09040008a48440008a48440008b09080000a09040008a48425210a0904000485050d0c0343040004b03025240949040004850525240949040004b0300d0c0343040004a48425240949040004b0900d0c0b09040004a4840d0c0a08440004b0902524094904000894840908094844000900012524094904000894842524094904000900020908024304000c91110c4c0313040000b0302464091908000c911124640919040000b0300c4c0313080008311124640919040000b0900c4c0b0908000431110c4c0313040000b090246409190400081505216108584400089484246409190400081505246409190400089484216108584400041511246409190400009490216109490400041511216108584400009490246409190 (by decide +kernel)

theorem lower181 : Claim 181 7 :=
  fromSearch 132101 (by decide +kernel) exclude181_11

theorem lower116 : Claim 116 5 :=
  fromLift 5 32 35783680 lower84 (by decide +kernel)

theorem lower117 : Claim 117 6 :=
  fromLift 6 1 132101 lower116 (by decide +kernel)

def rule245_0 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower241 none (by decide +kernel)

def rule245_1 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower244 none (by decide +kernel)

def rule245_2 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower229 none (by decide +kernel)

def rule245_3 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower213 none (by decide +kernel)

def rule245_4 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower181 none (by decide +kernel)

def rule245_5 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower116 none (by decide +kernel)

def rule245_6 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower117 none (by decide +kernel)

def rule245_7 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower212 none (by decide +kernel)

def rule245_8 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower165 none (by decide +kernel)

def rule245_9 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower225 none (by decide +kernel)

def rule245_10 : {c : Cut // CutGood (goalAt 245) c} :=
  ruleFor 245 lower85 none (by decide +kernel)

def cuts245 : Cuts (goalAt 245) := [rule245_0,rule245_1,rule245_2,rule245_3,rule245_4,rule245_5,rule245_6,rule245_7,rule245_8,rule245_9,rule245_10]

def state245_0 : List Sig := [0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa,input 0,input 4,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude245_0 : Impossible true (goalAt 245) 7 state245_0.toFinset :=
  node_ok cuts245 [] 0xe0601c0c0e0602c0c0d09034240e06034240d0902c0c0703028180e0600c444e06030100b0902c240e0602c240b0903010031113018070302c240b09034241000734240703040020503034240b0902c240850519180646038180949025240850525240949038180646019180c48425240949034240646034240c48419180c08434240949025240a4842524094902c24064602c240a48419180a0842c240949025240150519180646040024949025240150525240949040008646019181000919180646040000949025241000925240949040000646019180b03005414b03038181000238180b03040014b03038180150538180d09005414d09031211000231210d09040020d09031210150531210b09005414b09029211000229210b0904001cb0902921015052921100014000494842444431300c4c0e06024640919024444919024640e0600c4c0e06014444919024640d09040004d09014445000814044d0902464091900c444919024640b0900c4c0b0900c44431300c4c0b0902464091900544491902464094904000494900544500090504494902464091900541500020541500012464091904000500012064100014000885842c0c100062c0c0e06040014e0602c0c100052c0c0e06040018e06034241000434240c48440020c48434241000834240c48440010c4842c24100032c240a4844001ca4842c24100072c240a4844000ca484 (by decide +kernel)

def state245_1 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude245_1 : Impossible true (goalAt 245) 7 state245_1.toFinset :=
  node_ok cuts245 [] 0x100061c0c070302c0c0d09034241000834240d0902c0c0703014241000811414450540010d09034241000834240d0904001045051141470302c240b09034241000a34240703040020503034240b0902c240b0300c444b03024444b0902c240b0302c240b0902444431110c445000a0941425054000cb0902c241000a2c240b0904000c250509414c48425240949034240646034240c48419180c08434240949025240a4842524094902c24064602c240a48419180a0842c24094902524100061918064602c0c094902524100092524094902c0c064601918094841918094844002494902524094842524094904000864601918100091918064604000094902524100092524094904000064601918051112464091903424061603424051111858061603424091902464031112464091902c24061602c24031111858061602c24091902464015112464091902524085842524015112161085842524091902464091111858061602c0c091902464091112464091902c0c0616018581000221610858425210919024641000524640919025210858421611000518580616040004919024641000524640919040004616018581000640008e06034240948434240c48440008c48434241000830240c48425210c0902c24094842c240a48440008a4842c241000a28240a48425210a0902c0c100062c0c10002252109484400190006280c10006400187060 (by decide +kernel)

def state245_2 : List Sig := roots 245
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude245_2 : Impossible true (goalAt 245) 8 state245_2.toFinset :=
  node_ok cuts245 [⟨state245_0,exclude245_0⟩,⟨state245_1,exclude245_1⟩] 0x40010e0601c0c0e06040010b03034240d09040010e06034240d09040010b0301c0c0a0604000ce0600c444e0604000cc0402c240b0904000ce0602c240b0904000cc0400c444c0604001070302c240b09040010d09040010d09040010703040010503040010d0902c240b09040018b0301c180706040008e06025210948480004b03025210948440018e0601c180706040010d09025210d09040010c4841c180c48440010d0901c180c09040010c48425210c0904000cb09025210b0904000ca4841c180a4844000cb0901c180a0904000ca48425210a09040000850519180646040000e06025240949040000850525240949040000e06019180646040000c48425240949040000d09019180d09040000c48419180c08440000d09025240949040000a48425240949040000b09019180b09040000a48419180a08440000b09025240949040000948419180948440000706025240949040000948425240949040000706019180646040018911118580616040004e06024640919040014911124640919040004e06018580616040010511124640919040010d09018580d09040010511118580616040010d0902464091904000c31112464091904000cb09018580b0904000c31111858061604000cb090246409190400081505216108584400049484246409190800001505246409190400049484216108584400001511246409190400009490216109490400001511216108584400009490246409190 (by decide +kernel)

theorem lower245 : Claim 245 9 :=
  fromSearch 132101 (by decide +kernel) exclude245_2

def cuts194 : Cuts (goalAt 194) := []

def state194_0 : List Sig := roots 194
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude194_0 : Impossible true (goalAt 194) 3 state194_0.toFinset :=
  node_ok cuts194 [] 0x30100420230100820230200c08030100c08030200820210808420220808424010900c04020a00828020808828020a00c04010900424010808828020a00c08010900c08010808424010900c08020a008280 (by decide +kernel)

theorem lower194 : Claim 194 4 :=
  fromSearch 285212768 (by decide +kernel) exclude194_0

theorem lower226 : Claim 226 5 :=
  fromLift 5 32 286261328 lower194 (by decide +kernel)

theorem lower210 : Claim 210 5 :=
  fromLift 5 16 285278272 lower194 (by decide +kernel)

def cuts162 : Cuts (goalAt 162) := []

def state162_0 : List Sig := roots 162
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude162_0 : Impossible true (goalAt 162) 3 state162_0.toFinset :=
  node_ok cuts162 [] 0x28080220228080820228200a08028080a08028200820208808220220808222008880a02020a00828020808828020a00a02008880222008808828020a00a08008880a08008808222008880a08020a008280 (by decide +kernel)

theorem lower162 : Claim 162 4 :=
  fromSearch 269484112 (by decide +kernel) exclude162_0

theorem lower178 : Claim 178 5 :=
  fromLift 5 16 269549632 lower162 (by decide +kernel)

def cuts82 : Cuts (goalAt 82) := []

def state82_0 : List Sig := roots 82
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude82_0 : Impossible true (goalAt 82) 3 state82_0.toFinset :=
  node_ok cuts82 [] 0x140401202140404202141005040140405040141004202048081202108081210048405010109004240108084240109005010048401210048084240109005040048405040048081210048405040109004240 (by decide +kernel)

theorem lower82 : Claim 82 4 :=
  fromSearch 16842816 (by decide +kernel) exclude82_0

theorem lower114 : Claim 114 5 :=
  fromLift 5 32 17891392 lower82 (by decide +kernel)

def rule242_0 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower226 none (by decide +kernel)

def rule242_1 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower210 none (by decide +kernel)

def rule242_2 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower178 none (by decide +kernel)

def rule242_3 : {c : Cut // CutGood (goalAt 242) c} :=
  ruleFor 242 lower114 none (by decide +kernel)

def cuts242 : Cuts (goalAt 242) := [rule242_0,rule242_1,rule242_2,rule242_3]

def state242_0 : List Sig := roots 242
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude242_0 : Impossible true (goalAt 242) 6 state242_0.toFinset :=
  node_ok cuts242 [] 0x40008e0601c0c0e06040008b03034240d09040008e06034240d09040008b0301c0c0a06040004e06008808e06040004c0402c240b09040004e0602c240b09040004c04008808c0604000470302c240b09040004d09040004d09040004703040008503040004d0902c240b09040000b0301c180706040000e06040000e06040000b0304000ca03040000e0601c180706040000d09004808d09040000c0801c180c08040000d0901c180c09040000c08004808c09040000b09014100b09040000a0801c180a08040000b0901c180a09040000a08014100a0904000c82021898062604000ce06024a4092904000c820224a4092904000ce06018980626040008420224a40929040008d09018980d09040008420218980626040008d09024a40929040004220224a40929040004b09018980b09040004220218980626040004b09024a40929040000120220a00828040000706024a40929040000120224a40929040000706020a008290 (by decide +kernel)

theorem lower242 : Claim 242 7 :=
  fromSearch 286326848 (by decide +kernel) exclude242_0

theorem lower195 : Claim 195 5 :=
  fromLift 5 1 102 lower194 (by decide +kernel)

theorem lower83 : Claim 83 5 :=
  fromLift 5 1 65606 lower82 (by decide +kernel)

def rule211_0 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower209 none (by decide +kernel)

def rule211_1 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower195 none (by decide +kernel)

def rule211_2 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower210 none (by decide +kernel)

def rule211_3 : {c : Cut // CutGood (goalAt 211) c} :=
  ruleFor 211 lower83 none (by decide +kernel)

def cuts211 : Cuts (goalAt 211) := [rule211_0,rule211_1,rule211_2,rule211_3]

def state211_0 : List Sig := roots 211
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude211_0 : Impossible true (goalAt 211) 6 state211_0.toFinset :=
  node_ok cuts211 [] 0x4000cc04014444c0404000c911134240d0904000cc04034240d0904000c911114444509040004911114100504040004c04040004c0404000491114000c811140004c04014100504040004d09004c0cd09040004c08014100c08040004d09014100c09040004c08004c0cc09040000830310900424040000c04024a40929040000830324a40929040000c04010900424040000430324a40929040000d09010900d09040000430310900424040000d09024a40929040000130320a00828040000504024a40929040000130324a40929040000504020a00829040008911110500414040008c04024640919040008911124640919040008c04010500414040008511124640919040008d09010500d09040008511110500414040008d090246409190400041303206008180400045040246409190400041303246409190400045040206008190400001311246409190400009290400009290400001311400001211400009290246409190 (by decide +kernel)

theorem lower211 : Claim 211 7 :=
  fromSearch 65606 (by decide +kernel) exclude211_0

theorem lower163 : Claim 163 5 :=
  fromLift 5 1 85 lower162 (by decide +kernel)

def cuts147 : Cuts (goalAt 147) := []

def state147_0 : List Sig := roots 147
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude147_0 : Impossible true (goalAt 147) 3 state147_0.toFinset :=
  node_ok cuts147 [] 0x24444830320444811104c44929024a40129020a00929024a408290244449190246408203206009190246408190246409290048449190 (by decide +kernel)

theorem lower147 : Claim 147 4 :=
  fromSearch 65607 (by decide +kernel) exclude147_0

def cuts51 : Cuts (goalAt 51) := []

def state51_0 : List Sig := roots 51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0xc444230308444211104c4432300c8c012300888032300c8c022300c44431300c4c022030848031300c4c021300c4c03230048443130 (by decide +kernel)

theorem lower51 : Claim 51 4 :=
  fromSearch 65605 (by decide +kernel) exclude51_0

def rule179_0 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower178 none (by decide +kernel)

def rule179_1 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower161 none (by decide +kernel)

def rule179_2 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower163 none (by decide +kernel)

def rule179_3 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower147 none (by decide +kernel)

def rule179_4 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower51 none (by decide +kernel)

def rule179_5 : {c : Cut // CutGood (goalAt 179) c} :=
  ruleFor 179 lower162 none (by decide +kernel)

def cuts179 : Cuts (goalAt 179) := [rule179_0,rule179_1,rule179_2,rule179_3,rule179_4,rule179_5]

def state179_0 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_0 : Impossible true (goalAt 179) 4 state179_0.toFinset :=
  node_ok cuts179 [] 0x24a40a0900c8c092900c8c0929024a40323004c0c929024a41000124640929004844919024640a0900c4c091900c4c0919024640313004c0c9190246401203280c0a09028240211108c0c8303 (by decide +kernel)

def state179_1 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_1 : Impossible true (goalAt 179) 4 state179_1.toFinset :=
  node_ok cuts179 [] 0x929028240323024a40323024a4092900c8c0919024a4012112464091902824031302464031302464091900c4c0211128240a09008444323024a40323024a40313024640313024640211128240211128240a030 (by decide +kernel)

def state179_2 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_2 : Impossible true (goalAt 179) 5 state179_2.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_1,exclude179_1⟩] 0x83030c8c03230280c0929024a40830324a409290280c032300c8c1000124a4092902824032302824100010c8c0323028240929024a40130320a00828040004929024a40130324a40929040004828020a4091110c4c03130280c09190246409111246409190280c031300c4c0131124640919024a41000524a40131140004121124a4091902464021112464091902824031302824021110c4c0313028240919024640130320600818004808919024640130324640919004808818020640a03008444a03024444a09028240a03028240a09024444211108445000240008a080280c01303280c08303800048303280c20000280c0830304c0c8111 (by decide +kernel)

def state179_3 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_3 : Impossible true (goalAt 179) 4 state179_3.toFinset :=
  node_ok cuts179 [] 0x323024a4092900c8c092900c8c0323024a40919024a4012112464031302464091900c4c091900c4c0313024640a03020444a0302044492900c8c092900c8c091900c4c091900c4c08111280c08111280c0a090 (by decide +kernel)

def state179_4 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_4 : Impossible true (goalAt 179) 5 state179_4.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_3,exclude179_3⟩] 0xa0300c444a03020444a09028240a03028240a0902044431110c446000108c0c230304c0ca09028242000028240a09004c0c230308444230324a4092902824032302824023030c8c0323028240929024a4100010c8c03230280c0929024a41000124a409290280c032300c8c0130308880222040004929024a40130324a409290400042220088c031112464091902824031302824031110c4c0313028240919024640131124640919024a41000524a40131140004121124a4091902464081110c4c03130280c09190246408111246409190280c031300c4c01303084802120048089190246401303246409190048082120084c1000240008a020 (by decide +kernel)

def state179_5 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_5 : Impossible true (goalAt 179) 4 state179_5.toFinset :=
  node_ok cuts179 [] 0x2c0c0a020280c0a0302c240a08028240a09020a00929024a4082900c8c0929024a40323024a40b0900c8c092902c0c0b0902c240311120640919024640818024640121124a4091900c4c091902464031302464031302c2409190 (by decide +kernel)

def state179_6 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_6 : Impossible true (goalAt 179) 5 state179_6.toFinset :=
  node_ok cuts179 [⟨state179_0,exclude179_0⟩,⟨state179_5,exclude179_5⟩] 0xb03028080a030280c0b09028200a0902824013034000a000004c0c828024a40929020a40323024a4092900c8c092902c240323024a40131124a40929004c44818024640919020640919024a4012112464031302464091900c4c091902c24031302464200012464091904000091112c0c0b0904000c3111 (by decide +kernel)

def state179_7 : List Sig := roots 179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude179_7 : Impossible true (goalAt 179) 6 state179_7.toFinset :=
  node_ok cuts179 [⟨state179_2,exclude179_2⟩,⟨state179_4,exclude179_4⟩,⟨state179_6,exclude179_6⟩] 0x40010b0300c444b0304000c91112c240b09080008b0302c240b0904000c91110c444311140008b03004c0cb03040008a02040008a02040008b03080004a03040008a02004c0ca03040008b09004c0cb09040008a08040008a08040008b09080000a09040008a08004c0ca0904000483030c8c0323040004b03024a40929040004830324a40929040004b0300c8c0323040004230324a40929040004b0900c8c0b0904000423030c8c0323040004b09024a40929040008130320a00828040009000124a40929040008130324a40929040009000220a0082904000091110c4c0313040000b03024640919040000911124640919040000b0300c4c0313040000311124640919040000b0900c4c0b0904000031110c4c0313040000b090246409190400001303206008180400001202246409190400001303246409190400001202206008190400001311246409190400009290400009290400001311400041211400009290246409190 (by decide +kernel)

theorem lower179 : Claim 179 7 :=
  fromSearch 65605 (by decide +kernel) exclude179_7

theorem lower115 : Claim 115 6 :=
  fromLift 6 1 65605 lower114 (by decide +kernel)

theorem lower227 : Claim 227 6 :=
  fromLift 6 1 85 lower226 (by decide +kernel)

def rule243_0 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower241 none (by decide +kernel)

def rule243_1 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower242 none (by decide +kernel)

def rule243_2 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower211 none (by decide +kernel)

def rule243_3 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 none (by decide +kernel)

def rule243_4 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower115 none (by decide +kernel)

def rule243_5 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower227 none (by decide +kernel)

def rule243_6 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower114 none (by decide +kernel)

def rule243_7 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower225 none (by decide +kernel)

def rule243_8 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower241 (some (1,input 4,input 7)) (by decide +kernel)

def rule243_9 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower83 none (by decide +kernel)

def rule243_10 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower161 none (by decide +kernel)

def rule243_11 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower163 none (by decide +kernel)

def rule243_12 : {c : Cut // CutGood (goalAt 243) c} :=
  ruleFor 243 lower179 (some (1,input 4,input 7)) (by decide +kernel)

def cuts243 : Cuts (goalAt 243) := [rule243_0,rule243_1,rule243_2,rule243_3,rule243_4,rule243_5,rule243_6,rule243_7,rule243_8,rule243_9,rule243_10,rule243_11,rule243_12]

def state243_0 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_0 : Impossible true (goalAt 243) 7 state243_0.toFinset :=
  node_ok cuts243 [] 0x4001100041c0c0703040010a03030240c09040011000c30240c09040010a0301c0c0508040030706010c0c70604002c130330240c09040030706030240c0904002c130310c0c411140024703028240a09040024c09040024c09040024703040030503040024c09028240a09040010a0300c444a03040010811128240a09040010a03028240a0904001081110c444311140024706008c0c706040024504028240a09040024706028240a09040024504008c0c50604002c430324a4092904001cc09018980c0904002843031898062604001cc09024a40929040024230324a4092904001ca09018980a0904002423031898062604001ca09024a40929040011000418980626040010a03024a40929040011000824a40929040010a0301898062604002013031898062604001c706024a40929040020130324a4092904001c706018980626040018511124640919040018c09018580c09040018511118580616040018c09024640919040018311124640919040018a09018580a09040018311118580616040018a0902464091904001c13112464091904001892904001892904001813114002012114001c929024640919040010811118580616040010a03024640919040010811124640919040010a03018580616040018130318580616040018706024640919040018130324640919040018706018580616040011000440014e060 (by decide +kernel)

def state243_1 : List Sig := [0xffff0000ffff0000ffff0000ffff0000,input 7,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_1 : Impossible true (goalAt 243) 7 state243_1.toFinset :=
  node_ok cuts243 [] 0x40010e0601c0c0e06040010a02030240c09040010e06030240c09040010a0201c0c0a06040024703028240a09040024c09040024c0904002470304002c503040024c09028240a09040010e0600c444e06040010c04028240a09040010e06028240a09040010c0400c444c0604001c430324a4092904001cc09018980c0904001c43031898062604001cc09024a4092904001c230324a4092904001ca09018980a0904001c23031898062604001ca09024a40929040010830318980626040010e06024a40929040010830324a40929040010e06018980626040018511124640919040018c09018580c09040018511118580616040018c09024640919040018311124640919040018a09018580a09040018311118580616040018a0902464091904001c13112464091904001c92904001c92904001c13114001c12114001c929024640919040010830318580616040010e06024640919040010830324640919040010e06018580616040014703004c0c703040014c0901c180c0904001470301c180706040014c09004c0cc09040014311114100504040014a0901c180a0904001431111c180706040014a09014100a0904001432301c180706040014929004c0c929040014323004c0c32304001492901c18092904001431301c180706040014919004c0c919040014313004c0c31304001491901c180919040011000540010a030 (by decide +kernel)

def state243_2 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_2 : Impossible true (goalAt 243) 7 state243_2.toFinset :=
  node_ok cuts243 [] 0x100041c0c070302c0c0d09034241000b34240d0902c0c0703014241000b10c0c43034000cd09034241000b34240d0904000c430310c0c70302c240b0903424100093424070304002c503034240b0902c240b0300c444b03024444b0902c240b0302c240b0902444431110c445000908c0c230340008b0902c24100092c240b09040008230308c0c430324a40929034240626034240430318980626034240929024a40230324a4092902c24062602c24023031898062602c240929024a4100041898062602c0c0929024a41000724a4092902c0c0626018981000520a0082804001c929024a41000724a40929040014828020a41000718980626040000929024a41000724a4092904000062601898051112464091903424061603424051111858061603424091902464031112464091902c24061602c24031111858061602c240919024640131124640919024a41000724a4013114001c121124a4091902464091111858061602c0c091902464091112464091902c0c0616018581000520600818040018919024641000624640919040014818020641000618580616040004919024641000624640919040004616018581000440014e06034241000b34240c08040014c08034241000b30240c08040014c0902c24100092c240a08040014a0802c241000928240a08040014a0902c0c100042c0c10005400110005400110004280c10004400107060 (by decide +kernel)

def state243_3 : List Sig := roots 243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude243_3 : Impossible true (goalAt 243) 8 state243_3.toFinset :=
  node_ok cuts243 [⟨state243_0,exclude243_0⟩,⟨state243_1,exclude243_1⟩,⟨state243_2,exclude243_2⟩] 0x4000ce0601c0c0e0604000cb03034240d0904000ce06034240d0904000cb0301c0c0a06040008e0600c444e06040008c0402c240b09040008e0602c240b09040008c0400c444c0604000c70302c240b0904000cd0904000cd0904000c70304000c50304000cd0902c240b09040010b0301c180706040014e06080004e06080008b03080000a03040010e0601c18070604000cd09004c0cd0904000cc0801c180c0804000cd0901c180c0904000cc08004c0cc09040008b09014100b09040008a0801c180a08040008b0901c180a09040008a08014100a09040000830318980626040000e06024a40929040000830324a40929040000e06018980626040000430324a40929040000d09018980d09040000430318980626040000d09024a40929040000230324a40929040000b09018980b09040000230318980626040000b09024a40929040000130320a00828040000706024a40929040000130324a40929040000706020a00829040004911118580616040004e06024640919040004911124640919040004e06018580616040004511124640919040004d09018580d09040004511118580616040004d09024640919040004311124640919040004b09018580b09040004311118580616040004b090246409190400041303206008180400047060246409190400041303246409190400047060206008190400001311246409190400009290400009290400001311400001211400009290246409190 (by decide +kernel)

theorem lower243 : Claim 243 9 :=
  fromSearch 65605 (by decide +kernel) exclude243_3

theorem lower230 : Claim 230 6 :=
  fromLift 6 4 286262608 lower226 (by decide +kernel)

theorem lower198 : Claim 198 5 :=
  fromLift 5 4 285214304 lower194 (by decide +kernel)

theorem lower86 : Claim 86 5 :=
  fromLift 5 2 16843840 lower84 (by decide +kernel)

def rule214_0 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower210 none (by decide +kernel)

def rule214_1 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower212 none (by decide +kernel)

def rule214_2 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower198 none (by decide +kernel)

def rule214_3 : {c : Cut // CutGood (goalAt 214) c} :=
  ruleFor 214 lower86 none (by decide +kernel)

def cuts214 : Cuts (goalAt 214) := [rule214_0,rule214_1,rule214_2,rule214_3]

def state214_0 : List Sig := roots 214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude214_0 : Impossible true (goalAt 214) 6 state214_0.toFinset :=
  node_ok cuts214 [] 0x4000cc04014040c0404000c860634240d0904000cc04034240d0904000c86061404050904000d00031410050404000cc0402521094844000d00022521094844000cc04014100504040008d09025210d09040008c48414100c48440008d09014100c09040008c48425210c09040000860611100444040000c04025240949040000860625240949040000c04011100444040000c48425240949040000d09011100d09040000c48411100c08440000d0902524094904000094841110094844000050402524094904000094842524094904000050401110044404000c86061090042404000cc04024a4092904000c860624a4092904000cc04010900424040004460624a40929040004d09010900d09040004460610900424040004d09024a40929040008160621a10868440008948424a40929040008160624a40929040008948421a10868440001000024a40929040000949021a10949040001000121a10868440000949024a409290 (by decide +kernel)

theorem lower214 : Claim 214 7 :=
  fromSearch 285279296 (by decide +kernel) exclude214_0

theorem lower182 : Claim 182 6 :=
  fromLift 6 4 269550656 lower178 (by decide +kernel)

theorem lower118 : Claim 118 6 :=
  fromLift 6 2 17892416 lower116 (by decide +kernel)

theorem lower166 : Claim 166 5 :=
  fromLift 5 4 269485392 lower162 (by decide +kernel)

def cuts150 : Cuts (goalAt 150) := []

def state150_0 : List Sig := roots 150
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude150_0 : Impossible true (goalAt 150) 3 state150_0.toFinset :=
  node_ok cuts150 [] 0x5818948425210148405040949025240149025210949025240120604840929024a40129021a10929024a40868424a40949021a109290 (by decide +kernel)

theorem lower150 : Claim 150 4 :=
  fromSearch 268502080 (by decide +kernel) exclude150_0

def rule246_0 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower242 none (by decide +kernel)

def rule246_1 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower244 none (by decide +kernel)

def rule246_2 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower230 none (by decide +kernel)

def rule246_3 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower214 none (by decide +kernel)

def rule246_4 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower182 none (by decide +kernel)

def rule246_5 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower118 none (by decide +kernel)

def rule246_6 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower116 none (by decide +kernel)

def rule246_7 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower166 none (by decide +kernel)

def rule246_8 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower226 none (by decide +kernel)

def rule246_9 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower240 none (by decide +kernel)

def rule246_10 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower210 none (by decide +kernel)

def rule246_11 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower212 none (by decide +kernel)

def rule246_12 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower178 none (by decide +kernel)

def rule246_13 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower114 none (by decide +kernel)

def rule246_14 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower162 none (by decide +kernel)

def rule246_15 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower180 none (by decide +kernel)

def rule246_16 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower84 none (by decide +kernel)

def rule246_17 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower194 none (by decide +kernel)

def rule246_18 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower86 none (by decide +kernel)

def rule246_19 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower150 none (by decide +kernel)

def rule246_20 : {c : Cut // CutGood (goalAt 246) c} :=
  ruleFor 246 lower198 none (by decide +kernel)

def cuts246 : Cuts (goalAt 246) := [rule246_0,rule246_1,rule246_2,rule246_3,rule246_4,rule246_5,rule246_6,rule246_7,rule246_8,rule246_9,rule246_10,rule246_11,rule246_12,rule246_13,rule246_14,rule246_15,rule246_16,rule246_17,rule246_18,rule246_19,rule246_20]

def state246_0 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 4,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_0 : Impossible true (goalAt 246) 6 state246_0.toFinset :=
  node_ok cuts246 [] 0xe0601c0c0e0602c0c0d09034240e06034240d0902c0c0703028180e06008818e06030100b0902c240e0602c240b0903010022063018070302c240b09034241000b34240703040038503034240b0902c240820619180646038180929024a40820624a40929038180646019180c48424a40929034240646034240c48419180c08434240929024a40a48424a4092902c24064602c240a48419180a0842c240929024a40120619180646040024929024a40120624a40929040020646021a40868419180868440000929024a40868424a40929040000646019180b03004818b03038181000638180b03040018b03038180120638180d09004818d09031211000831210d09040038d09031210120631210b09004818b09029211000829210b0904002cb0902921012062921100014000492842c0c1000d2c0c0e06021a1086842c0c0868421a10e06040034e06034240868434240c48440038c28434241000e34240c48421a1086842c24086842c240a4844002ca2842c241000b2c240a48421a108684 (by decide +kernel)

def state246_1 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_1 : Impossible true (goalAt 246) 5 state246_1.toFinset :=
  node_ok cuts246 [] 0x2c0c070601c180c0602521094842c0c0948425210c0601c1807060140c0948424a1086841c1808684140c070601c18086842521086842c24094842c240a4841c180a4842c240706028240a48425210a09020818626018980c06025240949020818949025240c06018980626025210626025210706025240949025210949025240706018980626021a10949024a40503018980929021a10626021a10503025240949029210949025240b09018980b09029210626028210b09025240949030180503030180b03021a10868430180868421a10b030140c0a06008818868434240b090140c0b090088185030140c0b09021a10b0903018022063018082062c240b09030180b0902c2408206088182484 (by decide +kernel)

def state246_2 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 6,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_2 : Impossible true (goalAt 246) 6 state246_2.toFinset :=
  node_ok cuts246 [⟨state246_1,exclude246_1⟩] 0xe06008818e06030100b0902c240e0602c240b09030100220630181000c2c240b09010819000c10819000b40032000010818b0902c241000b2c240b09021a10220621a11000b08818220621a10b0902c240b0301c180706038180948425210b0302521094843818070601c180b09025210b09029210706029210b0901c180a09029210948428241000c2521094841081870601c181000e1c180706010818948425211000f25210928421a10706021a11000e1c180706021a10948421a10820618980626038180949025240820625240949038180626018980a4842524094902c24062602c240a48418980a0842c24094902524094841898094841c18094902524094842524094901c180626018980420625240949040024626018980420618980626040030949025240868425240929040000626024a40868418980868440000949025240e06010818e0602c0c100062c0c0e06040018e0602c0c042062c0c1000140004d09038181000d38180b03021a10868438180868421a10b03040034b030 (by decide +kernel)

def state246_3 : List Sig := [0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_3 : Impossible true (goalAt 246) 5 state246_3.toFinset :=
  node_ok cuts246 [] 0x70602521094841c180b09029210a09028240503025210948440044820621a10868430180868424a10120621a1086842c24022062c240626040030c0602c240b0901921064602918082061918094841c180948419180a4842c240a4842c240949030180b03028180a06034240b09029210b090 (by decide +kernel)

def state246_4 : List Sig := [0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_4 : Impossible true (goalAt 246) 5 state246_4.toFinset :=
  node_ok cuts246 [] 0x70602521094841c18094841c18070602521094841c180706025210928421a10706021a10626025240949018980948425240949018980949018980626025240949018980626025240929024a40868425240c0602c0c0a0602818042064002cc06020818c06008818b09030180868421a110010 (by decide +kernel)

def state246_5 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_5 : Impossible true (goalAt 246) 6 state246_5.toFinset :=
  node_ok cuts246 [⟨state246_1,exclude246_1⟩,⟨state246_3,exclude246_3⟩,⟨state246_4,exclude246_4⟩] 0x2c0c070601c180c0602521094842c0c0948425210c0601c1807060140c094842521100111c1807060140c070601c181000c2521094842c24094842c240a4841c180a4842c240706028240a48425210a09020819001020818c06021a10868420818868421a10c0604002cc06004818868421a1094844002c928404819000e04818948421a10868440031000c24a41000c21a108684140c1000c140c1000b400320000140c0868421a10220621a1086842c241000b2c24022068000822062c24086842c24082061918064603018094902524082062524094903018064601918094841918094841c18094902524094842524094901c180646019181000c252409490140c06460191820001191806460140c0949025240a4842524094902c24064602c240a48419180a0842c240949025240c060140c0c0602c0c1000c2c0c0c06040040a0602c0c0503028181000c40028d0903018022063018082062c240b09030180b0902c2408206088182484 (by decide +kernel)

def state246_6 : List Sig := [0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 4,input 1,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_6 : Impossible true (goalAt 246) 6 state246_6.toFinset :=
  node_ok cuts246 [] 0xe06034240d09028180e0602c240b09030180b0903424050302c240820621a1086843818086843424042063424086842c24022062c240868424a10120621a10929040020b03025210948438180d09031210d09025210b09029210b0902521070600d0c0949025240e06025240d09031210949025240b090292109490252109490090c064602c0c0e0602c0c0e06034240c08034240c0802c240a0802c240a080 (by decide +kernel)

def state246_7 : List Sig := [0xffff0000ffff0000fcfc0000fcfc0000ffff0000ffff0000fcfc0000fcfc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6,input 1,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_7 : Impossible true (goalAt 246) 5 state246_7.toFinset :=
  node_ok cuts246 [] 0xe06028240a09030180a09034240503028240820621a10868438180868428240220628240868434240420634240929038180d09034240508019180949025240646025240a09029210949025240d0903021094901c180948425210706025210a09029210a09021a10120621a10928430240c09031210d090191809490252109490 (by decide +kernel)

def state246_8 : List Sig := [0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 6,input 1,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_8 : Impossible true (goalAt 246) 6 state246_8.toFinset :=
  node_ok cuts246 [⟨state246_3,exclude246_3⟩,⟨state246_7,exclude246_7⟩] 0xe0602c240b09030180b0903121200002c240b09029210a4842c24070602521094841c180b09029210a09028240948431210706025212000125210948440020820621a1086843818086842c24022062c240868424a10120621a10868430a10420621a10626040030e06031210c48411210d09019180e06020818646029210b09029210b09025210706025210646031210646030210949038180b03038180b030 (by decide +kernel)

def state246_9 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,input 4,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_9 : Impossible true (goalAt 246) 7 state246_9.toFinset :=
  node_ok cuts246 [⟨state246_0,exclude246_0⟩,⟨state246_2,exclude246_2⟩,⟨state246_5,exclude246_5⟩,⟨state246_6,exclude246_6⟩,⟨state246_8,exclude246_8⟩] 0x40034e0601c0c0e06040018b03034240d09040018e06034240d09040034b0301c0c0a06040034e06008818e06040018c0402c240b09040018e0602c240b09040034c04008818c0604003070302c240b09040028d0904002cd0904002c703080008503040030d0902c240b09040034b0301c180706040018e06025210948440018b03025210948440034e0601c180706040030d09025210d09040020c4841c180c48440038d0901c180c09040020c48425210c09040028b09025210b09040020a4841c180a4844002cb0901c180a09040020a48425210a09040004820640034820640004e06021a10868440004820621a10868440004e06040004e06040004420621a10868440004d09040004d09040004420680004420640004d09021a10d09040004220621a10868440004b09040004b0904000422064002c220640004b09021a10b09040004120621a10868440004948440004928440004120680000120640004948421a10868440001000040000929040034820619180646040018e06025240949040018820625240949040034e06019180646040030c48425240949040024d09019180d09080010c48419180c08440030d09025240949040028a4842524094904002cb09019180b0904002ca48419180a08440028b0902524094904002094841918094844002470602524094908000c9484252409490400207060191806460 (by decide +kernel)

def state246_10 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 7,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_10 : Impossible true (goalAt 246) 6 state246_10.toFinset :=
  node_ok cuts246 [] 0xb09025210b09029210706029210b0901c180a0902921094842824100071c18070602818094842521100072521094842818070601c18050300581850304001c94842521050302521094844001c16060581894841918094841c18094902524094842524094901c180646019180a4842524094902c24064602c240a48419180a0842c240949025241001219180646028180949025241000c25240949028180646019181000c0d0c03430140c0949025241000c252409490140c034300d0c0160621a10868425210929024a40160624a40929025210868421a11000c24a40929025240868425241001021a10868425240929024a40260624a4092902c24062602c24026061898062602c240929024a41001218980626028180929024a41001024a4092902818062601898100100c8c03230140c0929024a41001024a409290140c032300c8c0a06009818a0604004cb0902c240a0602c240b0904004826061c24050300981850304000cb0902c24050302c240b0904000c260609819000440010b030 (by decide +kernel)

def state246_11 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_11 : Impossible true (goalAt 246) 6 state246_11.toFinset :=
  node_ok cuts246 [⟨state246_1,exclude246_1⟩] 0xb0301c180706030180948425210b0302521094843018070601c180b09025210b09029210706029210b0901c180a0902921094842824050302521094844001c70601c18050301c18070604001c94842521086061918064603018094902524086062524094903018064601918094841918094841c18094902524094842524094901c180646019180a4842524094902c24064602c240a48419180a0842c240949025241000c252409490140c0646019181000c191806460140c0949025240c06009818c06021818b0902c240c0602c240b09021818260609210860618980626030181000b2898086064004086063018062601898016061898062602521100072521016064001c160625210626025211000c18980626025241000c25241000b4003200002524062602524026064004c26062c24062602c24026061898062602c241000b2c241000440010929030180503030180b03040040b03030181001028180b030140c0a06009819000334240b090140c0b090098185030140c0b0904000cb090 (by decide +kernel)

def state246_12 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 7,input 6,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_12 : Impossible true (goalAt 246) 6 state246_12.toFinset :=
  node_ok cuts246 [] 0x94841c18070602521070602521094841c180b09029210a0902824016062521094840581894842524094901918094901918064602524064602524094901918094902c240a08425240141025240949005040868424a40929021a10929025240868424a40929018980626024a40626024a4092901898092902c240626024a40121024a40929004840c0602c0c0a06028180d09040048860630180b090092102606 (by decide +kernel)

def state246_13 : List Sig := [0xffffffffffffffffffffffffcccccccc,input 1,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_13 : Impossible true (goalAt 246) 5 state246_13.toFinset :=
  node_ok cuts246 [] 0x94841c180706025210b09029210a0902824094842524094901918094901918064602524094902c240a08425240d09021a10929024a40868424a40949021a10929024a40626018980929024a40b0901898092901c18094841c180948419180949019180949028180a06030180b03009210b09030180b090189809290189809290 (by decide +kernel)

def state246_14 : List Sig := [0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,input 1,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_14 : Impossible true (goalAt 246) 6 state246_14.toFinset :=
  node_ok cuts246 [⟨state246_4,exclude246_4⟩,⟨state246_13,exclude246_13⟩] 0x70602521094841c18094841c18070602521094841c18070602521094841c180706025210646025240949019180948425240949019180949019180646025240949019180646025240949019180646025240c0602c0c0a0602818046064002cc06021818c06009818b09018980c0602181862601898094840c8c094841898094908000094900c8c06260189803230098186260048c09290301820001301810012 (by decide +kernel)

def state246_15 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,input 1,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_15 : Impossible true (goalAt 246) 7 state246_15.toFinset :=
  node_ok cuts246 [⟨state246_5,exclude246_5⟩,⟨state246_10,exclude246_10⟩,⟨state246_11,exclude246_11⟩,⟨state246_12,exclude246_12⟩,⟨state246_14,exclude246_14⟩] 0x4001cb0301c18070604001cc0602521094844001cb0302521094844001cc0601c18070604001050302521094844001100071c18070604001050301c18070604001100042521094844001cb09025210b0904001ca4841c180a4844001cb0901c180a0904001ca48425210a09040048860619180646040030c06025240949040030860625240949040048c0601918064604001c94841918094844001c70602524094904001c94842524094904001c706019180646040011000425240949040010503019180646040011000c19180646040010503025240949040030a48425240949040030b09019180b09040030a48419180a08440030b0902524094904004886061898062604002cc06024a40929040040860624a40929040048c0601898062604001c160621a1086844001c948424a4092904001c160624a4092904001c948421a10868440031000c24a40929040030949021a10949040032000021a10868440030949024a40929040011000424a40929040010503018980626040012000218980626040010503024a4092904004c260624a4092904002cb09018980b0908001026061898062604002cb09024a40929040010c060140c0c06040010b03040010b03040010c06080004a06040010b030140c0a0604000d00034000cd09040048c06009818c0604004c86062c240b0908000cc0602c240b090400488606098182484 (by decide +kernel)

def state246_16 : List Sig := [0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc,input 1,input 4,input 2,input 5,input 6,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_16 : Impossible true (goalAt 246) 7 state246_16.toFinset :=
  node_ok cuts246 [⟨state246_0,exclude246_0⟩] 0xe0601c0c0e0602c0c0d09034240e06034240d0902c0c0703028180e06009818e06030100b0902c240e0602c240b0903010026063018070302c240b0903424100073424070304001c503034240b0902c240860619180646038180949025240860625240949038180646019180c48425240949034240646034240c48419180c08434240949025240a4842524094902c24064602c240a48419180a0842c240949025240160619180646004808949025240160625240949004808646019181000819180646040000949025241000825240949040000646019180b03005818b03038181000238180b03040018b03038180160638180d09005818d09031211000231210d0904001cd09031210160631210b09005818b09029211000229210b09040050b0902921016062921100014000494842181832300c8c0e06024a40929021818929024a40e0600c8c0e06011818929024a40d09040004d09011819000711818d09024a40929009818929024a40b0900c8c0b0900981832300c8c0b09024a40929040004929024a40949040004949040005000880000949024a40929005819000205819000124a40929040005000120a4100014000886842c0c100052c0c0e06040018e0602c0c100062c0c0e06040014e06034241000434240c4844001cc48434241000734240c48440010c4842c24100032c240a48440050a4842c24100142c240a4844000ca484 (by decide +kernel)

def state246_17 : List Sig := [0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,input 1,input 6,input 2,input 4,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_17 : Impossible true (goalAt 246) 7 state246_17.toFinset :=
  node_ok cuts246 [⟨state246_2,exclude246_2⟩,⟨state246_11,exclude246_11⟩] 0xe06009818e06030100b0902c240e0602c240b0903010026063018100042c240b09011819000411819000b40012000111818b0902c241000b2c240b0904000c260609819000b0981826064000cb0902c240b0301c180706038180948425210b0302521094843818070601c180b09025210b09029210706029210b0901c180a0902921094842824100042521094841181870601c18100071c18070601181894842521100072521094844000870601c18100071c180706040008948425210860619180646038180949025240860625240949038180646019180a4842524094902c24064602c240a48419180a0842c24094902524094841918094841c18094902524094842524094901c180646019180460625240949010808646019180460619180646010808949025241000c25240949040000646019181000c19180646040000949025240e06011818e0602c0c100042c0c0e06040018e0602c0c046062c0c1000440004d09021818626018980e06040004e06021819000621818e06018980626009818424010900b09018980b09009818626018980b09010900b09005818626018980948440004948405819000705818948418980948440004626018980949040004949040005000c80000949018980949011819000411819000118980626040011000408981000440010929038181000538180b03040018b03038181000638180b03040014b030 (by decide +kernel)

def state246_18 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_18 : Impossible true (goalAt 246) 7 state246_18.toFinset :=
  node_ok cuts246 [] 0x100051c0c070302c0c0d09034241000734240d0902c0c0703014241000711818460640010d09034241000734240d0904001046061181870302c240b0903424100073424070304001c503034240b0902c240b03009818b03040048b0902c240b0302c240b0904001426060981900120981826064000cb0902c24100122c240b0904000c260609818c48425240949034240646034240c48419180c08434240949025240a4842524094902c24064602c240a48419180a0842c24094902524100051918064602c0c0949025241000d2524094902c0c0646019180948419180948440034949025240948425240949040008646019181000d19180646040000949025241000d25240949040000646019180460624a40929034240626034240460618980626034240929024a40260624a4092902c24062602c24026061898062602c240929024a41000d24a40929025240868425241000621a10868425240929024a4100051898062602c0c0929024a41000624a4092902c0c0626018981000221a10868425210929024a41000624a40929025210868421a11000618980626040004929024a41000624a40929040004626018981000540008e06034240948434240c48440008c48434241000730240c48425210c0902c24094842c240a48440008a4842c241001228240a48425210a0902c0c100052c0c10002252109484400150005280c10005400147060 (by decide +kernel)

def state246_19 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_19 : Impossible true (goalAt 246) 7 state246_19.toFinset :=
  node_ok cuts246 [⟨state246_10,exclude246_10⟩] 0xe06009818e06030100b0902c240e0602c240b0903010026063018100042c240b09034241000434241001240012000034240b0902c24100120981826064000cb0902c24100122c240b0904000c260609818b09025210b09029210706029210b0901c180a0902921094842824100051c18070603818094842521100072521094843818070601c180d09025210d09031210706031210d0901c180c09031210948430241000705818160640008948425211000725210948440008160605818a4842524094902c24064602c240a48419180a0842c24094902524094841918094841c18094902524094842524094901c180646019181000519180646038180949025241000d25240949038180646019180c48425240949034240646034240c48419180c08434240949025241000d0d0c0343040000949025241000d2524094904000034300d0c0260624a4092902c24062602c24026061898062602c240929024a40160621a10868425210929024a40160624a40929025210868421a11000d24a40929025240868425241000621a10868425240929024a41000518980626038180929024a41000624a40929038180626018981000424a40929034240626034241000618980626034240929024a4100060c8c0323040004929024a41000624a4092904000432300c8c1000440010b03038181000538181000434240d090400110004281810004400147030 (by decide +kernel)

def state246_20 : List Sig := roots 246
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude246_20 : Impossible true (goalAt 246) 8 state246_20.toFinset :=
  node_ok cuts246 [⟨state246_9,exclude246_9⟩,⟨state246_15,exclude246_15⟩,⟨state246_16,exclude246_16⟩,⟨state246_17,exclude246_17⟩,⟨state246_18,exclude246_18⟩,⟨state246_19,exclude246_19⟩] 0x40014e0601c0c0e06040010b03034240d09080014e06034240d09040010b0301c0c0a0604000ce06009818e0604000cc0402c240b0904000ce0602c240b0904000cc04009818c0604000c70302c240b0904000cd0904000cd0904000c70308000450304000cd0902c240b09040014b0301c180706040008e06025210948480010b03025210948440014e0601c180706040010d09025210d09040008c4841c180c4844001cd0901c180c09040010c48425210c0904000cb09025210b0904000ca4841c180a4844000cb0901c180a0904000ca48425210a09040000860619180646040000e06025240949040000860625240949040000e06019180646040000c48425240949040000d09019180d09040000c48419180c08440000d09025240949040000a48425240949040000b09019180b09040000a48419180a08440000b09025240949040000948419180948440000706025240949040000948425240949040000706019180646040014860618980626040004e06024a40929040018860624a40929040014e06018980626040010460624a40929040004d09018980d0908000c460618980626040010d09024a4092904000c260624a4092904000cb09018980b0904000c26061898062604000cb09024a40929040008160621a10868440004948424a40929080008160624a40929040004948421a10868440001000024a40929040000949021a10949040002000021a10868440000949024a409290 (by decide +kernel)

theorem lower246 : Claim 246 9 :=
  fromSearch 286327872 (by decide +kernel) exclude246_20

theorem lower167 : Claim 167 6 :=
  fromLift 6 1 1365 lower166 (by decide +kernel)

theorem lower151 : Claim 151 5 :=
  fromLift 5 1 66631 lower150 (by decide +kernel)

theorem lower55 : Claim 55 5 :=
  fromLift 5 2 66629 lower53 (by decide +kernel)

def rule183_0 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 none (by decide +kernel)

def rule183_1 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 none (by decide +kernel)

def rule183_2 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower182 none (by decide +kernel)

def rule183_3 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower166 none (by decide +kernel)

def rule183_4 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower167 none (by decide +kernel)

def rule183_5 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower151 none (by decide +kernel)

def rule183_6 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower150 none (by decide +kernel)

def rule183_7 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_8 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower165 none (by decide +kernel)

def rule183_9 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower163 none (by decide +kernel)

def rule183_10 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower162 none (by decide +kernel)

def rule183_11 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower161 none (by decide +kernel)

def rule183_12 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (1,input 4,input 5)) (by decide +kernel)

def rule183_13 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower147 none (by decide +kernel)

def rule183_14 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower55 none (by decide +kernel)

def rule183_15 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 0,input 5)) (by decide +kernel)

def rule183_16 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower178 none (by decide +kernel)

def rule183_17 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (3,input 0,input 5)) (by decide +kernel)

def rule183_18 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 0,input 7)) (by decide +kernel)

def rule183_19 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower53 none (by decide +kernel)

def rule183_20 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower51 none (by decide +kernel)

def rule183_21 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_22 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower179 (some (1,input 5,input 7)) (by decide +kernel)

def rule183_23 : {c : Cut // CutGood (goalAt 183) c} :=
  ruleFor 183 lower181 (some (2,input 5,input 7)) (by decide +kernel)

def cuts183 : Cuts (goalAt 183) := [rule183_0,rule183_1,rule183_2,rule183_3,rule183_4,rule183_5,rule183_6,rule183_7,rule183_8,rule183_9,rule183_10,rule183_11,rule183_12,rule183_13,rule183_14,rule183_15,rule183_16,rule183_17,rule183_18,rule183_19,rule183_20,rule183_21,rule183_22,rule183_23]

def state183_0 : List Sig := [0xcfcfcfcfcfcfcccccfcfcfcfcfcfcccccfcfcfcfcfcfcccccfcfcfcfcfcfcccc,input 1,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_0 : Impossible true (goalAt 183) 5 state183_0.toFinset :=
  node_ok cuts183 [] 0xc4c0919024640313024640a0900c4c09190216109190246408584246409290048449190216109190246409490280c0a09028240211129210a03025210948405200323024a4092900c8c0929028240323024a40130724a40929021a4086840d0c0949025240343025240343028240949004c1c9490252409484 (by decide +kernel)

def state183_1 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0x303030303030000030303030303000003030303030300000303030303030000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_1 : Impossible true (goalAt 183) 4 state183_1.toFinset :=
  node_ok cuts183 [] 0x31302464091900c4c0858424640919021610919028240313024640a0302521094840520032302524094900c8c0919021610919025240210725240868424a409290280c0a09028240211121a10a090282408684 (by decide +kernel)

def state183_2 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0x303030303030000030303030303000003030303030300000303030303030000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_2 : Impossible true (goalAt 183) 4 state183_2.toFinset :=
  node_ok cuts183 [] 0x280c0a09028240211129210a0302521094840520034302524094900d0c094900d0c0a09025241000b2464085842464092900c4c0919024640313024640a0900c4c09190216109190246408584 (by decide +kernel)

def state183_3 : List Sig := [0x303030303030000030303030303000003030303030300000303030303030000,input 1,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_3 : Impossible true (goalAt 183) 5 state183_3.toFinset :=
  node_ok cuts183 [⟨state183_1,exclude183_1⟩,⟨state183_2,exclude183_2⟩] 0x31302464091900c4c0919028240313024640858424640919021610919021a12000124640a03028240a09008444a484280c0948425210148020c1c868421a10a03021a10a09080000a09021a10928404c1c86840d0c094902524034302464085842464094902524034302824094904002c9290 (by decide +kernel)

def state183_4 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_4 : Impossible true (goalAt 183) 4 state183_4.toFinset :=
  node_ok cuts183 [] 0xa0302521094840520034302524094900d0c012072464085842464094902524034302824094900c4c091902464031302161091902464085842464092900c4c09190280c0a09028240121129210a090282409484 (by decide +kernel)

def state183_5 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 1,0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_5 : Impossible true (goalAt 183) 5 state183_5.toFinset :=
  node_ok cuts183 [⟨state183_2,exclude183_2⟩,⟨state183_4,exclude183_4⟩] 0xa03028240a09008444a484280c094842521014800d0c094902524034302524034302824094900481c9490800001211252409190216109190252401211280c08107280c012112824200012824016072521012112521092900c4c0919024640313024640a0900c4c09190216109190246408584 (by decide +kernel)

def state183_6 : List Sig := [0x2222222222222222222222222222222222222222222222222222222222222222,input 1,0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_6 : Impossible true (goalAt 183) 5 state183_6.toFinset :=
  node_ok cuts183 [] 0xa03028240a09008444a484280c094842521014800d0c094902524034302524034302824094900481c929021a10929025240919021610919025240323024a4092900c8c0929028240323024a40868424a40929021a1031302464091900c4c09190282403130246408584246409190216101211 (by decide +kernel)

def state183_7 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_7 : Impossible true (goalAt 183) 5 state183_7.toFinset :=
  node_ok cuts183 [⟨state183_1,exclude183_1⟩,⟨state183_4,exclude183_4⟩] 0xc4c0919024640313021610919024640858424640323080004919024640a0900c4c09190280c094842521014800d0c0949025240343024640858424640949004c1c94908000032302524094900d0c0a090252403230248c083070c8c01707252103230252109290280c0a09028240211129210a090282409484 (by decide +kernel)

def state183_8 : List Sig := [0x3333333300000000333333330000000033333333000000003333333300000000,input 1,0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_8 : Impossible true (goalAt 183) 5 state183_8.toFinset :=
  node_ok cuts183 [] 0x31302464091900c4c0858424640919021610919024a40121124640a0302521094840520034302524094900d0c0919021610919025240130724a40868424a40949025240343028240949004c44929024a40329021a10929024a408684280c0a0902824021112824091900c4c09190292103230 (by decide +kernel)

def state183_9 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_9 : Impossible true (goalAt 183) 6 state183_9.toFinset :=
  node_ok cuts183 [⟨state183_0,exclude183_0⟩,⟨state183_3,exclude183_3⟩,⟨state183_5,exclude183_5⟩,⟨state183_6,exclude183_6⟩,⟨state183_7,exclude183_7⟩,⟨state183_8,exclude183_8⟩] 0x20c1c32300c8c0a03024a40929020c1c929024a40a0300c8c0323080014929024a40a0900c8c0a0908001032300c8c0a09024a40929005c1c868421a10948424a40929005c1c929024a40948421a1086842444431300c4c0a03024640919024444919024640a0300c4c0313004c4491902464092908000c929004c46000204844929024640919008444919024640a0900c4c0a0900844431300c4c0a09024640919005c1c858421610948424640919005c1c9190246409484216108584280c02111280c0911128240a090280c0a09028240911108444211140025000929210a03005c1ca03020c1c948425210a03025210948420c1c170705200a0300d0c0343020c1c949025240a03025240949020c1c34300d0c0929025240929021a12000121a10929080000929021a10949025240919025240919021610151121610919005444919021610949025240a0902524094904002434300d0c0a0900d0c0a090400309490252410009400241307 (by decide +kernel)

def state183_10 : List Sig := [0xffffffffffff0000ffffffffffff000000000000000000000000000000000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_10 : Impossible true (goalAt 183) 6 state183_10.toFinset :=
  node_ok cuts183 [] 0x25240a0900d0c094900d0c0949025240343005c1c94902524013070d0c0949025240343024a40949021a10929024a40a0900c8c092900c8c0929024a40323021a10929024a40868421a10929024a40868424640949021610919024640929004844919024640a0900c4c091900c4c0919024640313021610919024640858421610919024640858408444a09028240211109c1c211128240a09008444170721c1c1484280c09484 (by decide +kernel)

def state183_11 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_11 : Impossible true (goalAt 183) 5 state183_11.toFinset :=
  node_ok cuts183 [] 0xd0c0949025240343025210949025240230724a40949021a1092900c8c0929024a40323021a10929024a4086842464094902161091902464092900484491900c4c09190246403130216109190246408584280c0948425210148425240343025240a09024a40323024a40a09024640313024640a09008444a09028240a03025210a09028240a484 (by decide +kernel)

def state183_12 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_12 : Impossible true (goalAt 183) 5 state183_12.toFinset :=
  node_ok cuts183 [] 0x94902824034302524034302524094900d0c0948425240949004c1c929025240868424a40929028240323024a40323024a4092900c8c0868424a40929021a10a03028240a09008444a484280c0948425210148424640858425240919024640121124a4091902464031302824091900c4c09190246403130216109190246408584 (by decide +kernel)

def state183_13 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_13 : Impossible true (goalAt 183) 5 state183_13.toFinset :=
  node_ok cuts183 [] 0x94902824034302524034302524094900d0c0948425240949004c1c91902524085842464091902824031302464031302464091900c4c0858424640919021610a03028240a09008444a484280c0948425210148424a40868425240929024640121124640929024a4032302824092900c8c0929024a40323021a10929024a408684 (by decide +kernel)

def state183_14 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_14 : Impossible true (goalAt 183) 5 state183_14.toFinset :=
  node_ok cuts183 [] 0x929028240323024a40323024a4092900c8c0868424a40929021a10919024a4012112464091902824031302464031302464091900c4c0858424640919021610a03028240a09008444a484280c0948425210148424a40868424a4094902464085842464094902524034302824094900d0c0949025240343004c1c9490252409484 (by decide +kernel)

def state183_15 : List Sig := [0xfcfcfcfcfcfcccccfcfcfcfcfcfcccccfcfcfcfcfcfcccccfcfcfcfcfcfccccc,0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_15 : Impossible true (goalAt 183) 4 state183_15.toFinset :=
  node_ok cuts183 [] 0x24640a0900c4c091900c4c0919024640313004c1c9190246401207246409290048449190280c0a09028240211108c1c830724a40a0900c8c092900c8c0929024a40323004c1c929024a41000b (by decide +kernel)

def state183_16 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000,0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_16 : Impossible true (goalAt 183) 5 state183_16.toFinset :=
  node_ok cuts183 [⟨state183_15,exclude183_15⟩] 0x929028240323024a40323024a4092900c8c0130724a4092904002c929025242000024a40919024a4012112464091902824031302464031302464091900c4c013072464091900481c919025240141124640a03028240a09008444230720c1c94902824034302524034302524094900d0c01707 (by decide +kernel)

def state183_17 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_17 : Impossible true (goalAt 183) 6 state183_17.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩,⟨state183_12,exclude183_12⟩,⟨state183_13,exclude183_13⟩,⟨state183_14,exclude183_14⟩,⟨state183_16,exclude183_16⟩] 0x94902824034302524034302524094900d0c0948425240949080012000325240949040024929025240868424a40929028240323024a40323024a4092900c8c0868424a40929021a12000224a40929040020919025240858424640919024a4012112464091902824031302464031302464091900c4c085842464091902161200012464091904000ca03028240a09008444a484800008707280c09484052101707 (by decide +kernel)

def state183_18 : List Sig := [0xfcfcfcfcfcfcccccfcfcfcfcfcfcccccfcfcfcfcfcfcccccfcfcfcfcfcfccccc,0xffffffffffff0000ffffffffffff0000,input 7,input 5,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_18 : Impossible true (goalAt 183) 4 state183_18.toFinset :=
  node_ok cuts183 [] 0x91902824031302464031302464091900c4c0919024a40121124640211128240a09008444313024640313024640211128240211128240a0300c8c092900c8c0929024a40a0900c8c092900c8c0929024a403230 (by decide +kernel)

def state183_19 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000,0xffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_19 : Impossible true (goalAt 183) 5 state183_19.toFinset :=
  node_ok cuts183 [⟨state183_18,exclude183_18⟩] 0x929028240323024a40323024a4092900c8c0929025242000024a40919024a4012112464091902824031302464031302464091900c4c0919025240141124640211128240a09008444323024a40323024a40313024640313024640211128240211128240a0300d0c094900d0c0949025240a0900d0c094900d0c09490252403430 (by decide +kernel)

def state183_20 : List Sig := [0xffffffffffff0000ffffffffffff0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_20 : Impossible true (goalAt 183) 6 state183_20.toFinset :=
  node_ok cuts183 [⟨state183_19,exclude183_19⟩] 0x25240a0900d0c094900d0c0949025240343025210949025242000024a40949021a10929024a40a0900c8c092900c8c0929024a40323021a10929024a40868424640949021610919024640929004844919024640a0900c4c091900c4c0919024640313021610919024640858408444a0902824021112921097072521087070d0c094900d0c094900c8c092900c8c092900c4c091900c4c0919008444a09008444a090280c01707 (by decide +kernel)

def state183_21 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_21 : Impossible true (goalAt 183) 5 state183_21.toFinset :=
  node_ok cuts183 [] 0xd0c0949025240343029210949025240a08425240a0900d0c0949024a40949021a1092900c8c0929024a40323021a10929024a40868424a40a09021a1092902464094902161091902464092900484491900c4c0919024640313021610919024640858424640a090216109190280c0a484292103484280c0a09028240211129210a090282409484 (by decide +kernel)

def state183_22 : List Sig := [0xf0f0f0f0f0f0fffff0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_22 : Impossible true (goalAt 183) 5 state183_22.toFinset :=
  node_ok cuts183 [] 0x929028240323024a40323024a4092900c8c0868424a40929021a10929025240868424a40919024a4012112464091902824031302464031302464091900c4c0858424640919021610919025240858424640a03028240a09008444a484280c0948425210148025240a0900d0c094900d0c09490252403430252109490252401307 (by decide +kernel)

def state183_23 : List Sig := [0xffff000000000000ffff00000000000000000000000000000000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 7,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_23 : Impossible true (goalAt 183) 6 state183_23.toFinset :=
  node_ok cuts183 [⟨state183_21,exclude183_21⟩,⟨state183_22,exclude183_22⟩] 0x94902824034302524034302524094900d0c0170725240949004c1c929025240868424a40929028240323024a40323024a4092900c8c0868424a40929021a10919025240858424640919024a4012112464091902824031302464031302464091900c4c0858424640919021610a03028240a09008444270725c1ca03005c1d000925242000125240868424a40868424a40858424640858424642000021c1c9484 (by decide +kernel)

def state183_24 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_24 : Impossible true (goalAt 183) 5 state183_24.toFinset :=
  node_ok cuts183 [] 0x94842524094900481c34302524094900d0c0949028240343025240929025240868424a40868424a40929021a10323024a4092900c8c0929028240323024a40a03025210948420444a484280c0a09028240211124640858425240919024640121124a4091902161091902464085840c4c09190246403130246403130282409190 (by decide +kernel)

def state183_25 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_25 : Impossible true (goalAt 183) 6 state183_25.toFinset :=
  node_ok cuts183 [⟨state183_24,exclude183_24⟩] 0x2521094902524013070d0c0949025240343025240a0900d0c0949005444949025240151124a40949021a10929021a10929024a4086840c8c0929024a40323024a40a0900c8c0929004c44929024a4013112464094902161091902464092900484491902161091902464085840c4c0919024640313024640a0900c4c09190800009190246410003280c0948425210170705c1c948425210170724444a484280c0a090400142111 (by decide +kernel)

def state183_26 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_26 : Impossible true (goalAt 183) 6 state183_26.toFinset :=
  node_ok cuts183 [] 0x2521094902524013070d0c094902524034302524034300d0c0949024a40949021a10929021a10929024a4086840c8c0929024a40323024a4032300c8c092902464094902161091902464092900484491902161091902464085840c4c091902464031302464031300c4c09190280c0948425210170709c1ca111280c0211125240343025240343024a40323024a40323024640313024640313025210170725210170724444a090 (by decide +kernel)

def state183_27 : List Sig := [0xf0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_27 : Impossible true (goalAt 183) 5 state183_27.toFinset :=
  node_ok cuts183 [] 0x323024a4092900c8c0929028240323024a40868424a40929021a10a03028240a09008444a484280c094842521014800c4c0919024640313024640929004844919024640a0900c4c091902161091902464085840d0c0949025240343024a40868424a40949025240343028240949004c1c9490252409484246408584246409490 (by decide +kernel)

def state183_28 : List Sig := [0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_28 : Impossible true (goalAt 183) 6 state183_28.toFinset :=
  node_ok cuts183 [⟨state183_27,exclude183_27⟩] 0x34302524094900d0c0949028240343025240170725240949004c1e000025240949040024323024a4092900c8c0929025240868424a40929028240323024a40868424a40929021a10868424a40929021a10a03028240a0900844427074000ca03021c1ca0302044494840c4c0919024640313024640949005044919024640929004844919024640a0900c4c0919005c1c9190206408584280c08606280c08606 (by decide +kernel)

def state183_29 : List Sig := [0x5555555555550000555555555555000055555555555500005555555555550000,input 0,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_29 : Impossible true (goalAt 183) 6 state183_29.toFinset :=
  node_ok cuts183 [] 0xd0c0949025240343025240a0900d0c0949005c1c94902524013070c8c0929024a40323024a40949021a10929024a40a0900c8c0929021a10929024a408684280c0a09028240211109c1ca03021c1ca030204449111216108584280c0818025240858425240858424a40131124a40858428240211128240958405c1c8584280c09111280c0911125240151125240151124a40868424a408684282402111282402111252109190 (by decide +kernel)

def state183_30 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_30 : Impossible true (goalAt 183) 5 state183_30.toFinset :=
  node_ok cuts183 [] 0x2521094902524013070d0c0949025240343024a40949021a10929021a10929024a4086840c8c0929024a403230280c0948425210811124640949021610919024640929004c4491902161091902464085840c4c0919024640313025240343025240a09024a40323024a40a09025210a09028240a48408444a09028240a03024640313024640a090 (by decide +kernel)

def state183_31 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_31 : Impossible true (goalAt 183) 6 state183_31.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩] 0x25240a0900d0c094902521094902524013070d0c094902524034300d0c0949025240343024a40949021a10929024a40a0900c8c0929021a10929024a4086840c8c0929024a4032300c8c0929024a40323029210211128240a09008446000028240a09040014911125210948420444160625210948405818a03024640949021610919024640929004c44919024640a0900844491902161091902464085842444491902181c3130 (by decide +kernel)

def state183_32 : List Sig := [0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_32 : Impossible true (goalAt 183) 6 state183_32.toFinset :=
  node_ok cuts183 [] 0x25240a0900d0c094902521094902524013070d0c0949025240343024a40949021a10929024a40a0900c8c0929021a10929024a4086840c8c0929024a40323029210211128240a09008444911125210948420444313025240141125240313024a40121124a40211128240313028240170725210313025210a13024444313025240343025240343024a40323024a403230282402111282402111252101707252101707280c09190 (by decide +kernel)

def state183_33 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_33 : Impossible true (goalAt 183) 7 state183_33.toFinset :=
  node_ok cuts183 [⟨state183_9,exclude183_9⟩,⟨state183_10,exclude183_10⟩,⟨state183_17,exclude183_17⟩,⟨state183_20,exclude183_20⟩,⟨state183_23,exclude183_23⟩,⟨state183_25,exclude183_25⟩,⟨state183_26,exclude183_26⟩,⟨state183_28,exclude183_28⟩,⟨state183_29,exclude183_29⟩,⟨state183_31,exclude183_31⟩,⟨state183_32,exclude183_32⟩] 0x4003087070d0c0343040024a03025240949040030870725240949040024a0300d0c0343040015000c25240949040024a0900d0c0a09040035000c0d0c0343040014a0902524094904003094848000094844002413032524094904003094842524094904002413034003013074001c87070c8c0323040020a03024a4092904001c870724a40929040020a0300c8c0323040025000724a40929040020949021a1094904002d000721a10868440024949024a40929040015000724a40929040020a0900c8c0a0904001d00070c8c0323040014a09024a4092904001c170721a10868440020948424a4092904001c170724a40929040020948421a1086848002891110c4c031304000ca0302464091908002491112464091904000ca0300c4c031304002415112464091904000c94902161094904002815112161085844002494902464091904002013112464091904000c92904001c92904001c13114001c12114000c92902464091904001421112464091904000ca0900c4c0a0904001821110c4c0313040014a0902464091908002017072161085844000c94842464091908001c17072464091904000c948421610858480018a03008444a03040014911128240a09080014a03028240a09040014911108444211140011000440010a48480010a03005c1ca0308000c870725210948480008a03025210948480004870705c1c1484 (by decide +kernel)

def state183_34 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_34 : Impossible true (goalAt 183) 5 state183_34.toFinset :=
  node_ok cuts183 [] 0x34302524094900d0c0949028200a08425240929025240868424a40323024a4092900c8c0929029210323024a4094902521094900d0c0929021a10929021a109111252109484280c0a090246408584246408584280c0a48429210348424640858425240919024640121124a4091900c4c09190246403130246403130292109190 (by decide +kernel)

def state183_35 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_35 : Impossible true (goalAt 183) 6 state183_35.toFinset :=
  node_ok cuts183 [⟨state183_34,exclude183_34⟩] 0xd0c0949025240343025240a08028210949005444949025240151124a40949021a1092900c8c0929024a40323024a40a4840c8c0929004c44929024a4013112464094902161091902464092900484491900c4c0919024640313024640a4840c4c0919080000919024641000325240948425240343024a40868424a40868424640858424640858405c1c948425210a03028240170725210948405c1c9111280c0a4840d2102707 (by decide +kernel)

def state183_36 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_36 : Impossible true (goalAt 183) 6 state183_36.toFinset :=
  node_ok cuts183 [] 0xd0c094902524034302524034300d0c0949024a40949021a1092900c8c0929024a40323024a4032300c8c092902464094902161091902464092900484491900c4c091902464031302464031300c4c0919025240948425240343024a40868424a40868424640858424640858405c1c948425210a03008444170725210948405c1ca707280c0270725240343025240343024a40323024a40323024640313024640313024444a484 (by decide +kernel)

def state183_37 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff0000,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_37 : Impossible true (goalAt 183) 7 state183_37.toFinset :=
  node_ok cuts183 [⟨state183_35,exclude183_35⟩,⟨state183_36,exclude183_36⟩] 0x4002487070d0c0343040024a03025240949040024870725240949040024a0300d0c0343040014a48425240949040024a0800d0c0a08040024a4840d0c0a08440014a0802524094904002087070c8c0323040020a03024a40929040020870724a40929040020a0300c8c0323040025000924a40929040024949021a10949040025000821a10868440024949024a40929040014270724a40929040020a4840c8c0a4844002027070c8c0323040014a48424a4092904000c91110c4c031304000ca0302464091904000c91112464091904000ca0300c4c031304002415112464091904002494902161094904002415112161085844002494902464091904000c13112464091904000c92904000c92904000c13114002012114000c92902464091904001427072464091904000ca4840c4c0a4844000c27070c4c0313040014a48424640919080004a03009c1ca03040014911129210a48480000a03029210a48440014911109c1c348440010911105c1c911140010a03025210948440010911125210948440010a03005c1ca03040010949004c0c949040010343025210948440010949025210949040010343004c0c343040010929025210929040010868405c1c868440010929005c1c929040010868425210868440010919025210919040010858405c1c858440010919005c1c91904001085842521085844001100044001ca090 (by decide +kernel)

def state183_38 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 7,input 5,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_38 : Impossible true (goalAt 183) 5 state183_38.toFinset :=
  node_ok cuts183 [] 0x2c240a48428240a0902c0c0948425210a03025210949025240243025240b0902821094900d0c0949025240343021a10929024a40868424a40949021a10929024a40b0900c8c092900c8c0929024a4032302c0c0b0902c240248421610919024640858424640858425240919024640121124a4091902464031302c24091900c4c09190246403130 (by decide +kernel)

def state183_39 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,input 7,input 0,input 5,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_39 : Impossible true (goalAt 183) 6 state183_39.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩] 0xb09029210a09028240b030252109484280c01606252109484058189484252409490090c094902c240a0842524034302524094900d0c0141025240949005040868424a40929021a10929025240868424a4092902c240323024a40323024a4092900c8c0121024a40929004840b0302c240b09009210260621610919024640858424640949021610919024640929004c44919024640b0900c4c091900c4c09190246403130800008606 (by decide +kernel)

def state183_40 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_40 : Impossible true (goalAt 183) 5 state183_40.toFinset :=
  node_ok cuts183 [] 0x24640858424640a0900c4c094842521081300c44494842521021112521094902524024302524091902161091900d0c0949025240313005444949025240151121a10929024a40868424a40949021a10929024a4091900c8c091900c8c0929024a40313004c44929024a4013110c4c091902464024840c44491902464086070c44431300c4c02607 (by decide +kernel)

def state183_41 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 5,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_41 : Impossible true (goalAt 183) 6 state183_41.toFinset :=
  node_ok cuts183 [⟨state183_40,exclude183_40⟩] 0x2521027070844494842464085842464085842444494842521081110c4c094842521021302521094902524024302524034300d0c094902524091902161091900d0c094902524034300d0c0949025240313021a10929024a40868424a40949021a10929024a4032300c8c0929024a4091900c8c091900c8c0929024a4032300c8c0929024a4031302c24031112444600000c44431300c44431300981c91112464091902181c313024640919040014b030 (by decide +kernel)

def state183_42 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_42 : Impossible true (goalAt 183) 6 state183_42.toFinset :=
  node_ok cuts183 [⟨state183_40,exclude183_40⟩] 0x2c240a48428240a0902c0c0948425210a0300c444948425210211125210949025240243025240b0902821094900d0c0949025240343005444949025240151121a10929024a40868424a40949021a10929024a40b0900c8c092900c8c0929024a40323004c44929024a4013110848094840c4c094840c4c094900544494900c4c0929004c449290246403130244c200000c4c031110c4c031300981cb0302c240b0900921031112c240b090400089111 (by decide +kernel)

def state183_43 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,input 0,input 5,input 1,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_43 : Impossible true (goalAt 183) 7 state183_43.toFinset :=
  node_ok cuts183 [⟨state183_39,exclude183_39⟩,⟨state183_41,exclude183_41⟩,⟨state183_42,exclude183_42⟩] 0xb03005c1cb03028080948425210b030252109484280801707280c0311125210948409c1d000309c1c311140018211109c1c948425211000325210948440010170705c1d000305c1c17074001094842521087070d0c034302c0c094902524087072524094902c0c034300d0c0948409080948404c0c949025240948425240949004c0c2420090c027072524094900c44434300d0c027070d0c034300c44494902524100102524094904000434300d0c100100d0c034304000494902524087070c8c032302c0c0929024a40870724a4092902c0c032300c8c0170721a10868425210929024a40170724a40929025210868421a11001024a40929025240868425241000f21a10868425240929024a40270724a4092900c44432300c8c027070c8c032300c444929024a41000624a4092904000032300c8c1000f0c8c0323040000929024a40b0300c444b03024445000624444b03080008b0302444431110c445000240008b0902444431300c4c0b03040008b03024446000124444b0300c4c0313005c1c21200848094840c4c0948405c1c31300c4c094840848094840544431300c4c094904000894900544500100544494900c4c0949004c4431300c4c0929040008929004c45000f04c4492900c4c092900c44500050c44500020c4c031304000900020981d00024001491902c0c1000e2c0c086064001886062c0c200002c0c08606400388606 (by decide +kernel)

def state183_44 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffff5555ffff0000ffff5555ffff0000ffff5555ffff0000ffff5555ffff0000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_44 : Impossible true (goalAt 183) 4 state183_44.toFinset :=
  node_ok cuts183 [] 0x280c0a090282403111280c0948425210148428240a4842824094840c4c0919024640313024640a0900c4c091902161091902464085842464092902161091900d0c0949025240343025240a0900d0c0949025210949025241000b (by decide +kernel)

def state183_45 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 1,0xffff5555ffff0000ffff5555ffff0000ffff5555ffff0000ffff5555ffff0000,input 5,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_45 : Impossible true (goalAt 183) 5 state183_45.toFinset :=
  node_ok cuts183 [⟨state183_44,exclude183_44⟩] 0x34302524094900d0c094902824034302524094842524094900481ca03028240a0900c444a03025210948405210a09029210a090252101211280c08507280c012112524200002524012112824025072824016072521012112521092900c4c0919024640313024640949021610919024640a0900c4c09190216109190246408584 (by decide +kernel)

def state183_46 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,0xffff5555ffff0000ffff5555ffff0000ffff5555ffff0000ffff5555ffff0000,input 0,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_46 : Impossible true (goalAt 183) 5 state183_46.toFinset :=
  node_ok cuts183 [⟨state183_44,exclude183_44⟩] 0xa03028240a0900c44431302464091900c4c0919028240313024640858424640919021610919021a12000024640919025240858424640a03025210948405210a09029210a09025210830721a108684280c0868428240230728240868424a10130721a1092900d0c0949025240343025240a0900d0c0949025210949025241000b (by decide +kernel)

def state183_47 : List Sig := [0xf0f05050f0f00000f0f05050f0f00000f0f05050f0f00000f0f05050f0f0000,0xffff5555ffff0000ffff5555ffff0000ffff5555ffff0000ffff5555ffff0000,input 0,input 5,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_47 : Impossible true (goalAt 183) 5 state183_47.toFinset :=
  node_ok cuts183 [] 0x323024a4092900c8c0929028240323024a40868424a40929021a10a03028240a0900c44431302464091900c4c0919024a40121124640919028240313024640858424640919021610a03025210948405200a09029210a0902521034302524094900d0c0929021a1092902524094900d0c0a090252409190216109190252401307 (by decide +kernel)

def state183_48 : List Sig := [0xffff5555ffff0000ffff5555ffff0000ffff5555ffff0000ffff5555ffff0000,input 0,input 5,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_48 : Impossible true (goalAt 183) 6 state183_48.toFinset :=
  node_ok cuts183 [⟨state183_45,exclude183_45⟩,⟨state183_46,exclude183_46⟩,⟨state183_47,exclude183_47⟩] 0x21c1c34300d0c0a03025240949021c1c949025240a0300d0c0343009c1c949025240a0900d0c0a09009c1c34300d0c0a09025240949025212000225210130325240949025210949025240130340034130721c1c32300c8c0a03024a40929021c1c929024a40a0300c8c0323040034929024a40949021a10949080004868421a10949024a40929009c1c929024a40a0900c8c0a09009c1c32300c8c0a09024a40929005c1c868421a10948424a40929005c1c929024a40948421a108684280c03111280c0911128240a090280c0a0902824091110c44431112444431300c4c0a03024640919024444919024640a0300c4c0313005444919024640949021610949005444858421610949024640919004c4491902464092904000c929004c4600000484492902464091900c444919024640a0900c4c0a0900c44431300c4c0a09024640919005c1c858421610948424640919005c1c9190246409484216108584280c01707280c08707252109484280c0948425210870705c1c148428240948428240270740010a484282410004282402707252109484 (by decide +kernel)

def state183_49 : List Sig := [0xffffffffffffffffffffffffffffffff55555555000000005555555500000000,input 7,input 0,input 5,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_49 : Impossible true (goalAt 183) 6 state183_49.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩] 0xb09029210a09028240b030252109484280c0170725210948405c1c9484252409490090c094902c240a0842524034302524094900d0c0151125240949005444868424a40929021a10929025240868424a4092902c240323024a40323024a4092900c8c0131124a40929004c44b0302c240b0900921031112c240b0900c444858424640919021610919025240858424640919024a4012112464091902c240311124640b1302464091902c0c200002464091900c4c09111 (by decide +kernel)

def state183_50 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,0x5555555555555555555555555555555500000000000000000000000000000000,0x5555555500000000555555550000000055555555000000005555555500000000,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_50 : Impossible true (goalAt 183) 5 state183_50.toFinset :=
  node_ok cuts183 [] 0xc444948425210211125210949025240243005044949025240141121a10929024a40868424a40949021a10929004844929024a40121129210b09028240a0902c24094902821094902c24092900c8c092900c4c091902c24091900981ca1902464091902161091902161094902464091900c8c09290246408607 (by decide +kernel)

def state183_51 : List Sig := [0x5555555555555555555555555555555500000000000000000000000000000000,input 7,0x5555555500000000555555550000000055555555000000005555555500000000,input 5,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_51 : Impossible true (goalAt 183) 6 state183_51.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩,⟨state183_50,exclude183_50⟩] 0x2521027070844494842444494842521081112521094902524024302524034300d0c094900d0c0949025240343021a10929024a40868424a40949021a10929024a4032300c8c092900c8c0929024a4032300c4449111800043111084c094840c4c094840c4c094900d0c094900c4c092900c8c092902c240313024444b1300c4c031302464200002464085842464091902161091902161094902464091900c8c092902464091900c444b19024640b030 (by decide +kernel)

def state183_52 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 7,0x5555555500000000555555550000000055555555000000005555555500000000,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_52 : Impossible true (goalAt 183) 6 state183_52.toFinset :=
  node_ok cuts183 [⟨state183_50,exclude183_50⟩] 0xb030252109484280c03111252109484084449484252409490090c034302524094900d0c0151125240949005444868424a40929021a10929025240868424a40323024a4092900c8c0131124a40929004c44858424640919028640919025240858424640919024a4012112464200002464091900c640311124640919040008a4842c240a09028240b09025240a08425240b09024a40323024a4031302c0c0b0902c2402484098189111 (by decide +kernel)

def state183_53 : List Sig := [0x5555555500000000555555550000000055555555000000005555555500000000,input 0,input 5,input 1,input 2,input 4,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_53 : Impossible true (goalAt 183) 7 state183_53.toFinset :=
  node_ok cuts183 [⟨state183_48,exclude183_48⟩,⟨state183_49,exclude183_49⟩,⟨state183_51,exclude183_51⟩,⟨state183_52,exclude183_52⟩] 0xb03005c1cb03028080948425210b030252109484280801707280c0311125210948409c1d000509c1c311140014211109c1c94842521087070d0c034302c0c094902524087072524094902c0c034300d0c0948409080948404c0c949025240948425240949004c0c2420090c027072524094900c44434300d0c027070d0c034300c44494902524087070c8c032302c0c0929024a40870724a4092902c0c032300c8c0170721a10868425210929024a40170724a40929025210868421a11001024a40929025240868425241001121a10868425240929024a40270724a4092900c44432300c8c027070c8c032300c444929024a40b0300c444b03024445000524444b0308000cb0302444431110c44491118000891112c0c091902464091112464091902c0c100022c0c0170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024640131124640919024a41000224a40131140044121124a40919024641000240008b1900c44500050c44500022464091902c0c1000e2c0c091114001491112c0c200012c0c091114001491114001500044001094844001494844001500038000094844001094840d0c100010d0c094904001494900d0c100100d0c094904000494900c8c100000c8c092904001492900c8c100110c8c092904000092904000900022c2410005400083130 (by decide +kernel)

def state183_54 : List Sig := [0xffffffff00000000ffffffff00000000aaaaaaaa00000000aaaaaaaa,input 5,input 0,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_54 : Impossible true (goalAt 183) 6 state183_54.toFinset :=
  node_ok cuts183 [⟨state183_30,exclude183_30⟩] 0xb030252109484280c094840981a0000252109484252409490090c034302524094900d0c094900d0c0343025240868424a40929021a10929025240868424a40323024a4092900c8c092900c8c0323024a40858424640919021610919025240858424640919024a4013112464031302464091900c4c091900c4c0313024640b03024444b0302444494840581894840581894900d0c094900d0c092900c8c092900c8c091112c0c091112c0c091900c4c091900c4c0b090 (by decide +kernel)

def state183_55 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_55 : Impossible true (goalAt 183) 6 state183_55.toFinset :=
  node_ok cuts183 [⟨state183_40,exclude183_40⟩] 0x2c0c0948425210a0302c240a48428240a0902444494842521081112521094902524024300d0c0949025240343025240b09028210949005444949025240151121a10929024a40868424a40949021a1092900c8c0929024a40323024a40b0900c8c0929004c44929024a40131121610919024640858424640949021610919024640929004c4491900c4c091902c24200002464091112464091902181c91112c0c0b03040008b0302c240b090092103111 (by decide +kernel)

def state183_56 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_56 : Impossible true (goalAt 183) 6 state183_56.toFinset :=
  node_ok cuts183 [] 0xb030252109484280c0948409c1c2111252109484252409490090c034302524094900d0c094900d0c0343025240868424a40929021a10929025240868424a40323024a4092900c8c092900c8c0323024a40858424640919021610919025240858424640919024a4013112464031302464026060c44491902c0c031112c0c0260625210911125210811125240343025240343024a40323024a40323024640911124640860721818b090 (by decide +kernel)

def state183_57 : List Sig := [0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 7,input 1,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_57 : Impossible true (goalAt 183) 7 state183_57.toFinset :=
  node_ok cuts183 [⟨state183_41,exclude183_41⟩,⟨state183_31,exclude183_31⟩,⟨state183_39,exclude183_39⟩,⟨state183_54,exclude183_54⟩,⟨state183_55,exclude183_55⟩,⟨state183_56,exclude183_56⟩] 0x200050c444311124444b0902c24200042c240b0902444431110c446000309818260640014b0902c24200022c240b09040014260609818b09025210b09029211000329210b09080004a09029210948428240911105c1c911121c1c948425210911125210948421c1c170720445000305818160640010948425211000325210948440010160605818a4842524094902c24034302c240a4840d0c0a0842c240949025240948409080948404c0c949025240948425240949004c0c2420090c087070d0c034302444494902524087072524094902444434300d0c100100d0c034304000494902524100102524094904000434300d0c0270724a4092902c24032302c24027070c8c032302c240929024a40170721a10868425210929024a40170724a40929025210868421a11001024a40929025240868425241001221a10868425240929024a4087070c8c0323024444929024a40870724a4092902444432300c8c100120c8c0323040000929024a41001224a4092904000032300c8c1000240008b0300c444919024640b09040008b0900c44600000c444b09024640919005c1c858421610948424640919005c1c919024640948421610858405444919024640949021610949005444858421610949024640919004c44919024640929040008929004c45001204c44929024640919024445000e2444500022464091904000900022181d0002400383130 (by decide +kernel)

def state183_58 : List Sig := [0xffffffff55555555ffffffff55555555ffffffff00000000ffffffff00000000,input 5,input 0,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_58 : Impossible true (goalAt 183) 6 state183_58.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩] 0xb030252109484280c0b09029210a09028240170725210948405c1c9484252409490090c034302524094900d0c094902c240a08425240151125240949005444868424a40929021a10929025240868424a40323024a4092900c8c092902c240323024a40131124a40929004c44212025210313025210313025240141125240313024a40121124a4031302c0c091110c4c0b1902c24031302c24200000c4c0919024640b0302c240b0900921031112c0c091112c0c09111 (by decide +kernel)

def state183_59 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_59 : Impossible true (goalAt 183) 6 state183_59.toFinset :=
  node_ok cuts183 [⟨state183_50,exclude183_50⟩] 0xb09029210a090282409111252109484204449484252409490090c094902c240a08425240151125240949005444868424a40929021a10929025240868424a4092902c240323024a40131124a40929004c44212025210313025210313025240141125240313024a40121124a4200002c24031302c24091110c4c031304000894842c0c09484280c094900d0c094900d0c092900c8c092900c8c091902c240b0302c2402484218183111 (by decide +kernel)

def state183_60 : List Sig := [0x5555555555555555555555555555555500000000000000000000000000000000,input 0,input 7,input 1,input 2,input 4,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_60 : Impossible true (goalAt 183) 7 state183_60.toFinset :=
  node_ok cuts183 [⟨state183_51,exclude183_51⟩,⟨state183_32,exclude183_32⟩,⟨state183_58,exclude183_58⟩,⟨state183_59,exclude183_59⟩] 0x1000e0c444311124444b0902c24200032c240b0902444431110c444b09025210b09029211000329210b09080004a09029210948428240911105c1c911121c1c948425210911125210948421c1c170720444a4842524094902c24034302c240a4840d0c0a0842c240949025240948409080948404c0c949025240948425240949004c0c2420090c087070d0c034302444494902524087072524094902444434300d0c0270724a4092902c24032302c24027070c8c032302c240929024a40170721a10868425210929024a40170724a40929025210868421a11001024a40929025240868425241001321a10868425240929024a4087070c8c0323024444929024a40870724a4092902444432300c8c031118000031112c24031302c24031110c4c031302c24100022c24017070848021202521031302521017070c4c031302521021202521015110c4c031302524100022524015114004014112524031302524013110c4c0313024a41000224a4013114004c121124a40313024a41000240008b13024445000e2444500020c4c031302c24100052c24031114003831112c24200022c240311140014311125211000425210170740038170725211000325210170740010170725241000125240343040038343025241001025240343040004343024a41000024a40323040038323024a41001324a4032304000032304000900022c0c1000e400089190 (by decide +kernel)

def state183_61 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,input 4,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_61 : Impossible true (goalAt 183) 6 state183_61.toFinset :=
  node_ok cuts183 [] 0x20c1c32300c8c0b03024a40929020c1c929024a40b0300c8c0323009c1c929024a40b0900c8c0b09009c1c32300c8c0b09024a40929005c1c868421a10948424a40929005c1c929024a40948421a1086842444431300c4c0b03024640919024444919024640b0300c4c0313004c4491902464092904002c929004c45000b0484492902464091900c444919024640b0900c4c0b0900c44431300c4c0b09024640919005c1c858421610948424640919005c1c91902464094842161085842c0c031112c0c091112c240b0902c0c0b0902c24091110c44424802c0c017072c0c0a0202521094842c0c0948425210a02005c1ca0302c24094842c240a48440024a4842c241000c28240a48425210a0902c0c034300d0c083072524094902c0c094902524083070d0c0343024a40949024a4086844002c868424a41000b24a4086842524094902464094902464085840544485842464015112464085842524094902c240949025240a4840d0c0a0842c24034302c240a484252409490400242420090c09484252409490400309490252409484090809484 (by decide +kernel)

def state183_62 : List Sig := [0x5555555555555555555555555555555555555555555500005555555555550000,input 7,input 4,input 5,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_62 : Impossible true (goalAt 183) 5 state183_62.toFinset :=
  node_ok cuts183 [] 0x25240b0902821094902521094902524024300d0c0949025240343024a40949021a10929024a40b0900c8c0929021a10929024a4086840c8c0929024a4032302c0c0b0902c24024842c240a48428240a0902c0c0948425210a03024640858425240919024640121124a4091902464031302c24091902161091902464085840c4c09190246403130 (by decide +kernel)

def state183_63 : List Sig := [0x3333333333333333333333333333333333333333333300003333333333330000,input 7,input 4,input 5,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_63 : Impossible true (goalAt 183) 5 state183_63.toFinset :=
  node_ok cuts183 [] 0x25240b0902821094902521094902524024300d0c0949025240343024640949021610919024640b0900c4c091902161091902464085840c4c091902464031302c0c0b0902c24024842c240a48428240a0902c0c0948425210a03024a40868425240929024640121124640929024a4032302c240929021a10929024a4086840c8c0929024a403230 (by decide +kernel)

def state183_64 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000,input 7,input 4,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_64 : Impossible true (goalAt 183) 5 state183_64.toFinset :=
  node_ok cuts183 [] 0x24a40b0900c8c0929021a10929024a4086840c8c0929024a40323024640929004844919024640b0900c4c091902161091902464085840c4c091902464031302c0c0b0902c24024842c240a48428240a0902c0c0948425210a03024a40868424a40949024640858424640949025240a0842c2409490090c094902524094840d0c09490252403430 (by decide +kernel)

def state183_65 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_65 : Impossible true (goalAt 183) 6 state183_65.toFinset :=
  node_ok cuts183 [⟨state183_62,exclude183_62⟩,⟨state183_63,exclude183_63⟩,⟨state183_64,exclude183_64⟩] 0x94902c240a084252409484252409490090c034302524094900d0c2000225240949040004929025240868424a4092902c240323024a40868424a40929021a10323024a4092900c8c2000124a40929040000919025240858424640919024a4012112464091902c24031302464085842464091902161031302464091900c4c2000024640919040008b0302c240b0900921027072c240a48428240a0902c0c0948425210a03005c1c8707 (by decide +kernel)

def state183_66 : List Sig := [0xffffffffffff0000ffffffffffff0000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_66 : Impossible true (goalAt 183) 6 state183_66.toFinset :=
  node_ok cuts183 [] 0x94902c240a084252409484252409490090c034302524094900d0c0929025240868424a4092902c240323024a40868424a40929021a10323024a4092900c8c0919025240858424640919024a4012112464091902c24031302464085842464091902161031302464091900c4c031112c240b0900c444b09029210a09028240970725210948421c1c343025240343025240323024a40323024a4031302464031302464031112c24031112c240170725211000525210b030 (by decide +kernel)

def state183_67 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_67 : Impossible true (goalAt 183) 6 state183_67.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩] 0x25240a0900d0c094902521094902524100090d0c0949025240343009080949025240243024a40949021a10929024a40a0900c8c0929021a10929024a4086840c8c0929024a40323008880929024a40223024640949021610919024640929004844919024640a0900c4c091902161091902464085840c4c0919024640313008480919024640213029210a03028240a0900c446000028240a09008444a03025210948405210170725210948440014a020 (by decide +kernel)

def state183_68 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_68 : Impossible true (goalAt 183) 5 state183_68.toFinset :=
  node_ok cuts183 [] 0x92902c240323024a40868424a40929021a10323024a4092900c8c0929025240868424a40919024a4012112464091902c24031302464085842464091902161031302464091900c4c0919025240858424640a0842c0c0b0902c24021112c0c0948425210148025240a0900d0c094902521094902524013070d0c09490252403430 (by decide +kernel)

def state183_69 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 7,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_69 : Impossible true (goalAt 183) 6 state183_69.toFinset :=
  node_ok cuts183 [⟨state183_21,exclude183_21⟩,⟨state183_68,exclude183_68⟩] 0x25240b0900d0c0949005c1c94902524013070d0c0949025240343024a40949021a10929024a40b0900c8c0929021a10929024a4086840c8c0929024a40323024640949021610919024640929004844919024640b0900c4c091902161091902464085840c4c0919024640313029210b0302c240b09008444b03025c1cb03005c1d000925242000125240868424a40868424a40858424640858424640a0902824200002c241000505c1c948425210a030 (by decide +kernel)

def state183_70 : List Sig := [0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_70 : Impossible true (goalAt 183) 6 state183_70.toFinset :=
  node_ok cuts183 [] 0xc8c0929024a40323024a40b0900c8c0929021a10929024a40868421a10929024a4086840c4c0919024640313024640929004844919024640b0900c4c091902161091902464085842161091902464085842c0c0b0902c240311129210b03028080a030280c0b09040024a09025210b03020c1cb03020c1c34302524094900d0c0929021a1092902524091902161091902524094900d0c0b090252402430252409490090810001 (by decide +kernel)

def state183_71 : List Sig := [0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_71 : Impossible true (goalAt 183) 7 state183_71.toFinset :=
  node_ok cuts183 [⟨state183_61,exclude183_61⟩,⟨state183_65,exclude183_65⟩,⟨state183_66,exclude183_66⟩,⟨state183_67,exclude183_67⟩,⟨state183_69,exclude183_69⟩,⟨state183_70,exclude183_70⟩] 0x87070d0c034302c0c094902524087072524094902c0c034300d0c100092524094902c24034302c24100090d0c034302c2409490252410004090802420400249490252410009252409490400102420090c100098001600004000494902524100092524094904000500094000487070c8c032302c0c0929024a40870724a4092902c0c032300c8c1000924a40929025240868425241000821a10868425240929024a41000824a4092902c24032302c24100080c8c032302c240929024a41000421a10868440020929024a41000824a40929040010868421a11000821a10868440000929024a41000824a40929040000868421a1091110c4c031302c0c091902464091112464091902c0c031300c4c0151124640919025240858425240151121610858425240919024640131124640919024a41000324a40131140020121124a4091902464031112464091902c24031302c24031110c4c031302c24091902464100042161085844000c919024641000324640919040010858421611000321610858440008919024641000324640919040008858421610b0300c444b03024444b0902c240b0302c240b0902444431110c445000440010a4842c0c200042c0c0a02040010a0202c0c20003280c0a02040010a0302c24100052c24100044001100044001100042824100044001494842c0c1000e2c0c087078000887072c0c200012c0c08707400388707 (by decide +kernel)

def state183_72 : List Sig := [0xffffffffffffffffffffffffffffffff0000ffff000000000000ffff00000000,input 7,input 4,input 5,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_72 : Impossible true (goalAt 183) 6 state183_72.toFinset :=
  node_ok cuts183 [] 0x94902c240a0842524094842524094900908034302524094900d0c034302524094900d0c0929025240868424a4092902c240323024a40868424a40929021a10323024a4092900c8c0323024a4092900c8c0919025240858424640919024a4012112464091902c24031302464085842464091902161031302464091900c4c031302464091900c4c0a0202c240b0900921031112c240b0900c444b09029210a09028240b02025210948428080170725210948405c1cb030 (by decide +kernel)

def state183_73 : List Sig := [0xffff000000000000ffff000000000000ffff000000000000ffff00000000,input 4,input 5,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_73 : Impossible true (goalAt 183) 7 state183_73.toFinset :=
  node_ok cuts183 [⟨state183_72,exclude183_72⟩] 0x87070d0c034302c0c094902524087072524094902c0c034300d0c100052524094902c24034302c24100090d0c034302c240949025240948409080948404c0c949025240948425240949004c0c24200908087070c8c032302c0c0929024a40870724a4092902c0c032300c8c1000924a40929025240868425241000821a10868425240929024a41000524a4092902c24032302c24100080c8c032302c240929024a40170721a10868425210929024a40170724a40929025210868421a1091110c4c031302c0c091902464091112464091902c0c031300c4c0151124640919025240858425240151121610858425240919024640131124640919024a41000324a40131140020121124a4091902464031112464091902c24031302c24031110c4c031302c240919024640170721610858425210919024640170724640919025210858421610b0300c444b03024444b0902c240b0302c240b0902444431110c444b03005c1cb03028080948425210b03025210948428080170728081000440010b4842c24100052c241000425210948428081000e28080b03040014b03028082000028080b03040014b030090810001090809490400149490090810009090809490400049490088810000088809290400149290088810008088809290400009290084810002084809190400149190084810003084809190400089190400110004292110005400110007 (by decide +kernel)

def state183_74 : List Sig := [0xffffffff00000000ffffffff00000000ffff000000000000ffff0000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_74 : Impossible true (goalAt 183) 6 state183_74.toFinset :=
  node_ok cuts183 [⟨state183_11,exclude183_11⟩] 0x34302524094900d0c09484252409490090c094900d0c0343025240929025240868424a40323024a4092900c8c0868424a40929021a1092900c8c0323024a40919025240858424640919024a4012112464031302464091900c4c085842464091902161091900c4c0313024640b030252109484280c0948409c1e000025210b03024444b0302444494900d0c094900d0c092900c8c092900c8c091900c4c091900c4c091112c0c091112c0c0948405c1c948440010b090 (by decide +kernel)

def state183_75 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_75 : Impossible true (goalAt 183) 7 state183_75.toFinset :=
  node_ok cuts183 [⟨state183_67,exclude183_67⟩,⟨state183_65,exclude183_65⟩,⟨state183_74,exclude183_74⟩] 0xb0300c444b03024444b0902c240b0302c240b0902444431110c446000209c1c270740014b0902c24200012c240b09040014270709c1ca4842524094902c24034302c240a4840d0c0a0842c24094902524100090d0c034302c0c094902524100092524094902c0c034300d0c0948409080948440024949025240948425240949040010242009081000909080242040004949025241000925240949040004242009080270724a4092902c24032302c24027070c8c032302c240929024a41000924a40929025240868425241000821a10868425240929024a4100080c8c032302c0c0929024a41000824a4092902c0c032300c8c1000421a10868425210929024a41000824a40929025210868421a11000808880222040000929024a41000824a4092904000022200888031112464091902c24031302c24031110c4c031302c240919024640151124640919025240858425240151121610858425240919024640131124640919024a41000324a40131140020121124a4091902464091110c4c031302c0c091902464091112464091902c0c031300c4c1000421610858425210919024641000324640919025210858421611000308480212040008919024641000324640919040008212008481000440010a0202c24094842c240a48440010a4842c242000028240a48425210a0902c0c1000e2c0c10004252109484400110004280c10004400381707 (by decide +kernel)

def state183_76 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_76 : Impossible true (goalAt 183) 6 state183_76.toFinset :=
  node_ok cuts183 [⟨state183_68,exclude183_68⟩] 0x2c0c031112c0c091112c240b0902c0c0b0902c24091110c444248009c1c929024a40b0900c8c0b09009c1c32300c8c0b09024a40929020c1c32300c8c0b03024a40929020c1c929024a40b0300c8c0323005c1c868421a10948424a40929005c1c929024a40948421a10868440050929024a40949021a1094904004c868421a10949024a4092900c444919024640b0900c4c0b0900c44431300c4c0b09024640919004c4491902464092904004c929004c4500130484492902464091902444431300c4c0b03024640919024444919024640b0300c4c0313005c1c858421610948424640919005c1c91902464094842161085840544491902464094902161094900544485842161094902464091902c24094842c240a08440024a0842c24200002c240a0842521094842c0c017072c0c083072521094842c0c0948425210830705c1c148028210949025240b0900d0c0b09028210343028210b09025240949020c1c34300d0c0b03025240949020c1c949025240b0300d0c03430252102420252101303252409490252109490252401303090802430 (by decide +kernel)

def state183_77 : List Sig := [0xffffffff0000ffffffffffff0000ffffffffffff00000000ffffffff00000000,input 5,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_77 : Impossible true (goalAt 183) 6 state183_77.toFinset :=
  node_ok cuts183 [⟨state183_21,exclude183_21⟩] 0x34302524094900d0c02420252409490090c0949028200a0842524094900d0c0343025240929025240868424a40323024a4092900c8c0868424a40929021a10929029210323024a40929021a10868424a40919025240858424640919024a4012112464031302464091900c4c0858424640919021610919029210313024640919021610858424640b03028080a030280c0b48429212000029210170740010948425210b03029210a48409210b0902c0c091112c0c09111 (by decide +kernel)

def state183_78 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_78 : Impossible true (goalAt 183) 7 state183_78.toFinset :=
  node_ok cuts183 [⟨state183_69,exclude183_69⟩,⟨state183_76,exclude183_76⟩,⟨state183_77,exclude183_77⟩] 0xb0300c444b03024444b0902c240b0302c240b0902444431110c444a4842524094902c24034302c240a4840d0c0a0842c240949025241000e0d0c034302c0c094902524100092524094902c0c034300d0c0170709080242004c0c949025240170725240949004c0c2420090c0270724a4092902c24032302c24027070c8c032302c240929024a41000924a40929025240868425241000821a10868425240929024a41000e0c8c032302c0c0929024a41000824a4092902c0c032300c8c0170721a10868405414929024a40170724a40929005414868421a1031112464091902c24031302c24031110c4c031302c240919024640151124640919025240858425240151121610858425240919024640131124640919024a41000324a40131140020121124a4091902464091110c4c031302c0c091902464091112464091902c0c031300c4c0170721610858405818919024640170724640919005818858421610b09005c1cb09029211000429210b09080000b09029210170729211000440010b0202c0c1000e2c0c1000405c1c170729211000529210b09040038b09029212000229210b09040014b09040039000140004949040038949040039000980004949040004949021a11000021a10929040038929021a11000821a10929040000929021611000221610919040038919021611000321610919040008919040011000428081000e400109484 (by decide +kernel)

def state183_79 : List Sig := [0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_79 : Impossible true (goalAt 183) 6 state183_79.toFinset :=
  node_ok cuts183 [] 0x24444170724444870725210948424444948425210870705c1c14840c44494842521027074001427070c445000508444270725210948424640948424640858405c1c858424640170724640858425210858425210242025210130325240949025210949025240130309080243021c1c34300d0c0911125240949021c1c94902524091110d0c0343009c1c94902524031110d0c0343009c1c34300d0c0311125240949021610949025240919005444919021610151121610919025240919005c1c868421a10948424a40929005c1c929024a40948421a10868440034929024a40949021a1094904004c868421a10949024a40929021c1c32300c8c0911124a40929021c1c929024a4091110c8c0323009c1c929024a4031110c8c0323009c1c32300c8c0311124a4092904004c929024a40919004c4491904004c131104844919024a4091904001431110c444911140014911140015000e0921091110c44424840c4c026062c24091900c44491900c4c031110c4c091900981891902444431300c4c086062464091902444491902464086060c4c03130 (by decide +kernel)

def state183_80 : List Sig := [0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc,input 5,input 7,input 0,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_80 : Impossible true (goalAt 183) 6 state183_80.toFinset :=
  node_ok cuts183 [] 0x24444170724444870725210948424444948425210870705c1c14840c44494842521027074001427070c445000508444270725210948424a40948424a40868405c1c868424a40170724a40868425210868425210242025210130325240949025210949025240130309080243021c1c34300d0c0911125240949021c1c94902524091110d0c0343009c1c94902524031110d0c0343009c1c34300d0c0311125240949021a10949025240929040034929021a11001321a10929025240929005c1c858421610948424640919005c1c91902464094842161085840544491902464094902161094900544485842161094902464091902444431300c4c086062464091902444491902464086060c4c031300c44491902464026060c4c031300c44431300c4c0260624640919004c4491902464092904004c929004c4500130484492902464091904001431110c444911140014911140015000e0921091110c44424840c8c031112c240929009c1c92900c8c027070c8c092900c444929021c1c32300c8c0911124a40929021c1c929024a4091110c8c03230 (by decide +kernel)

def state183_81 : List Sig := [0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 5,input 7,input 0,input 1,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_81 : Impossible true (goalAt 183) 6 state183_81.toFinset :=
  node_ok cuts183 [] 0x24444170724444870725210948424444948425210870705c1c14840c444948425210a08440014a0840c445000508444a08425210948425240130325240242025210948425240948425240242004c0c243005c1c868421a10948424a40929005c1c929024a40948421a10868421c1c32300c8c0911124a40929021c1c929024a4091110c8c0323009c1c929024a40a0840c8c0a08409c1c32300c8c0a08424a40929040034929024a40949021a1094904004c868421a10949024a40929005c1c858421610948424640919005c1c919024640948421610858404c4491902464092904004c929004c4500130484492902464091902444431300c4c086062464091902444491902464086060c4c031300c444919024640a0840c4c0a0840c44431300c4c0a0842464091900544491902464094902161094900544485842161094902464091904001431110c444911128210a08440014a0842821091110c44424840d0c031112c24094902821094900d0c0a0842821094900c444949021c1c34300d0c0911125240949021c1c94902524091110d0c03430 (by decide +kernel)

def state183_82 : List Sig := [0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_82 : Impossible true (goalAt 183) 6 state183_82.toFinset :=
  node_ok cuts183 [] 0x21c1c34300d0c0a03025240949021c1c949025240a0300d0c0343009c1c949025240a0900d0c0a09009c1c34300d0c0a09025240949025210242025210130325240949025210949025240130309080243040034929024a40949021a1094904004c868421a10949024a40929021c1c32300c8c0a03024a40929021c1c929024a40a0300c8c0323009c1c929024a40a0900c8c0a09009c1c32300c8c0a09024a40929005c1c868421a10948424a40929005c1c929024a40948421a10868405444919024640949021610949005444858421610949024640919004c4491902464092904004c929004c4500130484492902464091902444431300c4c0a03024640919024444919024640a0300c4c031300c444919024640a0900c4c0a0900c44431300c4c0a09024640919005c1c858421610948424640919005c1c9190246409484216108584280c03111280c0911128240a090280c0a0902824091110c444248440010270729210948428240a09040010a09028240948409c1c9484280c01707280c08707252109484280c0948425210870705c1c1484 (by decide +kernel)

def state183_83 : List Sig := [0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_83 : Impossible true (goalAt 183) 6 state183_83.toFinset :=
  node_ok cuts183 [] 0x34302524094900d0c094902c240343025240242025240949009080242025240949009080929025240868424a40323024a4092900c8c092902c240323024a40868424a40929021a10868424a40929021a10919025240858424640919024a4012112464031302464091900c4c091902c240313024640858424640919021610858424640919021610b0302c240b09009210a4842c240b09009c1cb03021c1ca030280c0b09009c1ca0902824094842c0c0a0202c0c08707 (by decide +kernel)

def state183_84 : List Sig := [0xffffffff00000000ffffffff0000000000000000000000000000000000000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_84 : Impossible true (goalAt 183) 7 state183_84.toFinset :=
  node_ok cuts183 [⟨state183_79,exclude183_79⟩,⟨state183_80,exclude183_80⟩,⟨state183_81,exclude183_81⟩,⟨state183_82,exclude183_82⟩,⟨state183_83,exclude183_83⟩] 0x911105c1c911121c1c948425210911125210948421c1c170705210311125210948409c1d000509c1c311140014211109c1c948425211000525210948440011000540012000440016000340010948425210948409080948404c0c949025240948425240949004c0c2420090c087070d0c034302444494902524087072524094902444434300d0c027072524094900c44434300d0c027070d0c034300c444949025241000525240949040005000540005000d40016000240004949025240170721a10868425210929024a40170724a40929025210868421a11000d24a40929025240868425241001321a10868425240929024a4087070c8c0323024444929024a40870724a4092902444432300c8c0270724a4092900c44432300c8c027070c8c032300c444929024a41000524a40929040001000540001001340016000140000929024a40170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024640131124640919024a41001324a4013114004c121124a4091902464091110c4c031302181891902464091112464091902181831300c4c031112464091900981831300c4c031110c4c031300981891902464100052464091904000900054000900064001600004000891902464100050c444311124445000524445000540038248440015000e2c0c1000540014b090 (by decide +kernel)

def state183_85 : List Sig := [0xddddddddddddddddddddddddddddddddddddddddccccccccddddddddcccccccc,input 1,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_85 : Impossible true (goalAt 183) 5 state183_85.toFinset :=
  node_ok cuts183 [] 0xb030252109484280c0b09029210a090282409484252409490090c034302524094900d0c094902c240a08425240b0302c240b09009210868424a40929021a10929025240868424a40323024a4092900c8c092902c240323024a4012112161091902464085842464085842524091900c4c091902464031302464031302c2409190 (by decide +kernel)

def state183_86 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0x1111111111111111111111111111111111111111000000001111111100000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_86 : Impossible true (goalAt 183) 4 state183_86.toFinset :=
  node_ok cuts183 [] 0x2c0c0948425210a0302c240a48428240a0902c0c0b0902c24024842161091902464085840c4c091902464031302464031302c240919024640858424a4091902521094902524024300d0c0949025240343025240b090282109490 (by decide +kernel)

def state183_87 : List Sig := [0x1111111111111111111111111111111111111111000000001111111100000000,input 1,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_87 : Impossible true (goalAt 183) 5 state183_87.toFinset :=
  node_ok cuts183 [⟨state183_86,exclude183_86⟩] 0xb030252109484280c0b09029210a090282409484252409490090c034302524094900d0c094902c240a08425240b0302c240b0900921016072521012112521012112524200002524012112c0c085072c0c012112c24025072c24085842464091902161091902161094902464031302464091900c4c091900c4c0b090246409290 (by decide +kernel)

def state183_88 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_88 : Impossible true (goalAt 183) 5 state183_88.toFinset :=
  node_ok cuts183 [⟨state183_86,exclude183_86⟩] 0xb030252109484280c0b09029210a09028240b0302c240b0900921085842464091902161031302464091900c4c091900c4c0b09024640919080000868424640919021610949024640868424a10120721a10830721a1086842c0c086842c24023072c24092902521094902524024300d0c0949025240343025240b090282109490 (by decide +kernel)

def state183_89 : List Sig := [0x3030303030303030303030303030303030303030303030303030303030303030,input 1,0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_89 : Impossible true (goalAt 183) 5 state183_89.toFinset :=
  node_ok cuts183 [] 0xb030252109484280c0b09029210a09028240b0302c240b0900921085842464091902161031302464091900c4c091900c4c0b09024640919004844929024640828024a40929021a40323024a4092900c8c092902c240323024a409484252409490090c034302524094900d0c094902c240a084252408584246409490246408684 (by decide +kernel)

def state183_90 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_90 : Impossible true (goalAt 183) 6 state183_90.toFinset :=
  node_ok cuts183 [⟨state183_24,exclude183_24⟩,⟨state183_34,exclude183_34⟩,⟨state183_85,exclude183_85⟩,⟨state183_87,exclude183_87⟩,⟨state183_88,exclude183_88⟩,⟨state183_89,exclude183_89⟩] 0x2c0c016072c0c0a0202521094842c0c0948425210a0200581ca0302c24094842c240a48480004a4842c242000028240a48425210a09025210242025210120325240949025210949025240120309080243021c1c34300d0c0b03025240949021c1c949025240b0300d0c0343029210949025240b0900d0c0b09029210343028210b0902524094900581c868421a10948424a4092900581c929024a40948421a10868480014929024a40949021a10949080010868421a10949024a40929021c1c32300c8c0b03024a40929021c1c929024a40b0300c8c0323009c1c929024a40b0900c8c0b09009c1c32300c8c0b09024a4092902c0c031112c0c091112c240b0902c0c0b0902c24091110c444248425210858421610160724640919025210919024640160721610858425240919024640141121610858425240858425240141124640919024a4091902464012118000c121124a42000224a4012112464091902c0c031300c4c091112464091902c0c091902464091110c4c031302c24091902464031110c4c031302c24031302c2403111246409190 (by decide +kernel)

def state183_91 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeecccccccc,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_91 : Impossible true (goalAt 183) 5 state183_91.toFinset :=
  node_ok cuts183 [] 0xb030252109484280c0b09029210a0902824016072521094840581c9484252409490090c034302524094900d0c094902c240a0842524014112524094900504485072c0c0b0900921025072161091902464085842464094902161091900c4c0919024640313024640b0900c4c09190048449190246401211 (by decide +kernel)

def state183_92 : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_92 : Impossible true (goalAt 183) 6 state183_92.toFinset :=
  node_ok cuts183 [⟨state183_38,exclude183_38⟩,⟨state183_91,exclude183_91⟩] 0x2c0c0948425210a0302c240a48428240a0900581c94842521016072521094902524024300d0c0949025240343025240b09028210949005044949025240141121a10929024a40868424a40949021a1092900c8c0929024a40323024a40b0900c8c0929004844929024a4012112181cb0302c24024840981c858424640919021610919025240858424640919024a4200012464031302464091900c4c091902c2403130246420000 (by decide +kernel)

def state183_93 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_93 : Impossible true (goalAt 183) 6 state183_93.toFinset :=
  node_ok cuts183 [] 0x2c0c0948425210a0302c240a48428240a0900581c94842521016072521094902524024300d0c0949025240343025240b09028210949005044949025240141121a10929024a40868424a40949021a1092900c8c0929024a40323024a40b0900c8c0929004844929024a40121124444b0302c24024840c44485842464091902161091902161094902464091900484492902464031302464091900c4c091900c4c0b090246410002 (by decide +kernel)

def state183_94 : List Sig := [0x5555555555555555555555555555555555555555000000005555555500000000,input 0,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_94 : Impossible true (goalAt 183) 6 state183_94.toFinset :=
  node_ok cuts183 [] 0xb030252109484280c0b09029210a090282409484252409490090c034302524094900d0c094902c240a08425240868424a40929021a10929025240868424a40323024a4092900c8c092902c240323024a40b0302c240b09009210170725210160725210151125240141125240131124a40121124a4091112c0c091112c0c031112c24031112c240948405c1c948405c1c949005444949005444929004c44929004c44b03024444b03024444b0900c444b0900c4449190 (by decide +kernel)

def state183_95 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_95 : Impossible true (goalAt 183) 6 state183_95.toFinset :=
  node_ok cuts183 [] 0x34302524094900d0c094902c240a08425240242025240949009080929025240868424a40323024a4092900c8c092902c240323024a40868424a40929021a10919025240858424640919024a4012112464031302464091900c4c091902c240313024640858424640919021610b0302c240b09009210b03028080b03028080b09029210b09029210242025240242025240868424a40868424a40858424640858424640a0202c0c0a0202c0c0a4842c240a4842c2409484 (by decide +kernel)

def state183_96 : List Sig := [0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_96 : Impossible true (goalAt 183) 7 state183_96.toFinset :=
  node_ok cuts183 [⟨state183_39,exclude183_39⟩,⟨state183_42,exclude183_42⟩,⟨state183_52,exclude183_52⟩,⟨state183_55,exclude183_55⟩,⟨state183_59,exclude183_59⟩,⟨state183_65,exclude183_65⟩,⟨state183_25,exclude183_25⟩,⟨state183_35,exclude183_35⟩,⟨state183_90,exclude183_90⟩,⟨state183_92,exclude183_92⟩,⟨state183_93,exclude183_93⟩,⟨state183_94,exclude183_94⟩,⟨state183_95,exclude183_95⟩] 0xb03005c1cb03028080948425210b030252109484280801707280c0b09025210b09029212000729210b09080018a09029210948428242000c05c1c170740010948425212000525210948440010170705c1c948409080948404c0c949025240948425240949004c0c2420090c100160d0c034302c0c094902524100162524094902c0c034300d0c0a4842524094902c24034302c240a4840d0c0a0842c240949025241001605444151140004949025241001625240949040004151105444170721a10868425210929024a40170724a40929025210868421a11001524a40929025240868425241001521a10868425240929024a4100150c8c032302c0c0929024a41001524a4092902c0c032300c8c1001524a4092902c24032302c24100150c8c032302c240929024a41001504c44131140000929024a41001524a40929040000131104c44170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024640131124640919024a41001524a40131140054121124a4091902464200040c4c031302c0c091902464200032464091902c0c031300c4c200022464091902c24031302c24200010c4c031302c240919024642000b8002a00084000891902464200002464091904000a00094000900054001491112c0c1000e2c0c100052c240b09040015000e09211000e400383111 (by decide +kernel)

def state183_97 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_97 : Impossible true (goalAt 183) 4 state183_97.toFinset :=
  node_ok cuts183 [] 0xd0c0949025240343025210949025240120725240b0902821094902c0c0948425210a0302c240a48428240a0902464094902161091900c4c091902464031302161091902464085842464092900c4c091902c0c0b0902c2401211 (by decide +kernel)

def state183_98 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_98 : Impossible true (goalAt 183) 4 state183_98.toFinset :=
  node_ok cuts183 [] 0x2c0c0b0902c24021112c0c0948425210a0302c240a48428240a0900c4c0919024640313024640b0900c4c091902161091902464085842464092902161091900d0c0949025240343025240b09028210949025210949025241000b (by decide +kernel)

def state183_99 : List Sig := [0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,input 1,0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_99 : Impossible true (goalAt 183) 5 state183_99.toFinset :=
  node_ok cuts183 [⟨state183_97,exclude183_97⟩,⟨state183_98,exclude183_98⟩] 0x34302524094900d0c094902c240a0842524094842524094900481cb0302c240b09008444b030252109484280c0b09029210a0902824012112524200012524012112c0c085072c0c012112c24200002c24016072521012112521092902464094902161091900c4c0919024640313024640b0900c4c09190216109190246408584 (by decide +kernel)

def state183_100 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_100 : Impossible true (goalAt 183) 4 state183_100.toFinset :=
  node_ok cuts183 [] 0xc4c0919024640313021610919024640858424640b0900c4c091902464094902161091902c0c0948425210a0302c240868428240a0902c0c0b0902c24021110c8c0949025240323025210949025240210724a40929021a109490 (by decide +kernel)

def state183_101 : List Sig := [0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,input 1,0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 7,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_101 : Impossible true (goalAt 183) 5 state183_101.toFinset :=
  node_ok cuts183 [⟨state183_97,exclude183_97⟩,⟨state183_100,exclude183_100⟩] 0x34302524094900d0c0948425240949004c1c94902c240a0842524091902524085842464031302464091900c4c085842464091902161091900c8c200002464091902c240313024640b030252109484280c0b09029210a090282403230252420001252403230248c087070c8c017072521032302521092902c0c0b0902c2402111 (by decide +kernel)

def state183_102 : List Sig := [0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,input 1,0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7,input 0]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_102 : Impossible true (goalAt 183) 5 state183_102.toFinset :=
  node_ok cuts183 [⟨state183_100,exclude183_100⟩,⟨state183_98,exclude183_98⟩] 0x31302464091900c4c091902c240313024640858424640919021610919021a12000124640919025240858424640b0302c240b09008444b030252109484280c0b09029210a09028240830721a1086842c0c086842c24200002c240868424a10130721a1092900d0c0949025240343025240b09028210949025210949025241000b (by decide +kernel)

def state183_103 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_103 : Impossible true (goalAt 183) 5 state183_103.toFinset :=
  node_ok cuts183 [] 0x323024a4092900c8c092902c240323024a40868424a40929021a10919024a4012112464031302464091900c4c091902c240313024640858424640919021610b0302c240b09008444b03025210948405200b09028210b09025210929021a1092902524091902161091902524034302524094900d0c0949028210b090252401307 (by decide +kernel)

def state183_104 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_104 : Impossible true (goalAt 183) 6 state183_104.toFinset :=
  node_ok cuts183 [⟨state183_99,exclude183_99⟩,⟨state183_101,exclude183_101⟩,⟨state183_102,exclude183_102⟩,⟨state183_103,exclude183_103⟩] 0x21c1c34300d0c0b03025240949021c1c949025240b0300d0c0343029210949025240b0900d0c0b09029210343028210b09025240949025212000325210130325240949025210949025240130340034130740034929024a40949021a10949080008868421a10949024a40929021c1c32300c8c0b03024a40929021c1c929024a40b0300c8c0323040014929024a40b0900c8c0b0908000432300c8c0b09024a40929005c1c868421a10948424a40929005c1c929024a40948421a10868405444919024640949021610949005444858421610949024640919004c44919024640929040018929004c4600000484492902464091902444431300c4c0b03024640919024444919024640b0300c4c0313008444919024640b0900c4c0b0900844431300c4c0b09024640919005c1c858421610948424640919005c1c91902464094842161085842c0c021112c0c091112c240b0902c0c0b0902c24091110844421112c0c017072c0c087072521094842c0c0948425210870705c1ca0302c24094842c240a48440010a4842c241000428240a48425210a090 (by decide +kernel)

def state183_105 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000,input 4,input 5,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_105 : Impossible true (goalAt 183) 5 state183_105.toFinset :=
  node_ok cuts183 [] 0xc8c0929024a40323024a40b0900c8c0929021a10929024a4086842464092900484491900c4c0919024640313024640b0900c4c091902161091902464085842c0c0b0902c24024802c0c094842521014802c240a0842c240948424a40868424a4094902464085842464094900d0c0949025240343025240a0842c2409490090c09490252409484 (by decide +kernel)

def state183_106 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffffffffffff0000ffffffffffff0000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_106 : Impossible true (goalAt 183) 6 state183_106.toFinset :=
  node_ok cuts183 [⟨state183_105,exclude183_105⟩] 0x34302524094900d0c094902c240a084252402420252409490090c2000025240949040004929025240868424a40323024a4092900c8c092902c240323024a40868424a40929021a10868424a40929021a10919025240858424640919024a4012112464031302464091900c4c091902c240313024640858424640919021610858424640919021610b0302c240b0900c444b0302c080b03021c1cb09029210b0902921094842c0c087072c0c0a0202c240a4842c240a484 (by decide +kernel)

def state183_107 : List Sig := [0xffffffff00000000ffffffff00000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_107 : Impossible true (goalAt 183) 7 state183_107.toFinset :=
  node_ok cuts183 [⟨state183_104,exclude183_104⟩,⟨state183_106,exclude183_106⟩] 0x911105c1c911121c1c948425210911125210948421c1c170705210b09025210b09029211000529210b09040014a09029210948428240948409080948404c0c949025240948425240949004c0c2420090c087070d0c034302444494902524087072524094902444434300d0c0a4842524094902c24034302c240a4840d0c0a0842c240949025240170721a10868425210929024a40170724a40929025210868421a11000d24a40929025240868425241001721a10868425240929024a4087070c8c0323024444929024a40870724a4092902444432300c8c1000524a4092902c24032302c24100170c8c032302c240929024a40170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024640131124640919024a41000624a4013114005c121124a4091902464091110c4c031302181891902464091112464091902181831300c4c100052464091902c24031302c24100060c4c031302c240919024641000540038b11140014b0902c24091114001491114001500044001094844001494844001600018000094844001094840d0c100010d0c094904001494900d0c1000d0d0c094904000494900c8c100000c8c092904001492900c8c100170c8c092904000092900c4c100020c4c091904001491900c4c100060c4c091904000891904001500152c0c10005400143111 (by decide +kernel)

def state183_108 : List Sig := [0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,input 0,input 5,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_108 : Impossible true (goalAt 183) 6 state183_108.toFinset :=
  node_ok cuts183 [] 0xb030252109484280c0948409c1c2111252109484252409490090c034302524094900d0c094900d0c0343025240868424a40929021a10929025240868424a40323024a4092900c8c092900c8c0323024a40b03024444b0300c444858424640919021610919025240858424640919024a4013112464091112464091902c0c091902c640311124640313025210160625210160625240343025240343024a40323024a40323024444b03024444b0300c44426062c240b090 (by decide +kernel)

def state183_109 : List Sig := [0xffff0000ffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 5,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_109 : Impossible true (goalAt 183) 6 state183_109.toFinset :=
  node_ok cuts183 [] 0x34302524094900d0c094902c240343025240948425240949009080242025240949009080929025240868424a40323024a4092900c8c092902c240323024a40868424a40929021a10222024a40929008880919025240858424640919024a4012112464031302464091900c4c091902c240313024640858424640919021610212024640919008480b0302c240b0900c444b03025210948428080b0902d210b0902521017072c0c0a0202c0c0a0202c24027072c240a484 (by decide +kernel)

def state183_110 : List Sig := [0xffffffff00000000ffffffff00000000000000000000000000000000,input 5,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_110 : Impossible true (goalAt 183) 7 state183_110.toFinset :=
  node_ok cuts183 [⟨state183_56,exclude183_56⟩,⟨state183_26,exclude183_26⟩,⟨state183_36,exclude183_36⟩,⟨state183_108,exclude183_108⟩,⟨state183_109,exclude183_109⟩] 0xb03005c1cb03028080948425210b030252109484280801707280c0311125210948409c1e000209c1c311180004211109c1c948425210948409080948404c0c949025240948425240949004c0c2420090c1000e0d0c034302c0c094902524100142524094902c0c034300d0c027072524094900c44434300d0c027070d0c034300c444949025240170721a10868425210929024a40170724a40929025210868421a11001424a40929025240868425241001321a10868425240929024a41000e0c8c032302c0c0929024a41001324a4092902c0c032300c8c0270724a4092900c44432300c8c027070c8c032300c444929024a40170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024640131124640919024a41001324a4013114004c121124a40919024641000e0c4c031302c0c091902464200002464091902c0c031300c4c031112464091900981831300c4c031110c4c0313009818919024641000540038b1112c0c1000e2c0c100050c444311125211000425210170740038170725212000425210170740010170725241000125240343040038343025241001425240343040004343024a41000024a40323040038323024a41001324a40323040000323024641000224640313040038313024642000324640313040008313040015000524445000e40054b090 (by decide +kernel)

def state183_111 : List Sig := roots 183
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude183_111 : Impossible true (goalAt 183) 8 state183_111.toFinset :=
  node_ok cuts183 [⟨state183_33,exclude183_33⟩,⟨state183_37,exclude183_37⟩,⟨state183_43,exclude183_43⟩,⟨state183_53,exclude183_53⟩,⟨state183_57,exclude183_57⟩,⟨state183_60,exclude183_60⟩,⟨state183_71,exclude183_71⟩,⟨state183_73,exclude183_73⟩,⟨state183_75,exclude183_75⟩,⟨state183_78,exclude183_78⟩,⟨state183_84,exclude183_84⟩,⟨state183_96,exclude183_96⟩,⟨state183_107,exclude183_107⟩,⟨state183_110,exclude183_110⟩] 0x80034b0300c444b0308003091112c240b0908002cb0302c240b0908002891110c444248480024b03005c1cb03040010a02025210948480020b03025210948440010a02005c1ca0308001cb09025210b09040010a48480004a48480018b09080000a09040010a48425210a0904000487070d0c0343040004b03025240949040004870725240949040004b0300d0c0343040004a48425240949040004b0900d0c0b09040004a4840d0c0a08440004b0902524094904000494840908094844000413032524094904000494842524094904000413030908024304000087070c8c0323040000b03024a40929040000870724a40929040000b0300c8c0323040000270724a40929040000b0900c8c0b0904000027070c8c0323040000b09024a40929040000170721a10868440000948424a40929040000170724a40929040000948421a10868440001000024a40929040000949021a10949040001000021a10868440000949024a4092908001491110c4c0313040008b03024640919080010911124640919040008b0300c4c031308000c311124640919040008b0900c4c0b0908000831110c4c0313040008b0902464091904001017072161085844000894842464091904000c1707246409190400089484216108584400041511246409190400049490216109490400041511216108584400049490246409190400001311246409190400009290400009290400001311400001211400009290246409190 (by decide +kernel)

theorem lower183 : Claim 183 9 :=
  fromSearch 66629 (by decide +kernel) exclude183_111

theorem lower199 : Claim 199 6 :=
  fromLift 6 1 1638 lower198 (by decide +kernel)

theorem lower87 : Claim 87 6 :=
  fromLift 6 1 66630 lower86 (by decide +kernel)

def rule215_0 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower213 none (by decide +kernel)

def rule215_1 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower214 none (by decide +kernel)

def rule215_2 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower211 none (by decide +kernel)

def rule215_3 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower199 none (by decide +kernel)

def rule215_4 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower87 none (by decide +kernel)

def rule215_5 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower151 none (by decide +kernel)

def rule215_6 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower198 none (by decide +kernel)

def rule215_7 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower197 none (by decide +kernel)

def rule215_8 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower195 none (by decide +kernel)

def rule215_9 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower193 none (by decide +kernel)

def rule215_10 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower86 none (by decide +kernel)

def rule215_11 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower85 none (by decide +kernel)

def rule215_12 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower83 none (by decide +kernel)

def rule215_13 : {c : Cut // CutGood (goalAt 215) c} :=
  ruleFor 215 lower84 none (by decide +kernel)

def cuts215 : Cuts (goalAt 215) := [rule215_0,rule215_1,rule215_2,rule215_3,rule215_4,rule215_5,rule215_6,rule215_7,rule215_8,rule215_9,rule215_10,rule215_11,rule215_12,rule215_13]

def state215_0 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,input 4,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_0 : Impossible true (goalAt 215) 6 state215_0.toFinset :=
  node_ok cuts215 [] 0x20c1c424010900c04024a40929020c1c929024a40c04010900424011c1c929024a40d09010900d09011c1c424010900d09024a40929005c1c868421a10948424a40929005c1c929024a40948421a10868424444414010500c04024640919024444919024640c04010500414004c44919024640929040024929004c45000904844929024640919014444919024640d09010500d09014444414010500d09024640919005c1c858421610948424640919005c1c919024640948421610858430100511130100911134240d09030100d09034240911114444509024444504014100c04025210948424444948425210c04014100504034240948434240c48414100c48434240504030240c48425210c09030100444011100830725240949030100949025240830711100444024a40949024a40868440024868424a41000924a40868425240949024640949024640858405444858424640151124640858425240949034240949025240c48411100c08434240444034240c484252409490141004440111009484252409490141009490252409484111009484 (by decide +kernel)

def state215_1 : List Sig := [0x5555555555555555555555555555555555555555555555555555000055550000,input 7,input 4,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_1 : Impossible true (goalAt 215) 5 state215_1.toFinset :=
  node_ok cuts215 [] 0x25240d09030210949025210949025240444011100949025240444024a40949021a10929024a40d09010900929021a10929024a40868410900929024a40424030100d09034240509034240c48430240c09014100948425210504024640858425240919024640121124a409190246404140342409190216109190246408584105009190246404140 (by decide +kernel)

def state215_2 : List Sig := [0x3333333333333333333333333333333333333333333333333333000033330000,input 7,input 4,input 6,input 0,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_2 : Impossible true (goalAt 215) 5 state215_2.toFinset :=
  node_ok cuts215 [] 0x25240d09030210949025210949025240444011100949025240444024640949021610919024640d09010500919021610919024640858410500919024640414030100d09034240509034240c48430240c09014100948425210504024a40868425240929024640121124640929024a40424034240929021a10929024a40868410900929024a404240 (by decide +kernel)

def state215_3 : List Sig := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000,input 7,input 4,input 6,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_3 : Impossible true (goalAt 215) 5 state215_3.toFinset :=
  node_ok cuts215 [] 0x24a40d09010900929021a10929024a40868410900929024a40424024640929004844919024640d09010500919021610919024640858410500919024640414030100d09034240509034240c48430240c09014100948425210504024a40868424a40949024640858424640949025240c084342409490111009490252409484111009490252404440 (by decide +kernel)

def state215_4 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_4 : Impossible true (goalAt 215) 6 state215_4.toFinset :=
  node_ok cuts215 [⟨state215_1,exclude215_1⟩,⟨state215_2,exclude215_2⟩,⟨state215_3,exclude215_3⟩] 0x949034240c08425240948425240949011100444025240949011102000225240949040008929025240868424a40929034240424024a40868424a40929021a10424024a40929010902000124a40929040000919025240858424640919024a40121124640919034240414024640858424640919021610414024640919010502000024640919040004c04034240d09014240470734240c48430240c09014100948425210504005c1c8707 (by decide +kernel)

def state215_5 : List Sig := [0xffffffffffffffffffff0000ffff0000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_5 : Impossible true (goalAt 215) 6 state215_5.toFinset :=
  node_ok cuts215 [] 0x949034240c08425240948425240949011100444025240949011100929025240868424a40929034240424024a40868424a40929021a10424024a40929010900919025240858424640919024a40121124640919034240414024640858424640919021610414024640919010500511134240d09014444d09031210c09030240504025210948414100444025240444025240424024a40424024a40414024640414024640511134240511134240504025210504025210c040 (by decide +kernel)

def state215_6 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 7,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_6 : Impossible true (goalAt 215) 6 state215_6.toFinset :=
  node_ok cuts215 [] 0x25240c09011100949025210949025241000811100949025240444011100949025240444024a40949021a10929024a40c09010900929021a10929024a40868410900929024a40424010900929024a40424024640949021610919024640929004844919024640c09010500919021610919024640858410500919024640414010500919024640414031210511130240c09014240504030240c09010444911125210948405210504025210948440010c040 (by decide +kernel)

def state215_7 : List Sig := [0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_7 : Impossible true (goalAt 215) 6 state215_7.toFinset :=
  node_ok cuts215 [] 0x10900929024a40424024a40d09010900929021a10929024a40868421a10929024a40868410500919024640414024640929004844919024640d09010500919021610919024640858421610919024640858430100d09034240509031210504030100911114100d09014100c09025210c04020c1cc04020c1c444025240949011100929021a10929025240919021610919025240949011100d090252404440252409490111010002 (by decide +kernel)

def state215_8 : List Sig := [0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_8 : Impossible true (goalAt 215) 7 state215_8.toFinset :=
  node_ok cuts215 [⟨state215_0,exclude215_0⟩,⟨state215_4,exclude215_4⟩,⟨state215_5,exclude215_5⟩,⟨state215_6,exclude215_6⟩,⟨state215_7,exclude215_7⟩] 0x870711100444030100949025240870725240949030100444011101000825240949034240444034241000811100444034240949025241000311100444014100949025241000825240949014100444011101000880012000040008949025241000825240949040009000840008870710900424030100929024a40870724a40929030100424010901000724a40929025240868425241000721a10868425240929024a41000724a40929034240424034241000710900424034240929024a41000321a10868414100929024a41000724a40929014100868421a11000721a10868440000929024a41000724a40929040000868421a10911110500414030100919024640911124640919030100414010500151124640919025240858425240151121610858425240919024640131124640919024a41000724a4013114001c121124a40919024640511124640919034240414034240511110500414034240919024641000321610858414100919024641000624640919014100858421611000621610858440004919024641000624640919040004858421610c04014444c04024444d09034240c04034240d0902444451111424100034000cc48424444504014100c0404000cc04024446000324444c0401410050403424100053424100031410050404000d0003302410003400149484301010004301008707800088707301020001301008707400108707 (by decide +kernel)

def state215_9 : List Sig := [0x5555555555555555555555555555555500005555000055550000000000000000,input 7,input 4,input 6,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_9 : Impossible true (goalAt 215) 5 state215_9.toFinset :=
  node_ok cuts215 [] 0x25240d09030210949025210949025240444011100949025240444024a40949021a10929024a40d09010900929021a10929024a40868410900929024a40424030100d09034240448434240c48430240c09034100948425210c04024640858425240919024640121124a409190246404140342409190216109190246408584105009190246404140 (by decide +kernel)

def state215_10 : List Sig := [0xffffffffffffffffffffffffffffffff0000ffff0000ffff0000000000000000,input 7,input 4,input 6,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_10 : Impossible true (goalAt 215) 6 state215_10.toFinset :=
  node_ok cuts215 [⟨state215_9,exclude215_9⟩] 0x949034240c08425240948425240949011100444025240949011100151125240949005444929025240868424a40929034240424024a40868424a40929021a10424024a40929010900131124a40929004c44919025240858424640919024a40121124640919034240414024640858424640919021610414024640919010502000024640919040004c04034240d09011210511134240d09014444d09031210c09030240d040252109484301001707252109484141009111 (by decide +kernel)

def state215_11 : List Sig := [0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000,input 4,input 6,input 0,input 1,input 2,input 7]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_11 : Impossible true (goalAt 215) 7 state215_11.toFinset :=
  node_ok cuts215 [⟨state215_10,exclude215_10⟩] 0x870711100444030100949025240870725240949030100444011101000525240949034240444034241000811100444034240949025240948411100948404c0c949025240948425240949004c0c444011100870710900424030100929024a40870724a40929030100424010901000724a40929025240868425241000721a10868425240929024a41000724a40929034240424034241000710900424034240929024a40170721a10868425210929024a40170724a40929025210868421a10911110500414030100919024640911124640919030100414010500151124640919025240858425240151121610858425240919024640131124640919024a41000724a4013114001c121124a40919024640511124640919034240414034240511110500414034240919024640170721610858425210919024640170724640919025210858421610c04014444c04024444d09034240c04034240d09024444511114240911105c1c91113010094842521091112521094843010017073010100034000cd4843424100053424100032521094843010100043010091114001491113010200003010091114001091111110100021110094904001494901110100081110094904000894901090100001090092904001c92901090100071090092904000092901050100011050091904001491901050100061050091904000491904000d00033121100054000c5040 (by decide +kernel)

def state215_12 : List Sig := [0xffffffffffffffff0000000000000000ffff0000ffff0000,input 6,input 4,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_12 : Impossible true (goalAt 215) 6 state215_12.toFinset :=
  node_ok cuts215 [] 0x444025240949011100948425240949011100949011100444025240929025240868424a40424024a40929010900868424a40929021a10929010900424024a40919025240858424640919024a40121124640414024640919010500858424640919021610919010500414024640504025210948414100948414100504025210c04024444c04024444949011100949011100929010900929010900919010500919010500911130100911130100948414100948414100d090 (by decide +kernel)

def state215_13 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_13 : Impossible true (goalAt 215) 6 state215_13.toFinset :=
  node_ok cuts215 [] 0x25210949025240444011100949025240444025240d09030210949005444949025240149024a40949021a10929021a10929024a40868410900929024a40424024a40d09010900929004c44929024a40129024640949021610919024640929004844919021610919024640858410500919024640414024640d09010500919024444919024641000a14100d09031210c09030240911125210948405210911130100c0404000cc04034240d090112105111 (by decide +kernel)

def state215_14 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_14 : Impossible true (goalAt 215) 7 state215_14.toFinset :=
  node_ok cuts215 [⟨state215_6,exclude215_6⟩,⟨state215_4,exclude215_4⟩,⟨state215_12,exclude215_12⟩,⟨state215_13,exclude215_13⟩] 0x1000414444511124444d09034242000334240d09024444511114242000211c1c470740014d09034242000134240d09040014470711c1cc48425240949034240444034240c48411100c0843424094902524100041110044402444494902524100082524094902444444401110094841110094844002094902524094842524094904000c444011101000811100444040008949025241000825240949040008444011100470724a40929034240424034240470710900424034240929024a41000724a40929025240868425241000721a10868425240929024a41000410900424024444929024a41000724a40929024444424010901000321a10868425210929024a41000724a40929025210868421a11000710900424040000929024a41000724a40929040000424010900511124640919034240414034240511110500414034240919024640151124640919025240858425240151121610858425240919024640131124640919024a41000724a4013114001c121124a40919024640911110500414040028919024640911124640919040010414010501000321610858425210919024641000a24640919025210858421611000a10500414040004919024641000a2464091904000441401050100044000cc04034240948434240c4844000cc48434242000030240c48425210c090244450004244450003252109484400110004052110004400105040 (by decide +kernel)

def state215_15 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,input 6,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_15 : Impossible true (goalAt 215) 6 state215_15.toFinset :=
  node_ok cuts215 [] 0x24444504014100c04025210948424444948425210c04014100504034240948434240c48414100c48434240504030240c48425210c09025210444025210504025240949025210949025240504011100444021c1c444011100c04025240949021c1c949025240c04011100444031210949025240d09011100d09031210444030210d0902524094900581c868421a10948424a4092900581c929024a40948421a10868440034929024a40949021a10949040034868421a10949024a40929021c1c424010900c04024a40929021c1c929024a40c04010900424011c1c929024a40d09010900d09011c1c424010900d09024a40929030100511130100911134240d09030100d09034240911114444509025210858421610160724640919025210919024640160721610858425240919024640141121610858425240858425240141124640919024a40919024640121140034121124a41000d24a401211246409190301004140105009111246409190301009190246409111105004140342409190246405111105004140342404140342405111246409190 (by decide +kernel)

def state215_16 : List Sig := [0x5555555555555555555555555555555555555555555555550000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_16 : Impossible true (goalAt 215) 6 state215_16.toFinset :=
  node_ok cuts215 [] 0x14100948425210504034240c48430240c0900581c948425210160725210949025240444011100949025240444025240d09030210949005044949025240141121a10929024a40868424a40949021a10929010900929024a40424024a40d09010900929004844929024a40121124444c04034240509014444858424640919021610919021610949024640919004844929024640414024640919010500919010500d090246410001 (by decide +kernel)

def state215_17 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_17 : Impossible true (goalAt 215) 6 state215_17.toFinset :=
  node_ok cuts215 [] 0x444025240949011100949034240c08425240444025240949011100929025240868424a40424024a40929010900929034240424024a40868424a40929021a10919025240858424640919024a40121124640414024640919010500919034240414024640858424640919021610c04034240d09014240911130100911130100d09031210d09031210444025240444025240868424a40868424a40858424640858424640c04024444c04024444c48434240c484342409484 (by decide +kernel)

def state215_18 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_18 : Impossible true (goalAt 215) 7 state215_18.toFinset :=
  node_ok cuts215 [⟨state215_4,exclude215_4⟩,⟨state215_13,exclude215_13⟩,⟨state215_15,exclude215_15⟩,⟨state215_16,exclude215_16⟩,⟨state215_17,exclude215_17⟩] 0x1000414100504030100948425212000125210948430100504014100d09025210d09031210504031210d09014100c09031210948430242000405c1c17074000c94842521200002521094844000c170705c1c948411100948414100949025240948425240949014100444011101000411100444030100949025241000c25240949030100444011100c48425240949034240444034240c48411100c08434240949025241000c05444151140008949025241000c25240949040008151105444170721a10868425210929024a40170724a40929025210868421a11000b24a40929025240868425241000b21a10868425240929024a41000410900424030100929024a41000b24a40929030100424010901000b24a40929034240424034241000b10900424034240929024a41000b04c44131140000929024a41000b24a40929040000131104c44170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024640131124640919024a41000a24a4013114002c121124a40919024641000410500414030100919024641000a24640919030100414010501000a24640919034240414034241000a10500414034240919024641000a8000e000240004919024641000a24640919040005000a40005000440014911130101000430101000534240d090400110004142410004400105111 (by decide +kernel)

def state215_19 : List Sig := [0xf0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000,input 4,input 6,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_19 : Impossible true (goalAt 215) 5 state215_19.toFinset :=
  node_ok cuts215 [] 0x10900929024a40424024a40d09010900929021a10929024a40868424640929004844919010500919024640414024640d09010500919021610919024640858414444d09034240509014100948425210504034240c08434240948424a40868424a40949024640858424640949011100949025240444025240c084342409490111009490252409484 (by decide +kernel)

def state215_20 : List Sig := [0xffff0000ffff0000ffff0000ffff0000ffffffffffffffffffff0000ffff0000,input 4,input 6,input 7,input 0,input 1,input 2]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_20 : Impossible true (goalAt 215) 6 state215_20.toFinset :=
  node_ok cuts215 [⟨state215_19,exclude215_19⟩] 0x444025240949011100949034240c08425240444025240949011102000025240949040008929025240868424a40424024a40929010900929034240424024a40868424a40929021a10868424a40929021a10919025240858424640919024a40121124640414024640919010500919034240414024640858424640919021610858424640919021610511134240d09014240504034100911114100d09031210d09031210948424444870730100c04034240c48434240c484 (by decide +kernel)

def state215_21 : List Sig := [0xffffffffffffffff0000000000000000,input 6,input 7,input 0,input 1,input 2,input 4]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_21 : Impossible true (goalAt 215) 7 state215_21.toFinset :=
  node_ok cuts215 [⟨state215_20,exclude215_20⟩] 0x911114100504021c1c948425210911125210948421c1c504014100d09025210d09031210504031210d09014100c09031210948430240948411100948414100949025240948425240949014100444011100870711100444024444949025240870725240949024444444011100c48425240949034240444034240c48411100c08434240949025240170721a10868425210929024a40170724a40929025210868421a11000b24a40929025240868425241000b21a10868425240929024a40870710900424024444929024a40870724a40929024444424010901000524a40929034240424034241000b10900424034240929024a40170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024640131124640919024a41000a24a4013114002c121124a40919024640911110500414021818919024640911124640919021818414010501000524640919034240414034241000a10500414034240919024641000440010d11140014d0903424091114001091111410100031410094844001494841410200001410094844000c948411101000211100949040014949011101000c11100949040008949010901000010900929040014929010901000b10900929040000929010501000110500919040014919010501000a105009190400049190400150004301010004400105111 (by decide +kernel)

def state215_22 : List Sig := roots 215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude215_22 : Impossible true (goalAt 215) 8 state215_22.toFinset :=
  node_ok cuts215 [⟨state215_8,exclude215_8⟩,⟨state215_11,exclude215_11⟩,⟨state215_14,exclude215_14⟩,⟨state215_18,exclude215_18⟩,⟨state215_21,exclude215_21⟩] 0x40010c04014444c04080010911134240d0908000cc04034240d0904001091111444450904001091111410050404000cc04025210948480008911125210948440010c04014100504080004d09025210d0904000cc48414100c48480000d09014100c0904000cc48425210c09040008870711100444040008c04025240949040008870725240949040008c04011100444040008c48425240949040008d09011100d09040008c48411100c08440008d09025240949040008948411100948440008504025240949040008948425240949040008504011100444040000870710900424040000c04024a40929040000870724a40929040000c04010900424040000470724a40929040000d09010900d09040000470710900424040000d09024a40929040000170721a10868440000948424a40929040000170724a40929040000948421a10868440001000024a40929040000949021a10949040001000021a10868440000949024a40929040004911110500414040004c04024640919040004911124640919040004c04010500414040004511124640919040004d09010500d09040004511110500414040004d090246409190400041707216108584400049484246409190400041707246409190400049484216108584400041511246409190400049490216109490400041511216108584400049490246409190400001311246409190400009290400009290400001311400001211400009290246409190 (by decide +kernel)

theorem lower215 : Claim 215 9 :=
  fromSearch 66630 (by decide +kernel) exclude215_22

theorem lower231 : Claim 231 7 :=
  fromLift 7 1 1365 lower230 (by decide +kernel)

theorem lower119 : Claim 119 7 :=
  fromLift 7 1 66629 lower118 (by decide +kernel)

def rule247_0 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower245 none (by decide +kernel)

def rule247_1 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 none (by decide +kernel)

def rule247_2 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower246 none (by decide +kernel)

def rule247_3 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 none (by decide +kernel)

def rule247_4 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower215 none (by decide +kernel)

def rule247_5 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower231 none (by decide +kernel)

def rule247_6 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower119 none (by decide +kernel)

def rule247_7 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower199 none (by decide +kernel)

def rule247_8 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower167 none (by decide +kernel)

def rule247_9 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower118 none (by decide +kernel)

def rule247_10 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower117 none (by decide +kernel)

def rule247_11 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower227 none (by decide +kernel)

def rule247_12 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower215 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_13 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_14 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower246 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_15 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower230 none (by decide +kernel)

def rule247_16 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower245 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_17 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower116 none (by decide +kernel)

def rule247_18 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower114 none (by decide +kernel)

def rule247_19 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower86 none (by decide +kernel)

def rule247_20 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower166 none (by decide +kernel)

def rule247_21 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower229 none (by decide +kernel)

def rule247_22 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower225 none (by decide +kernel)

def rule247_23 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower85 none (by decide +kernel)

def rule247_24 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower165 none (by decide +kernel)

def rule247_25 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower243 (some (1,input 4,input 7)) (by decide +kernel)

def rule247_26 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower115 none (by decide +kernel)

def rule247_27 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower83 none (by decide +kernel)

def rule247_28 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower163 none (by decide +kernel)

def rule247_29 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower87 none (by decide +kernel)

def rule247_30 : {c : Cut // CutGood (goalAt 247) c} :=
  ruleFor 247 lower183 (some (3,input 4,input 7)) (by decide +kernel)

def cuts247 : Cuts (goalAt 247) := [rule247_0,rule247_1,rule247_2,rule247_3,rule247_4,rule247_5,rule247_6,rule247_7,rule247_8,rule247_9,rule247_10,rule247_11,rule247_12,rule247_13,rule247_14,rule247_15,rule247_16,rule247_17,rule247_18,rule247_19,rule247_20,rule247_21,rule247_22,rule247_23,rule247_24,rule247_25,rule247_26,rule247_27,rule247_28,rule247_29,rule247_30]

def state247_0 : List Sig := [0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_0 : Impossible true (goalAt 247) 9 state247_0.toFinset :=
  node_ok cuts247 [] 0x40018e0601c0c0e06040018a02034240d09040018e06034240d09040018a0201c0c0a0604002070302c240b09040020d09040020d09040020703040020503040020d0902c240b09040018e0600c444e06040018c0402c240b09040018e0602c240b09040018c0400c444c0604002cc4842524094904002cd09019180d0904002cc48419180c0844002cd0902524094904002ca4842524094904002cb09019180b0904002ca48419180a0844002cb09025240949040018870719180646040018e06025240949040018870725240949040018e06019180646040014170719180646040014706025240949040014170725240949040014706019180646040019000619180646040019000125240949040019000b25240949040019000119180646040020470724a40929040020d09018980d09040020470718980626040020d09024a4092904001c270724a4092904001cb09018980b0904001c27071898062604001cb09024a4092904002d000b24a4092904002c949021a1094904002d000a21a1086844002c949024a40929040018870718980626040018e06024a40929040018870724a40929040018e06018980626040014170721a10868440014706024a40929040014170724a40929040014706021a10868440019000621a10868440019000024a40929040019000a24a40929040019000021a10868440020511124640919040020d09018580d09040020511118580616040020d09024640919040024311124640919040024b09018580b09040024311118580616040024b0902464091904002c15112464091904002c94902161094904002c15112161085844002c949024640919040024131124640919040024929040024929040024131140028121140024929024640919040018870718580616040018e06024640919040018870724640919040018e06018580616040014170721610858440014706024640919040014170724640919040014706021610858440019000621610858440019000224640919040019000924640919040019000221610858440014d09005c1cd09040014c4841c180c48440014d0901c180d09040014c48405c1cc48440014b09014100b09040014a4841c180a48440014b0901c180b09040014a48414100a4844001900061c180706040018e06040018e06040019000540018a03040018d0904000cd09040018c48440018c48440018d09040020d09040018c4844000cc48440018b09040010b09040018a48440018a48440018b0904001cb09040018a48440010a48440019000640018b030400190006400149484 (by decide +kernel)

def state247_1 : List Sig := [0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_1 : Impossible true (goalAt 247) 9 state247_1.toFinset :=
  node_ok cuts247 [] 0x40019000d1c0c0703040020b03034240d09040035000d34240d09040018b0301c0c0509040035000d11c1c470740021000334240d09040035000d34240d09040021000311c1c47074002070302c240b0904001cd09040034d09040034703040034503040020d0902c240b09040018b0300c444b0304001c91112c240b09040074b0302c240b0904001891110c444311140031000c09c1c27074001d00042c240b09040031000c2c240b0904001d000409c1c270740020c4842524094904002cd09019180d09040070c48419180c0844002cd0902524094904001ca4842524094904002cb09019180b0904006ca48419180a0844002cb0902524094904001900191918064604002cb03025240949040069001925240949040018b0301918064604001494841918094844002d001a2524094904002c948425240949040015001a1918064604006500191918064604002d00012524094904006500192524094904002d000119180646040020470724a40929040028d09018980d09040060470718980626040020d09024a4092904001c270724a40929040028b09018980b0904005c27071898062604001cb09024a4092904002d001024a40929040028949021a10949040059001021a1086844002c949024a40929040019001018980626040028b03024a40929040029001024a40929040018b03018980626040015001021a10868440028948424a40929040055001024a40929040014948421a10868440041001018980626040029000024a40929040041001024a40929040029000018980626040020511124640919040024d09018580d09040050511118580616040020d0902464091904001c311124640919040024b09018580b0904004c311118580616040024b0902464091904002c15112464091904002494902161094904004815112161085844002c949024640919040028131124640919040024929040040929040044131140040121140024929024640919040018911118580616040024b03024640919040024911124640919040018b03018580616040015000e2161085844002494842464091904003d000e24640919040014948421610858440039000e18580616040025000224640919040039000e24640919040025000218580616040015000540014e06040020d09025210d09040014c48440034c48440020d09040034c09040014c48425210c0904001cb09025210b09040014a48440030a4844001cb09040030a09040014a48425210a09040018b03040018b03040015000525210948440019000540018a030400190006400187060 (by decide +kernel)

def state247_2 : List Sig := [0xffff0000ffff0000ffff0000ffff0000,input 4,input 7,input 0,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_2 : Impossible true (goalAt 247) 9 state247_2.toFinset :=
  node_ok cuts247 [] 0x40018e0601c0c0e06040020a02034240d09040020e06034240d09040018a0201c0c0a0604002070302c240b09040020d09040020d09040020703040020503040020d0902c240b09040018e0600c444e0604001cc0402c240b0904001ce0602c240b09040018c0400c444c0604002cc4842524094904002cd09019180d0904002cc48419180c0844002cd0902524094904002ca4842524094904002cb09019180b0904002ca48419180a0844002cb0902524094904001887071918064604002ce0602524094904002c870725240949040018e06019180646040014948419180948440015000b25240949040014948425240949040015000519180646040020470724a40929040020d09018980d09040020470718980626040020d09024a4092904001c270724a4092904001cb09018980b0904001c27071898062604001cb09024a4092904002d000b24a4092904002c949021a1094904002d001521a1086844002c949024a40929040018870718980626040028e06024a40929040028870724a40929040018e06018980626040015000521a10868440014948424a40929040015001524a40929040014948421a10868440020511124640919040020d09018580d09040020511118580616040020d0902464091904001c311124640919040024b09018580b0904001c311118580616040024b0902464091904002c15112464091904002c94902161094904002c15112161085844002c94902464091904002813112464091904002492904003c92904003c131140054121140024929024640919040018870718580616040024e06024640919040024870724640919040018e06018580616040015000521610858440014948424640919040015000f24640919040014948421610858440014d09025210d09040014c48440014c48440014d09040020c09040014c48425210c09040014b09025210b09040014a48440014a48440014b0904001ca09040014a48425210a09040019000540018f06040015000525210948440018e06040018e0604001470304000c703040014d09040014d09040014703040020703040014d0904000cd09040014311140010311140014b09040014b0904001431114001c311140014b09040010b0904001434304000434304001494904001494904001434304002c34304001494904000494904001432304000032304001492904001492904001432304005432304001492904000092904001431304000831304001491904001491904001431304003c313040014919040008919040015000540040b030400190006400187060 (by decide +kernel)

def state247_3 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_3 : Impossible true (goalAt 247) 6 state247_3.toFinset :=
  node_ok cuts247 [] 0x5c1c868421a10948424a40929005c1c929024a40948421a1086844006c929024a40949021a1094904005c868421a10949024a40929009c1c929024a40b09018980b09009c1c626018980b09024a40929020c1c32300c8c0503024a40929020c1c929024a4050300c8c0323004c4491902464092904005c929004c45001704844929024640919005c1c858421610948424640919005c1c91902464094842161085840544491902464094902161094900544485842161094902464091900c444919024640b09018580b0900c444616018580b0902464091902444431300c4c050302464091902444491902464050300c4c031302c24094842c240a0841c180a0842c24070602c240a084252109484140c01707140c08307252109484140c0948425210830705c1c148025210646025210706025240949025210949025240706019180646028210949025240b09019180b09028210646028210b09025240949020c1c34300d0c0503025240949020c1c94902524050300d0c03430140c03111140c091112c240b090140c0b0902c24091110c4442480 (by decide +kernel)

def state247_4 : List Sig := [0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000,input 6,0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 0,input 1]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_4 : Impossible true (goalAt 247) 7 state247_4.toFinset :=
  node_ok cuts247 [⟨state247_3,exclude247_3⟩] 0x83071898062602c0c0929024a40830724a4092902c0c0626018980170721a10868425210929024a40170724a40929025210868421a11001b24a40929025240868425241001721a10868425240929024a41001c24a409290140c06260189810017189806260140c0929024a40270724a4092902c24062602c24027071898062602c240929024a40131124640919024a41001724a4013114005c121124a4091902464091111858061602c0c091902464091112464091902c0c0616018580170721610858425210919024640170724640919025210858421610151124640919025240858425240151121610858425240919024641001c246409190140c06160185810013185806160140c091902464031112464091902c24061602c24031111858061602c240919024640b0301c180706020c1c948425210b03025210948420c1c70601c18050302521094844007070601c18050301c180706040070948425210b09025210b09028210706028210b0901c180b0902821094842521083071918064602c0c094902524083072524094902c0c064601918094841918094841c18094902524094842524094901c180646019181001c252409490140c0646019181001b191806460140c0949025240a0842524094902c24064602c240a08419180a0842c240949025241001d140c050302c0c1001d2c0c1001c4007600002c0c05030140c1001d40074d0902c0c031112c0c091112c240b0902c0c0b0902c24091110c4442480 (by decide +kernel)

def state247_5 : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,input 6,0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 0,input 1,input 5]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_5 : Impossible true (goalAt 247) 7 state247_5.toFinset :=
  node_ok cuts247 [⟨state247_3,exclude247_3⟩] 0x1001d2c240b09034241001d34241001d40072000034240b0902c240b0300c444b03024444b0902c240b0302c240b09024444311109200270724a4092902c24062602c24027071898062602c240929024a40170721a10868425210929024a40170724a40929025210868421a11000a24a40929025240868425241000a21a10868425240929024a41000a24a40929034240626034241000a18980626034240929024a4083070c8c032302c0c0929024a40830724a4092902c0c032300c8c031112464091902c24061602c24031111858061602c240919024640131124640919024a41000924a40131140028121124a4091902464017072161085842521091902464017072464091902521085842161015112464091902524085842524015112161085842524091902464100092464091903424061603424100091858061603424091902464091110c4c031302c0c091902464091112464091902c0c031300c4c0b09025210b09028210706028210b0901c180b09028210948425210d09025210d09030210706030210d0901c180d09030210948425210b03005c1cb03020c1c948425210b03025210948420c1c170705200a0842524094902c24064602c240a08419180a0842c24094902524094841918094841c18094902524094842524094901c180646019180c08425240949034240646034240c08419180c0843424094902524083070d0c034302c0c094902524083072524094902c0c034300d0c10006400187030 (by decide +kernel)

def state247_6 : List Sig := [0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,input 4,input 7,input 0,input 1,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_6 : Impossible true (goalAt 247) 8 state247_6.toFinset :=
  node_ok cuts247 [⟨state247_4,exclude247_4⟩,⟨state247_5,exclude247_5⟩] 0x4001900061c0c0703040018b03034240d0904001a000134240d09040018b0301c0c050904007470302c240b09040074d09040074d09040074703080000503040074d0902c240b09040018b0300c444b0304001891112c240b09040018b0302c240b0904001891110c444248040028470724a40929040028d09018980d09040028470718980626040028d09024a40929040028270724a40929040028b09018980b09040028270718980626040028b09024a40929040018830718980626040018b03024a40929040018830724a40929040018b0301898062604002c170721a10868440028948424a40929040028170724a4092904002c948421a10868440029000a24a40929040028949021a10949040029000a21a10868440028949024a40929040024511124640919040024d09018580d09040024511118580616040024d09024640919040024311124640919040024b09018580b09040024311118580616040024b09024640919040024131124640919040024929040024929040024131140028121140024929024640919040018911118580616040018b03024640919040018911124640919040018b0301858061604002c17072161085844002494842464091904002417072464091904002c948421610858440024151124640919040024949021610949040024151121610858440024949024640919040070d09025210d0904002cc0841c180c08440070d0901c180d0904002cc08425210948440074b09025210b0904002ca0841c180a08440074b0901c180b0904002ca08425210948440018b0301c180706040018830725210948440018b0302521094844001883071c180706040068c08425240949040068d09019180d09040068c08419180c08440068d09025240949040068a08425240949040068b09019180b09040068a08419180a08440068b09025240949040018830719180646040018b03025240949040018830725240949040018b0301918064604002c94841918094844006870602524094904006894842524094904002c7060191806460 (by decide +kernel)

def state247_7 : List Sig := [0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000,input 4,input 7,input 0,input 1,input 2,input 5,input 6]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_7 : Impossible true (goalAt 247) 9 state247_7.toFinset :=
  node_ok cuts247 [⟨state247_6,exclude247_6⟩] 0x4001900061c0c0703040018b03034240d09040019001e34240d09040018b0301c0c050904002070302c240b0904001cd09040074d09040074703040078503040020d0902c240b09040018b0300c444b0304001891112c240b09040018b0302c240b0904001891110c444311140020c4842524094904002cd09019180d09040068c48419180c0844002cd0902524094904001ca4842524094904002cb09019180b09040068a48419180a0844002cb09025240949040019000619180646040018b03025240949040019001a25240949040018b0301918064604001417071918064604002c70602524094904002c170725240949040014706019180646040020470724a40929040028d09018980d09040028470718980626040020d09024a4092904001c270724a40929040028b09018980b0904002827071898062604001cb09024a4092904002d000a24a40929040028949021a10949040029000a21a1086844002c949024a40929040019000618980626040018b03024a40929040019000a24a40929040018b03018980626040014170721a10868440028706024a40929040028170724a40929040014706021a10868440020511124640919040024d09018580d09040024511118580616040020d09024640919040024311124640919040024b09018580b09040024311118580616040024b0902464091904002c15112464091904002494902161094904002415112161085844002c949024640919040024131124640919040024929040024929040024131140028121140024929024640919040018911118580616040018b03024640919040018911124640919040018b03018580616040014170721610858440024706024640919040024170724640919040014706021610858440020d09005c1cd09040014c4841c180c48440020d0901c180d09040014c48405c1cc4844001cb09014100b09040014a4841c180a4844001cb0901c180b09040014a48414100a48440019000540018f06040018b03040018b0304001900061c180706040018c4844000cc48440018d09040018d09040018c48440078c48440018d0904000cd09040018a48440010a48440018b09040018b09040018a48440074a48440018b09040010b0904001900064000500014001894904001894904001900064006a000040018949040004949040018868440000868440018929040018929040018868440028868440018929040000929040018858440008858440018919040018919040018858440024858440018919040008919040019000640018e060400190006400409484 (by decide +kernel)

def state247_8 : List Sig := roots 247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exclude247_8 : Impossible true (goalAt 247) 10 state247_8.toFinset :=
  node_ok cuts247 [⟨state247_0,exclude247_0⟩,⟨state247_1,exclude247_1⟩,⟨state247_2,exclude247_2⟩,⟨state247_7,exclude247_7⟩] 0x4000ce0601c0c0e0604000cb03034240d0904000ce06034240d0904000cb0301c0c0a06040010e0600c444e06040010c0402c240b09040010e0602c240b09040010c0400c444c0604000c70302c240b0904000cd0904000cd0904000c70304000c50304000cd0902c240b0908000cb0301c180706080008e06025210948480004b03025210948480000e0601c18070604000cd09025210d0904000cc4841c180c4844000cd0901c180c0904000cc48425210c09040010b09025210b09040010a4841c180a48440010b0901c180a09040010a48425210a09040004870719180646040004e06025240949040004870725240949040004e06019180646040004c48425240949040004d09019180d09040004c48419180c08440004d09025240949040004a48425240949040004b09019180b09040004a48419180a08440004b09025240949040004948419180948440004706025240949040004948425240949040004706019180646040000870718980626040000e06024a40929040000870724a40929040000e06018980626040000470724a40929040000d09018980d09040000470718980626040000d09024a40929040000270724a40929040000b09018980b09040000270718980626040000b09024a40929040000170721a10868440000948424a40929040000170724a40929040000948421a10868440001000024a40929040000949021a10949040001000021a10868440000949024a40929040008911118580616040008e06024640919040008911124640919040008e0601858061604000c51112464091904000cd09018580d0904000c51111858061604000cd09024640919040008311124640919040008b09018580b09040008311118580616040008b090246409190400081707216108584400089484246409190400081707246409190400089484216108584400041511246409190400049490216109490400041511216108584400049490246409190400001311246409190400009290400009290400001311400001211400009290246409190 (by decide +kernel)

theorem lower247 : Claim 247 11 :=
  fromSearch 66629 (by decide +kernel) exclude247_8


open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 255
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [13, 7]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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


def lowRow (i : Fin 8) : Row := Fin.ofNat 256 (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 256 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
  (ruleFor 255 lower247 none (by decide +kernel)).property 11 eightInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_31357_aux

open PEqualNP.Outside.L_meta_31357_aux in
theorem PEqualNP.Outside.L_meta_31357 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true))  := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct
